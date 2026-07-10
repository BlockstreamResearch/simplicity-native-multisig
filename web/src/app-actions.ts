import { assetLabel, emptyScan, utxoKey } from "./app-helpers";
import type { AppActionContext } from "./app-action-context";
import type { BusyAction } from "./app-model";
import {
  applyLoadedDescriptor,
  clearProposalState,
  clearVoteState,
  run,
  showToast,
} from "./app-action-tools";
import { satsAmountError } from "./lib/sats";
import {
  createMultisigDescriptor,
  createProposedSpend,
  createSignedVote,
  decodeVoteTransaction,
  decodeVoteTransactionAuto,
  deriveParticipantKey,
  inspectMultisigDescriptor,
} from "./lib/contracts";
import { demoMnemonics } from "./lib/demo";
import { requestFaucetFunds } from "./lib/faucet";
import { claimParticipant } from "./lib/lwk/participants";
import {
  publishParticipantAnnouncement,
  publishVote,
} from "./lib/lwk/publishing";
import {
  discoverParticipantAnnouncements,
  scanSession,
  scanVoteFromDecoded,
} from "./lib/lwk/scan";
import { finalizeAndBroadcastSpend } from "./lib/lwk/spend";
import { esploraTxHex } from "./lib/lwk/network";
import { FaucetAsset, FaucetTarget, ScanTransaction, ScanVote } from "./types";

export function createAppActions(ctx: AppActionContext) {
  const {
    activeMultisigDescriptor,
    announcementMnemonic,
    announcementStake,
    announcementStakeValid,
    changeOutputs,
    claimed,
    claimMnemonic,
    currentMultisigAddress,
    descriptorText,
    executorFeeRate,
    executorFundingEnabled,
    executorFundingMnemonic,
    feeAmount,
    info,
    manualVoteTx,
    outputs,
    participantKeys,
    proposal,
    proposalAmountErrors,
    proposalAmountsValid,
    scan,
    selectedUtxos,
    session,
    threshold,
    underfundedAssets,
    vote,
    voteStake,
    voteStakeValid,
    votesForFinalization,
    setActiveTab,
    setAnnouncementMnemonic,
    setAnnouncementScan,
    setBusyAction,
    setClaimed,
    setClaimMnemonic,
    setDescriptorText,
    setFaucetBusy,
    setFaucetResult,
    setFinalSpend,
    setMultisigDescriptor,
    setParticipantKeys,
    setProposal,
    setScan,
    setSelectedInputs,
    setSession,
    setThreshold,
    setVote,
  } = ctx;

  async function withBusyAction<T>(action: BusyAction, work: () => Promise<T>): Promise<T> {
    setBusyAction(action);
    try {
      return await work();
    } finally {
      setBusyAction(undefined);
    }
  }

  async function fillDemo() {
    await run(ctx, "Deriving demo participants", async () => {
      const keys = await Promise.all(
        demoMnemonics.map((mnemonic, index) => deriveParticipantKey(mnemonic, index)),
      );
      setParticipantKeys(keys.map((key) => key.xOnlyPublicKey));
      setClaimMnemonic(demoMnemonics[0]);
      setAnnouncementMnemonic(demoMnemonics[0]);
    });
  }

  async function createDescriptor() {
    const next = await run(ctx, "Creating multisig descriptor", () =>
      createMultisigDescriptor(threshold, participantKeys),
    );
    if (next) {
      applyLoadedDescriptor(ctx, next);
      setDescriptorText(JSON.stringify(next, null, 2));
      setActiveTab("create");
    }
  }

  async function loadDescriptor() {
    const nextDescriptor = await run(ctx, "Inspecting descriptor", () =>
      inspectMultisigDescriptor(descriptorText),
    );
    if (nextDescriptor) {
      applyLoadedDescriptor(ctx, nextDescriptor);
      await refreshAnnouncements(nextDescriptor);
    }
  }

  async function refreshAnnouncements(descriptor = activeMultisigDescriptor): Promise<boolean> {
    if (!descriptor || !info) return false;
    setAnnouncementScan((current) => ({
      ...current,
      status: "scanning",
      message: "Scanning descriptor announcements",
    }));

    const next = await run(ctx, "Scanning descriptor announcements", () =>
      discoverParticipantAnnouncements(descriptor, info),
    );
    if (!next) {
      setAnnouncementScan((current) => ({
        ...current,
        status: "error",
        message: "Announcement scan failed",
      }));
      return false;
    }

    setAnnouncementScan(next.scan);
    if (next.session) {
      setSession(next.session);
      setMultisigDescriptor(descriptor);
      setThreshold(next.session.threshold);
      setParticipantKeys(
        next.session.participants.map((participant) => participant.xOnlyPublicKey),
      );
      setScan(emptyScan);
      clearProposalState(ctx);
    }
    return true;
  }

  async function rescan(): Promise<boolean> {
    if (!info) return false;
    if (!session) {
      return refreshAnnouncements();
    }

    setScan((current) => ({
      ...current,
      status: "scanning",
      message: "Scanning Liquid testnet",
    }));
    const next = await run(ctx, "Scanning Liquid testnet", () =>
      scanSession(session, info, claimed, scan.votes),
    );
    if (next) {
      setScan(next);
      setSelectedInputs(new Set(next.utxos.slice(0, 1).map(utxoKey)));
      return true;
    }

    setScan((current) => ({
      ...current,
      status: "error",
      message: "Scan failed",
    }));
    return false;
  }

  async function claim() {
    if (!session) return;
    const next = await run(ctx, "Verifying participant", () => claimParticipant(session, claimMnemonic));
    if (next) {
      setClaimed(next);
    }
  }

  async function buildProposal() {
    if (!session || !info) return;
    const next = await run(ctx, "Building proposal", () => {
      if (!proposalAmountsValid) {
        throw new Error(proposalAmountErrors[0]);
      }
      if (underfundedAssets.length > 0) {
        throw new Error(`Selected inputs do not cover ${underfundedAssets.join(", ")}`);
      }

      return createProposedSpend(session, selectedUtxos, [
        ...outputs,
        ...changeOutputs,
        {
          id: "fee",
          kind: "fee",
          address: "",
          asset: info.policyAsset,
          value: feeAmount,
        },
      ]);
    });
    if (next) {
      setProposal(next);
      clearVoteState(ctx);
    }
  }

  async function signVote() {
    if (!session || !proposal) return;
    const mnemonic = claimed?.mnemonic ?? claimMnemonic;
    await withBusyAction("create-vote", async () => {
      const next = await run(ctx, "Signing vote", () =>
        createSignedVote(
          session,
          proposal.psetBase64,
          proposal.inputUtxos,
          proposal.totalProposedOutputs,
          mnemonic,
        ),
      );
      if (next) {
        setVote(next);
      }
    });
  }

  async function broadcastVote() {
    if (!info || !session || !claimed || !proposal || !vote) return;
    if (!voteStakeValid) {
      showToast(ctx, "error", "Publishing vote", satsAmountError("Vote amount"));
      return;
    }
    await withBusyAction("publish-vote", async () => {
      const published = await run(ctx, "Publishing vote", () =>
        publishVote(info, claimed, proposal, vote, voteStake),
      );
      if (published) {
        const decoded = await decodeVoteTransactionAuto(session, published.txHex);
        await navigator.clipboard.writeText(published.txid).catch(() => undefined);
        await rescan();
        mergeDiscoveredVote(scanVoteFromDecoded(decoded, published.txid, published.explorerUrl));
        showToast(ctx, "success", "Vote published", published.txid);
      }
    });
  }

  async function fundFromFaucet(target: FaucetTarget, asset: FaucetAsset) {
    if (!info) return;

    const address = target === "multisig" ? currentMultisigAddress : claimed?.fundingAddress;
    if (!address) return;

    const busyKey = `${target}:${asset}`;
    setFaucetBusy(busyKey);
    try {
      const next = await run(ctx, `Requesting ${assetLabel(asset)} faucet funds`, () =>
        requestFaucetFunds(info, target, address, asset),
      );
      if (next) {
        setFaucetResult(next);
      }
    } finally {
      setFaucetBusy(undefined);
    }
  }

  async function publishAnnouncement() {
    if (!info || !activeMultisigDescriptor || !announcementMnemonic.trim()) return;
    if (!announcementStakeValid) {
      showToast(ctx, "error", "Publishing participant announcement", satsAmountError("Dust amount"));
      return;
    }
    await withBusyAction("publish-announcement", async () => {
      const next = await run(ctx, "Publishing participant announcement", () =>
        publishParticipantAnnouncement(
          info,
          activeMultisigDescriptor,
          announcementMnemonic,
          announcementStake,
        ),
      );
      if (next) {
        await navigator.clipboard.writeText(next.txid).catch(() => undefined);
        if (await refreshAnnouncements(activeMultisigDescriptor)) {
          showToast(ctx, "success", `Participant ${next.participantIndex + 1} announced`, next.txid);
        }
      }
    });
  }

  async function decodeManualVote() {
    if (!session || !manualVoteTx.trim()) return;
    const result = await run(ctx, "Decoding vote transaction", async () => {
      const trimmed = manualVoteTx.trim();
      let tx = { hex: trimmed, txid: "manual", explorerUrl: "" };
      if (/^[0-9a-fA-F]{64}$/.test(trimmed)) {
        if (!info) {
          throw new Error("Load Liquid testnet info before decoding a vote txid.");
        }
        const txid = trimmed.toLowerCase();
        tx = {
          hex: await esploraTxHex(info, txid),
          txid,
          explorerUrl: `${info.explorerTxUrlPrefix}${txid}`,
        };
      }
      const decoded = proposal
        ? await decodeVoteTransaction(session, tx.hex, proposal.totalProposedOutputs)
        : await decodeVoteTransactionAuto(session, tx.hex);

      return { decoded, txid: tx.txid, explorerUrl: tx.explorerUrl };
    });
    if (result) {
      mergeDiscoveredVote(scanVoteFromDecoded(result.decoded, result.txid, result.explorerUrl));
    }
  }

  function mergeDiscoveredVote(vote: ScanVote) {
    setScan((current) => {
      const transaction: ScanTransaction = {
        txid: vote.txid,
        type: "vote",
        sources: [`Participant ${vote.participantIndex + 1}`],
        explorerUrl: vote.explorerUrl,
      };
      const existingTransaction = current.transactions.find(
        (item) => item.txid === transaction.txid,
      );
      const transactions = existingTransaction
        ? current.transactions.map((item) =>
            item.txid === transaction.txid
              ? {
                  ...item,
                  type: item.type === "vote" ? item.type : transaction.type,
                  sources: [...new Set([...item.sources, ...transaction.sources])],
                  explorerUrl: item.explorerUrl || transaction.explorerUrl,
                }
              : item,
          )
        : [transaction, ...current.transactions];

      return {
        ...current,
        votes: [...current.votes.filter((item) => item.txid !== vote.txid), vote],
        transactions,
      };
    });
  }

  async function loadProposalFromVote(vote: ScanVote) {
    const next = await run(ctx, "Loading proposal from vote", async () => {
      const inputUtxos = vote.proposalInputOutpoints.map((outpoint) => {
        const utxo = scan.utxos.find(
          (candidate) => candidate.txid === outpoint.txid && candidate.vout === outpoint.vout,
        );
        if (!utxo) {
          throw new Error(`Missing multisig UTXO ${outpoint.txid}:${outpoint.vout}`);
        }
        return utxo;
      });

      return {
        psetBase64: vote.proposedPsetBase64,
        txHex: vote.proposedTxHex,
        totalProposedOutputs: vote.totalProposedOutputs,
        messageHash: vote.messageHash,
        inputUtxos,
      };
    });

    if (next) {
      setProposal(next);
      clearVoteState(ctx);
      setSelectedInputs(new Set(next.inputUtxos.map(utxoKey)));
      setActiveTab("builder");
    }
  }

  async function broadcastSpend() {
    if (!info || !session || !proposal) return;
    await withBusyAction("finalize-spend", async () => {
      const next = await run(ctx, "Finalizing multisig spend", () =>
        finalizeAndBroadcastSpend(
          info,
          session,
          proposal,
          votesForFinalization,
          executorFundingEnabled && executorFundingMnemonic?.trim()
            ? {
                mnemonic: executorFundingMnemonic,
                feeRate: executorFeeRate,
              }
            : undefined,
        ),
      );
      if (next) {
        setFinalSpend(next);
        await navigator.clipboard.writeText(next.txid).catch(() => undefined);
        if (await rescan()) {
          showToast(ctx, "success", "Final spend broadcast", next.txid);
        }
      }
    });
  }

  return {
    broadcastSpend,
    broadcastVote,
    buildProposal,
    claim,
    createDescriptor,
    decodeManualVote,
    fillDemo,
    fundFromFaucet,
    loadDescriptor,
    loadProposalFromVote,
    publishAnnouncement,
    refreshAnnouncements,
    rescan,
    signVote,
  };
}
