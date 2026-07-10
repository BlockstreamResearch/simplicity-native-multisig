import { useEffect, useMemo, useRef, useState } from "react";
import {
  emptyAnnouncementScan,
  emptyScan,
  finalizableVotes,
  groupSpendableProposals,
  randomId,
  utxoKey,
} from "./app-helpers";
import { clearProposalState } from "./app-action-tools";
import { createAppActions } from "./app-actions";
import { liquidTestnetInfo } from "./lib/contracts";
import { esploraFeeRateSatsPerVbyte } from "./lib/lwk/network";
import { outpointsAreLive } from "./lib/outpoints";
import { isPositiveSats } from "./lib/sats";
import type {
  AnnouncementScanState,
  ClaimedParticipant,
  FaucetResult,
  FinalizedSpendResult,
  LiquidTestnetInfo,
  MultisigDescriptor,
  MultisigSession,
  ProposalResult,
  ScanState,
  SignedVoteResult,
  SpendOutput,
} from "./types";

export type AppTab = "builder" | "proposals" | "create" | "setup" | "faucet" | "transactions";
export type BusyAction = "create-vote" | "publish-vote" | "finalize-spend" | "publish-announcement";
export type TransactionSourceFilter = "all" | "multisig" | "participants" | "votes";
export type ExecutorFundingSource = "verified" | "mnemonic";
export type FeeRateStatus = "loading" | "fetched" | "manual" | "fallback";
export type ToastMessage = {
  id: string;
  tone: "error" | "success";
  title: string;
  message: string;
  linkUrl?: string;
};

const activeTabStorageKey = "simplicity-multisig.active-tab";
const descriptorStorageKey = "simplicity-multisig.descriptor";
const appTabs: AppTab[] = ["builder", "proposals", "create", "setup", "faucet", "transactions"];

function readStorage(key: string): string | undefined {
  try {
    return window.localStorage.getItem(key) ?? undefined;
  } catch {
    return undefined;
  }
}

function writeStorage(key: string, value: string | undefined) {
  try {
    if (value === undefined) window.localStorage.removeItem(key);
    else window.localStorage.setItem(key, value);
  } catch {
    // Private browsing or blocked storage: the app still works, it just forgets.
  }
}

function storedActiveTab(): AppTab {
  const stored = readStorage(activeTabStorageKey);
  return appTabs.includes(stored as AppTab) ? (stored as AppTab) : "setup";
}

function safeSats(value: number): number {
  return Number.isFinite(value) ? value : 0;
}

function assetTotals(items: Array<{ asset: string; value: number }>): Map<string, number> {
  return items.reduce(
    (totals, item) => totals.set(item.asset, (totals.get(item.asset) ?? 0) + safeSats(item.value)),
    new Map<string, number>(),
  );
}

export function useAppModel() {
  const [activeTab, setActiveTab] = useState<AppTab>(storedActiveTab);
  const [info, setInfo] = useState<LiquidTestnetInfo>();
  const [descriptorText, setDescriptorText] = useState("");
  const [threshold, setThreshold] = useState(2);
  const [participantKeys, setParticipantKeys] = useState(["", "", ""]);
  const [multisigDescriptor, setMultisigDescriptor] = useState<MultisigDescriptor>();
  const [session, setSession] = useState<MultisigSession>();
  const [scan, setScan] = useState<ScanState>(emptyScan);
  const [announcementScan, setAnnouncementScan] =
    useState<AnnouncementScanState>(emptyAnnouncementScan);
  const [selectedInputs, setSelectedInputs] = useState<Set<string>>(new Set());
  const [outputs, setOutputs] = useState<SpendOutput[]>([]);
  const [proposal, setProposal] = useState<ProposalResult>();
  const [feeAmount, setFeeAmount] = useState(300);
  const [claimMnemonic, setClaimMnemonic] = useState("");
  const [announcementMnemonic, setAnnouncementMnemonic] = useState("");
  const [announcementStake, setAnnouncementStake] = useState(1_000);
  const [claimed, setClaimed] = useState<ClaimedParticipant>();
  const [vote, setVote] = useState<SignedVoteResult>();
  const [voteStake, setVoteStake] = useState(1_000);
  const [manualVoteTx, setManualVoteTx] = useState("");
  const [faucetBusy, setFaucetBusy] = useState<string>();
  const [faucetResult, setFaucetResult] = useState<FaucetResult>();
  const [finalSpend, setFinalSpend] = useState<FinalizedSpendResult>();
  const [busyAction, setBusyAction] = useState<BusyAction>();
  const [executorFundingEnabled, setExecutorFundingEnabled] = useState(false);
  const [executorFundingSource, setExecutorFundingSource] =
    useState<ExecutorFundingSource>("verified");
  const [executorMnemonic, setExecutorMnemonic] = useState("");
  const [executorFeeRate, setExecutorFeeRate] = useState(0.1);
  const [executorFeeRateStatus, setExecutorFeeRateStatus] =
    useState<FeeRateStatus>("manual");
  const [transactionSource, setTransactionSource] = useState<TransactionSourceFilter>("all");
  const [transactionQuery, setTransactionQuery] = useState("");
  const [activity, setActivity] = useState("Ready");
  const [toast, setToast] = useState<ToastMessage>();
  const [pendingDescriptorRestore] = useState(() => readStorage(descriptorStorageKey));
  const descriptorRestoreStarted = useRef(false);

  useEffect(() => {
    writeStorage(activeTabStorageKey, activeTab);
  }, [activeTab]);

  // Success toasts dismiss themselves; errors stay until read and dismissed.
  useEffect(() => {
    if (!toast || toast.tone !== "success") return;
    const timer = window.setTimeout(() => {
      setToast((current) => (current?.id === toast.id ? undefined : current));
    }, 8_000);
    return () => window.clearTimeout(timer);
  }, [toast]);

  useEffect(() => {
    liquidTestnetInfo()
      .then((next) => {
        setInfo(next);
        setOutputs([
          {
            id: randomId(),
            kind: "transfer",
            address: "",
            asset: next.policyAsset,
            value: 1_000,
          },
        ]);
      })
      .catch((nextError: unknown) => {
        const message = nextError instanceof Error ? nextError.message : String(nextError);
        setToast({
          id: randomId(),
          tone: "error",
          title: "Loading testnet constants failed",
          message,
        });
      });
  }, []);

  useEffect(() => {
    if (!info) return;

    let cancelled = false;
    setExecutorFeeRateStatus("loading");
    esploraFeeRateSatsPerVbyte(info)
      .then((next) => {
        if (!cancelled) {
          setExecutorFeeRate(Number(next.toFixed(2)));
          setExecutorFeeRateStatus("fetched");
        }
      })
      .catch(() => {
        if (!cancelled) {
          setExecutorFeeRateStatus("fallback");
        }
      });

    return () => {
      cancelled = true;
    };
  }, [info]);

  useEffect(() => {
    if (!claimed && executorFundingSource === "verified") {
      setExecutorFundingSource("mnemonic");
    }
  }, [claimed, executorFundingSource]);

  const selectedUtxos = useMemo(() => {
    return scan.utxos.filter((utxo) => selectedInputs.has(utxoKey(utxo)));
  }, [scan.utxos, selectedInputs]);

  const selectedValue = selectedUtxos.reduce((sum, utxo) => sum + safeSats(utxo.value), 0);
  const outputValue = outputs.reduce((sum, output) => sum + safeSats(output.value), 0);
  const proposedSpendValue = outputValue + safeSats(feeAmount);
  const proposalAmountErrors = [
    ...outputs.flatMap((output, index) =>
      isPositiveSats(output.value)
        ? []
        : [`Output ${index + 1} amount must be a whole positive satoshi amount.`],
    ),
    ...(Number.isSafeInteger(feeAmount) && feeAmount >= 0 && feeAmount <= Number.MAX_SAFE_INTEGER
      ? []
      : ["Fee must be a whole non-negative satoshi amount."]),
  ];
  const proposalAmountsValid = proposalAmountErrors.length === 0;
  const voteStakeValid = isPositiveSats(voteStake);
  const announcementStakeValid = isPositiveSats(announcementStake);
  const selectedByAsset = assetTotals(selectedUtxos);
  const outputByAsset = assetTotals(outputs);
  const requestedAssetValue = (asset: string) =>
    (outputByAsset.get(asset) ?? 0) + (asset === info?.policyAsset ? safeSats(feeAmount) : 0);
  const changeOutputs: SpendOutput[] =
    session && info
      ? [...selectedByAsset.entries()].flatMap(([asset, value]) => {
          const change = value - requestedAssetValue(asset);
          return change > 0
            ? [
                {
                  id: `change-${asset}`,
                  kind: "transfer" as const,
                  address: session.multisigAddress,
                  asset,
                  value: change,
                },
              ]
            : [];
        })
      : [];
  const underfundedAssets =
    info === undefined
      ? []
      : [...new Set([...outputByAsset.keys(), info.policyAsset])].filter(
          (asset) => requestedAssetValue(asset) > (selectedByAsset.get(asset) ?? 0),
        );
  const policyChangeValue =
    info === undefined
      ? 0
      : Math.max(
          0,
          (selectedByAsset.get(info.policyAsset) ?? 0) - requestedAssetValue(info.policyAsset),
        );

  const spendableVotes = useMemo(() => {
    return scan.votes.filter(
      (voteItem) =>
        voteItem.participantIndex >= 0 &&
        voteItem.voteUtxo !== undefined &&
        outpointsAreLive(voteItem.proposalInputOutpoints, scan.utxos),
    );
  }, [scan.utxos, scan.votes]);
  const proposalGroups = useMemo(
    () => groupSpendableProposals(spendableVotes, scan.utxos, session?.threshold ?? 0),
    [scan.utxos, session?.threshold, spendableVotes],
  );
  const eligibleVotes = useMemo(
    () =>
      finalizableVotes(
        spendableVotes.filter((item) => item.participantIndex >= 0),
        proposal?.messageHash,
      ),
    [proposal, spendableVotes],
  );
  const builderVotes = proposal ? eligibleVotes : spendableVotes;
  const voteTxids = useMemo(
    () => new Set(scan.votes.map((item) => item.txid)),
    [scan.votes],
  );
  const visibleTransactions = useMemo(() => {
    const query = transactionQuery.trim().toLowerCase();
    return scan.transactions.filter((tx) => {
      const isVote = voteTxids.has(tx.txid);
      const matchesSource =
        transactionSource === "all" ||
        (transactionSource === "votes" && isVote) ||
        (transactionSource === "multisig" && tx.sources.includes("Multisig")) ||
        (transactionSource === "participants" &&
          tx.sources.some((source) => source.startsWith("Participant")));
      if (!matchesSource) {
        return false;
      }
      if (!query) {
        return true;
      }
      return [tx.txid, tx.type, ...tx.sources].some((value) =>
        value.toLowerCase().includes(query),
      );
    });
  }, [scan.transactions, transactionQuery, transactionSource, voteTxids]);

  const votesForFinalization = eligibleVotes.slice(0, session?.threshold ?? 0);
  const executorFundingMnemonic =
    executorFundingSource === "verified" ? claimed?.mnemonic : executorMnemonic;
  const executorFundingReady =
    !executorFundingEnabled || Boolean(executorFundingMnemonic?.trim());
  const canFinalize =
    Boolean(info && session && proposal) &&
    votesForFinalization.length >= (session?.threshold ?? Number.POSITIVE_INFINITY) &&
    executorFundingReady;
  const actionBusy = busyAction !== undefined;
  const isCreatingVote = busyAction === "create-vote";
  const isPublishingVote = busyAction === "publish-vote";
  const isFinalizingSpend = busyAction === "finalize-spend";
  const isPublishingAnnouncement = busyAction === "publish-announcement";
  const activeMultisigDescriptor =
    multisigDescriptor ??
    (session
      ? {
          version: session.version,
          network: session.network,
          threshold: session.threshold,
          participants: session.participants.map((participant) => ({
            index: participant.index,
            xOnlyPublicKey: participant.xOnlyPublicKey,
          })),
          multisigScriptPubkey: session.multisigScriptPubkey,
          multisigAddress: session.multisigAddress,
          lwkDescriptor: session.lwkDescriptor,
        }
      : undefined);
  const currentMultisigAddress =
    session?.multisigAddress ?? activeMultisigDescriptor?.multisigAddress;

  useEffect(() => {
    if (
      proposal &&
      scan.status === "ready" &&
      !proposal.inputUtxos.every((utxo) =>
        scan.utxos.some((candidate) => candidate.txid === utxo.txid && candidate.vout === utxo.vout),
      )
    ) {
      clearProposalState({ setFinalSpend, setProposal, setVote });
    }
  }, [proposal, scan.status, scan.utxos]);

  const actions = createAppActions({
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
    setActivity,
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
    setToast,
    setVote,
  });

  // Keep the loaded descriptor across reloads: coordination waits on other
  // participants, so losing it to an accidental refresh is costly.
  useEffect(() => {
    if (multisigDescriptor) {
      writeStorage(descriptorStorageKey, JSON.stringify(multisigDescriptor));
    }
  }, [multisigDescriptor]);

  const restoreDescriptor = actions.loadDescriptor;
  useEffect(() => {
    if (!info || !pendingDescriptorRestore || descriptorRestoreStarted.current) return;
    descriptorRestoreStarted.current = true;
    void restoreDescriptor(pendingDescriptorRestore).then((restored) => {
      if (!restored) writeStorage(descriptorStorageKey, undefined);
    });
  }, [info, pendingDescriptorRestore, restoreDescriptor]);

  return {
    ...actions,
    actionBusy,
    activeMultisigDescriptor,
    activeTab,
    activity,
    announcementMnemonic,
    announcementScan,
    announcementStake,
    announcementStakeValid,
    builderVotes,
    canFinalize,
    changeOutputs,
    claimed,
    claimMnemonic,
    currentMultisigAddress,
    descriptorText,
    eligibleVotes,
    executorFeeRate,
    executorFeeRateStatus,
    executorFundingEnabled,
    executorFundingSource,
    executorMnemonic,
    faucetBusy,
    faucetResult,
    feeAmount,
    finalSpend,
    info,
    isCreatingVote,
    isFinalizingSpend,
    isPublishingAnnouncement,
    isPublishingVote,
    manualVoteTx,
    outputs,
    outputValue,
    participantKeys,
    policyChangeValue,
    proposal,
    proposalAmountErrors,
    proposalAmountsValid,
    proposalGroups,
    proposedSpendValue,
    scan,
    selectedInputs,
    selectedUtxos,
    selectedValue,
    session,
    setActiveTab,
    setAnnouncementMnemonic,
    setAnnouncementStake,
    setClaimMnemonic,
    setDescriptorText,
    setExecutorFeeRate,
    setExecutorFeeRateStatus,
    setExecutorFundingEnabled,
    setExecutorFundingSource,
    setExecutorMnemonic,
    setFeeAmount,
    setManualVoteTx,
    setOutputs,
    setParticipantKeys,
    setSelectedInputs,
    setThreshold,
    setToast,
    setTransactionQuery,
    setTransactionSource,
    setVoteStake,
    spendableVotes,
    threshold,
    toast,
    transactionQuery,
    transactionSource,
    underfundedAssets,
    visibleTransactions,
    vote,
    voteStake,
    voteStakeValid,
    voteTxids,
    votesForFinalization,
  };
}

export type AppModel = ReturnType<typeof useAppModel>;
