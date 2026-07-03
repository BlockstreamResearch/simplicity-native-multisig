import {
  createSessionFromParticipantAnnouncements,
  decodeParticipantAnnouncementTransaction,
  decodeVoteTransactionAuto,
} from "../contracts";
import type {
  AnnouncementScanState,
  ClaimedParticipant,
  LiquidTestnetInfo,
  MultisigDescriptor,
  MultisigSession,
  ParticipantAnnouncement,
  ScanState,
  ScanVote,
  WireUtxo,
} from "../../types";
import { loadLwk, walletScanIndex } from "./core";
import {
  esploraJson,
  esploraTxHex,
  scanDescriptor,
  scanMultisigAddress,
  waterfallsClient,
} from "./network";

async function validatedScanVote(
  session: MultisigSession,
  info: LiquidTestnetInfo,
  txid: string,
  txHex: string,
  multisigUtxos: WireUtxo[],
): Promise<ScanVote | undefined> {
  const decoded = await decodeVoteTransactionAuto(session, txHex);
  const voteUtxo = decoded.voteUtxo;
  const proposalInputsLive = decoded.proposalInputOutpoints.every((outpoint) =>
    multisigUtxos.some((utxo) => utxo.txid === outpoint.txid && utxo.vout === outpoint.vout),
  );
  if (!voteUtxo || !proposalInputsLive) {
    return undefined;
  }
  const outspend = await esploraJson<{ spent: boolean }>(
    info,
    `/tx/${voteUtxo.txid}/outspend/${voteUtxo.vout}`,
  );
  if (outspend.spent) {
    return undefined;
  }

  return {
    participantIndex: decoded.participantIndex,
    txid,
    messageHash: decoded.messageHash,
    signatureHex: decoded.participantSignatureHex,
    proposedPsetBase64: decoded.proposedPsetBase64,
    proposedTxHex: decoded.proposedTxHex,
    totalProposedOutputs: decoded.totalProposedOutputs,
    proposalInputOutpoints: decoded.proposalInputOutpoints,
    voteAddress: decoded.voteAddress,
    voteUtxo,
    explorerUrl: `${info.explorerTxUrlPrefix}${txid}`,
  };
}

export async function scanSession(
  session: MultisigSession,
  info: LiquidTestnetInfo,
  claimed?: ClaimedParticipant,
  knownVotes: ScanVote[] = [],
): Promise<ScanState> {
  const lwk = await loadLwk();
  const network = lwk.Network.testnet();
  const multisig = await scanMultisigAddress(session, info);
  const votes: ScanVote[] = [];
  const participantScans = await Promise.all(
    session.participants.map(async (participant) => {
      const client = await waterfallsClient(lwk, network, info);
      return scanDescriptor(
        lwk,
        network,
        client,
        participant.voteDescriptor,
        info,
        walletScanIndex,
      )
        .then((scan) => ({ participant, scan }))
        .catch((error: unknown) => {
          console.warn(`Participant ${participant.index + 1} vote wallet scan failed:`, error);
          return { participant, scan: undefined };
        });
    }),
  );

  for (const { scan } of participantScans) {
    if (!scan) {
      continue;
    }

    for (const tx of scan.wallet.transactions()) {
      const txid = tx.txid().toString();
      if (votes.some((vote) => vote.txid === txid)) {
        continue;
      }
      try {
        const vote = await validatedScanVote(session, info, txid, tx.tx().toString(), multisig.utxos);
        if (vote) {
          votes.push(vote);
        }
      } catch {
        // Most wallet transactions are not vote carrier transactions.
      }
    }
  }

  // Wallet indexers can lag behind just-broadcast vote transactions. Keep
  // votes that are already known locally, as long as they still validate
  // against esplora (unspent vote UTXO, live proposal inputs).
  for (const known of knownVotes) {
    if (votes.some((vote) => vote.txid === known.txid)) {
      continue;
    }
    try {
      const vote = await validatedScanVote(
        session,
        info,
        known.txid,
        await esploraTxHex(info, known.txid),
        multisig.utxos,
      );
      if (vote) {
        votes.push(vote);
      }
    } catch {
      // The known vote disappeared (evicted or reorged away): drop it.
    }
  }

  let ownerUtxos: WireUtxo[] = [];
  if (claimed) {
    ownerUtxos =
      (
        await scanDescriptor(
          lwk,
          network,
          await waterfallsClient(lwk, network, info),
          claimed.voteDescriptor,
          info,
          walletScanIndex,
        ).catch(() => undefined)
      )?.utxos ?? [];
  }

  const transactionsByTxid = new Map(
    multisig.transactions.map((transaction) => [
      transaction.txid,
      {
        ...transaction,
        sources: [...transaction.sources],
      },
    ]),
  );
  for (const { participant, scan } of participantScans) {
    if (!scan) {
      continue;
    }
    for (const transaction of scan.transactions) {
      const current = transactionsByTxid.get(transaction.txid);
      if (!current) {
        transactionsByTxid.set(transaction.txid, {
          ...transaction,
          sources: [`Participant ${participant.index + 1}`],
        });
        continue;
      }

      current.sources = [...new Set([...current.sources, `Participant ${participant.index + 1}`])];
      current.timestamp ??= transaction.timestamp;
      current.height ??= transaction.height;
    }
  }

  return {
    status: "ready",
    message: "Scan complete",
    utxos: multisig.utxos,
    transactions: [...transactionsByTxid.values()].sort((left, right) => {
      const leftTime = left.timestamp ?? left.height ?? 0;
      const rightTime = right.timestamp ?? right.height ?? 0;
      return rightTime - leftTime;
    }),
    votes,
    ownerUtxos,
  };
}

export async function discoverParticipantAnnouncements(
  multisigDescriptor: MultisigDescriptor,
  info: LiquidTestnetInfo,
): Promise<{
  scan: AnnouncementScanState;
  session?: MultisigSession;
}> {
  const multisig = await scanMultisigAddress(multisigDescriptor, info);
  const announcementsByParticipant = new Map<number, ParticipantAnnouncement>();

  await Promise.all(
    multisig.transactions.map(async (transaction) => {
      try {
        const txHex = await esploraTxHex(info, transaction.txid);
        const announcement = await decodeParticipantAnnouncementTransaction(
          multisigDescriptor,
          txHex,
        );
        const current = announcementsByParticipant.get(announcement.participantIndex);
        if (current && current.participantDescriptor !== announcement.participantDescriptor) {
          return;
        }
        announcementsByParticipant.set(announcement.participantIndex, {
          ...announcement,
          txid: transaction.txid,
          explorerUrl: transaction.explorerUrl,
        });
      } catch {
        // Most multisig funding transactions are not descriptor announcements.
      }
    }),
  );

  const announcements = [...announcementsByParticipant.values()].sort(
    (left, right) => left.participantIndex - right.participantIndex,
  );
  const scan: AnnouncementScanState = {
    status: "ready",
    message:
      announcements.length === multisigDescriptor.participants.length
        ? "Participant announcements complete"
        : "Waiting for participant announcements",
    announcements,
    transactions: multisig.transactions,
  };

  if (announcements.length !== multisigDescriptor.participants.length) {
    return { scan };
  }

  return {
    scan,
    session: await createSessionFromParticipantAnnouncements(multisigDescriptor, announcements),
  };
}
