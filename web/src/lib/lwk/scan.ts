import {
  createSessionFromParticipantAnnouncements,
  decodeParticipantAnnouncementTransaction,
  decodeVoteTransactionAuto,
} from "../contracts";
import { outpointsAreLive } from "../outpoints";
import type {
  AnnouncementScanState,
  ClaimedParticipant,
  DecodedVoteResult,
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
  waterfallsScriptHistory,
} from "./network";

export function scanVoteFromDecoded(
  decoded: DecodedVoteResult,
  txid: string,
  explorerUrl: string,
): ScanVote {
  return {
    participantIndex: decoded.participantIndex,
    txid: decoded.voteUtxo?.txid ?? txid,
    messageHash: decoded.messageHash,
    signatureHex: decoded.participantSignatureHex,
    proposedPsetBase64: decoded.proposedPsetBase64,
    proposedTxHex: decoded.proposedTxHex,
    totalProposedOutputs: decoded.totalProposedOutputs,
    proposalInputOutpoints: decoded.proposalInputOutpoints,
    voteAddress: decoded.voteAddress,
    voteUtxo: decoded.voteUtxo,
    explorerUrl,
  };
}

// Whether a transaction carries a vote is deterministic, so decode results are
// cached for the session lifetime; `null` marks non-carrier transactions.
const voteDecodeCache = new Map<string, ScanVote | null>();

/** Strip a `ct(...)` wrapper so the descriptor can be queried at script level. */
function plainWatchDescriptor(voteDescriptor: string): string {
  const confidential = voteDescriptor.match(/^ct\([^,]+,(.*)\)$/);
  return confidential ? confidential[1] : voteDescriptor;
}

async function discoverVote(
  session: MultisigSession,
  info: LiquidTestnetInfo,
  txid: string,
): Promise<ScanVote | null> {
  const cacheKey = `${session.multisigScriptPubkey}:${txid}`;
  const cached = voteDecodeCache.get(cacheKey);
  if (cached !== undefined) {
    return cached;
  }

  let txHex: string;
  try {
    txHex = await esploraTxHex(info, txid);
  } catch {
    // Transient fetch failure: retry on the next scan instead of caching.
    return null;
  }

  let vote: ScanVote | null = null;
  try {
    const decoded = await decodeVoteTransactionAuto(session, txHex);
    vote = scanVoteFromDecoded(decoded, txid, `${info.explorerTxUrlPrefix}${txid}`);
  } catch {
    // Most transactions are not vote carrier transactions.
  }
  voteDecodeCache.set(cacheKey, vote);
  return vote;
}

async function voteIsLive(
  info: LiquidTestnetInfo,
  vote: ScanVote,
  multisigUtxos: WireUtxo[],
): Promise<boolean> {
  if (!vote.voteUtxo || !outpointsAreLive(vote.proposalInputOutpoints, multisigUtxos)) {
    return false;
  }
  const outspend = await esploraJson<{ spent: boolean }>(
    info,
    `/tx/${vote.voteUtxo.txid}/outspend/${vote.voteUtxo.vout}`,
  );
  return !outspend.spent;
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

  // Vote carriers are discovered at script level through the waterfalls
  // index. An LWK wallet scan cannot be used here: carriers funded purely
  // from confidential outputs are invisible to a watch-only wallet, which
  // only tracks outputs it can unblind. Votes for the current multisig UTXOs
  // cannot be older than the oldest of those UTXOs, which bounds how much
  // history has to be decoded.
  const candidateTxids = new Set<string>(knownVotes.map((known) => known.txid));
  if (multisig.utxos.length > 0) {
    const histories = await Promise.all(
      session.participants.map((participant) =>
        waterfallsScriptHistory(info, plainWatchDescriptor(participant.voteDescriptor)).catch(
          (error: unknown) => {
            console.warn(`Participant ${participant.index + 1} history scan failed:`, error);
            return [];
          },
        ),
      ),
    );
    for (const seen of histories.flat()) {
      if (
        seen.height === undefined ||
        seen.height <= 0 ||
        multisig.oldestUtxoHeight === undefined ||
        seen.height >= multisig.oldestUtxoHeight
      ) {
        candidateTxids.add(seen.txid);
      }
    }
  }

  for (const txid of candidateTxids) {
    const vote = await discoverVote(session, info, txid);
    if (
      vote &&
      !votes.some((item) => item.txid === vote.txid) &&
      (await voteIsLive(info, vote, multisig.utxos))
    ) {
      votes.push(vote);
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
