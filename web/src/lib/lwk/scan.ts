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

export async function scanSession(
  session: MultisigSession,
  info: LiquidTestnetInfo,
  claimed?: ClaimedParticipant,
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
        .catch(() => ({ participant, scan: undefined }));
    }),
  );

  for (const { scan } of participantScans) {
    if (!scan) {
      continue;
    }

    for (const tx of scan.wallet.transactions()) {
      try {
        const decoded = await decodeVoteTransactionAuto(session, tx.tx().toString());
        const voteUtxo = decoded.voteUtxo;
        const proposalInputsLive = decoded.proposalInputOutpoints.every((outpoint) =>
          multisig.utxos.some((utxo) => utxo.txid === outpoint.txid && utxo.vout === outpoint.vout),
        );
        if (!voteUtxo || !proposalInputsLive) {
          continue;
        }
        const outspend = await esploraJson<{ spent: boolean }>(
          info,
          `/tx/${voteUtxo.txid}/outspend/${voteUtxo.vout}`,
        );
        if (outspend.spent) {
          continue;
        }

        votes.push({
          participantIndex: decoded.participantIndex,
          txid: tx.txid().toString(),
          messageHash: decoded.messageHash,
          signatureHex: decoded.participantSignatureHex,
          proposedPsetBase64: decoded.proposedPsetBase64,
          proposedTxHex: decoded.proposedTxHex,
          totalProposedOutputs: decoded.totalProposedOutputs,
          proposalInputOutpoints: decoded.proposalInputOutpoints,
          voteAddress: decoded.voteAddress,
          voteUtxo,
          explorerUrl: `${info.explorerTxUrlPrefix}${tx.txid().toString()}`,
        });
      } catch {
        // Most wallet transactions are not vote carrier transactions.
      }
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
