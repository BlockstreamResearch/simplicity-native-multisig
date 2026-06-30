import type {
  DecodedVoteResult,
  AnnouncementScanState,
  FaucetAsset,
  ScanVote,
  WireUtxo,
  ScanState,
} from "./types";

type ProposalGroup = {
  messageHash: string;
  votes: ScanVote[];
  inputOutpoints: ScanVote["proposalInputOutpoints"];
  totalProposedOutputs: number;
  inputValue: number;
  ready: boolean;
};

export const emptyScan: ScanState = {
  status: "idle",
  message: "No scan yet",
  utxos: [],
  transactions: [],
  votes: [],
  ownerUtxos: [],
};

export const emptyAnnouncementScan: AnnouncementScanState = {
  status: "idle",
  message: "No announcement scan yet",
  announcements: [],
  transactions: [],
};

export function outputId(): string {
  return crypto.randomUUID();
}

export function utxoKey(utxo: WireUtxo): string {
  return `${utxo.txid}:${utxo.vout}`;
}

export function assetLabel(asset: FaucetAsset): string {
  return asset === "test" ? "TEST" : "L-BTC";
}

export function amountFromInput(value: string): number {
  if (value.trim() === "") {
    return 0;
  }
  const next = Number(value);
  return Number.isFinite(next) ? next : 0;
}

export function amountLabel(label: string): string {
  return `${label} must be a whole positive satoshi amount.`;
}

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

export function groupSpendableProposals(
  votes: ScanVote[],
  multisigUtxos: WireUtxo[],
  threshold: number,
): ProposalGroup[] {
  const byMessageHash = new Map<string, ScanVote[]>();
  for (const vote of votes) {
    byMessageHash.set(vote.messageHash, [
      ...(byMessageHash.get(vote.messageHash) ?? []),
      vote,
    ]);
  }

  return [...byMessageHash.entries()]
    .map(([messageHash, groupVotes]) => {
      const votes = finalizableVotes(groupVotes, messageHash);
      const firstVote = votes[0] ?? groupVotes[0];
      const inputValue = firstVote.proposalInputOutpoints.reduce((total, outpoint) => {
        const utxo = multisigUtxos.find(
          (candidate) => candidate.txid === outpoint.txid && candidate.vout === outpoint.vout,
        );
        return total + (utxo?.value ?? 0);
      }, 0);

      return {
        messageHash,
        votes,
        inputOutpoints: firstVote.proposalInputOutpoints,
        totalProposedOutputs: firstVote.totalProposedOutputs,
        inputValue,
        ready: threshold > 0 && votes.length >= threshold,
      };
    })
    .filter((group) => group.votes.length > 0)
    .sort((left, right) => {
      if (left.ready !== right.ready) return left.ready ? -1 : 1;
      if (left.votes.length !== right.votes.length) return right.votes.length - left.votes.length;
      return left.messageHash.localeCompare(right.messageHash);
    });
}

export function finalizableVotes(votes: ScanVote[], proposalMessageHash?: string): ScanVote[] {
  const byParticipant = new Map<number, ScanVote>();
  for (const vote of votes) {
    if (
      vote.participantIndex < 0 ||
      !vote.voteUtxo ||
      (proposalMessageHash !== undefined && vote.messageHash !== proposalMessageHash) ||
      byParticipant.has(vote.participantIndex)
    ) {
      continue;
    }
    byParticipant.set(vote.participantIndex, vote);
  }

  return [...byParticipant.values()].sort(
    (left, right) => left.participantIndex - right.participantIndex,
  );
}
