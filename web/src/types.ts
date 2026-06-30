type Participant = {
  index: number;
  xOnlyPublicKey: string;
  voteDescriptor: string;
};

type MultisigParticipant = {
  index: number;
  xOnlyPublicKey: string;
};

export type MultisigDescriptor = {
  version: number;
  network: "liquid-testnet";
  threshold: number;
  participants: MultisigParticipant[];
  multisigScriptPubkey: string;
  multisigAddress: string;
  lwkDescriptor: string;
};

export type MultisigSession = {
  version: number;
  network: "liquid-testnet";
  threshold: number;
  participants: Participant[];
  multisigScriptPubkey: string;
  multisigAddress: string;
  lwkDescriptor: string;
};

export type ParticipantKey = {
  derivationPath: string;
  xOnlyPublicKey: string;
};

export type LiquidTestnetInfo = {
  network: "liquid-testnet";
  policyAsset: string;
  genesisHash: string;
  defaultEsploraUrl: string;
  defaultWaterfallsUrl: string;
  explorerTxUrlPrefix: string;
};

export type WireUtxo = {
  txid: string;
  vout: number;
  scriptPubkey: string;
  asset: string;
  value: number;
};

type WireOutpoint = {
  txid: string;
  vout: number;
};

type SpendOutputKind = "transfer" | "burn" | "fee";

export type SpendOutput = {
  id: string;
  kind: SpendOutputKind;
  address: string;
  scriptPubkey?: string;
  asset: string;
  value: number;
};

export type ProposalResult = {
  psetBase64: string;
  txHex: string;
  totalProposedOutputs: number;
  messageHash: string;
  inputUtxos: WireUtxo[];
};

export type SignedVoteResult = {
  participantIndex: number;
  derivationPath: string;
  xOnlyPublicKey: string;
  messageHash: string;
  multisigInputCount: number;
  signatureHex: string;
  voteScriptPubkey: string;
  voteAddress: string;
  carrierOutputs: OutputSummary[];
};

export type CarrierAppendResult = {
  psetBase64: string;
  outputCount: number;
};

export type ParticipantAnnouncementAppendResult = {
  psetBase64: string;
  participantIndex: number;
  xOnlyPublicKey: string;
};

export type ParticipantAnnouncement = {
  participantIndex: number;
  xOnlyPublicKey: string;
  participantDescriptor: string;
  signatureHex: string;
  txid?: string;
  explorerUrl?: string;
};

export type DecodedVoteResult = {
  participantIndex: number;
  proposedPsetBase64: string;
  proposedTxHex: string;
  participantSignatureHex: string;
  messageHash: string;
  multisigInputCount: number;
  totalProposedOutputs: number;
  proposalInputOutpoints: WireOutpoint[];
  voteScriptPubkey: string;
  voteAddress: string;
  voteUtxo?: WireUtxo;
};

export type FinalizedSpendResult = {
  psetBase64: string;
  txHex: string;
  txid: string;
  explorerUrl: string;
};

export type PsetResult = {
  psetBase64: string;
};

export type ExecutorInputSecret = {
  asset: string;
  value: number;
  assetBlindingFactor: string;
  valueBlindingFactor: string;
};

type OutputSummary = {
  scriptPubkey: string;
  asset: string;
  value: number;
};

export type VoteInput = {
  participantIndex: number;
  signatureHex: string;
  utxo: WireUtxo;
};

export type ScanTransaction = {
  txid: string;
  type: string;
  height?: number;
  timestamp?: number;
  sources: string[];
  explorerUrl: string;
};

export type ScanVote = {
  participantIndex: number;
  txid: string;
  messageHash: string;
  signatureHex: string;
  proposedPsetBase64: string;
  proposedTxHex: string;
  totalProposedOutputs: number;
  proposalInputOutpoints: WireOutpoint[];
  voteAddress: string;
  voteUtxo?: WireUtxo;
  explorerUrl: string;
};

export type ScanState = {
  status: "idle" | "scanning" | "ready" | "error";
  message: string;
  utxos: WireUtxo[];
  transactions: ScanTransaction[];
  votes: ScanVote[];
  ownerUtxos: WireUtxo[];
};

export type AnnouncementScanState = {
  status: "idle" | "scanning" | "ready" | "error";
  message: string;
  announcements: ParticipantAnnouncement[];
  transactions: ScanTransaction[];
};

export type ClaimedParticipant = {
  participantIndex: number;
  xOnlyPublicKey: string;
  derivationPath: string;
  mnemonic: string;
  voteDescriptor: string;
  fundingAddress: string;
};

export type FaucetAsset = "lbtc" | "test";

export type FaucetTarget = "multisig" | "participant";

export type FaucetResult = {
  target: FaucetTarget;
  asset: FaucetAsset;
  address: string;
  message: string;
  txid?: string;
  explorerUrl?: string;
  balance?: number;
  balanceTest?: number;
};
