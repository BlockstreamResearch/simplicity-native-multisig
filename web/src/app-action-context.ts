import type { Dispatch, SetStateAction } from "react";
import type { AppTab, BusyAction, ToastMessage } from "./app-model";
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
  ScanVote,
  SignedVoteResult,
  SpendOutput,
  WireUtxo,
} from "./types";

type Setter<T> = Dispatch<SetStateAction<T>>;

export type AppActionContext = {
  activeMultisigDescriptor?: MultisigDescriptor;
  announcementMnemonic: string;
  announcementStake: number;
  announcementStakeValid: boolean;
  changeOutputs: SpendOutput[];
  claimed?: ClaimedParticipant;
  claimMnemonic: string;
  currentMultisigAddress?: string;
  descriptorText: string;
  executorFeeRate: number;
  executorFundingEnabled: boolean;
  executorFundingMnemonic?: string;
  feeAmount: number;
  info?: LiquidTestnetInfo;
  manualVoteTx: string;
  outputs: SpendOutput[];
  participantKeys: string[];
  proposal?: ProposalResult;
  proposalAmountErrors: string[];
  proposalAmountsValid: boolean;
  scan: ScanState;
  selectedUtxos: WireUtxo[];
  session?: MultisigSession;
  threshold: number;
  underfundedAssets: string[];
  vote?: SignedVoteResult;
  voteStake: number;
  voteStakeValid: boolean;
  votesForFinalization: ScanVote[];
  setActiveTab: Setter<AppTab>;
  setActivity: Setter<string>;
  setAnnouncementMnemonic: Setter<string>;
  setAnnouncementScan: Setter<AnnouncementScanState>;
  setBusyAction: Setter<BusyAction | undefined>;
  setClaimed: Setter<ClaimedParticipant | undefined>;
  setClaimMnemonic: Setter<string>;
  setDescriptorText: Setter<string>;
  setFaucetBusy: Setter<string | undefined>;
  setFaucetResult: Setter<FaucetResult | undefined>;
  setFinalSpend: Setter<FinalizedSpendResult | undefined>;
  setMultisigDescriptor: Setter<MultisigDescriptor | undefined>;
  setParticipantKeys: Setter<string[]>;
  setProposal: Setter<ProposalResult | undefined>;
  setScan: Setter<ScanState>;
  setSelectedInputs: Setter<Set<string>>;
  setSession: Setter<MultisigSession | undefined>;
  setThreshold: Setter<number>;
  setToast: Setter<ToastMessage | undefined>;
  setVote: Setter<SignedVoteResult | undefined>;
};
