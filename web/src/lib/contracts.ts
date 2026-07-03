import type {
  DecodedVoteResult,
  FinalizedSpendResult,
  ExecutorInputSecret,
  LiquidTestnetInfo,
  MultisigDescriptor,
  MultisigSession,
  ParticipantAnnouncement,
  ParticipantAnnouncementAppendResult,
  ParticipantKey,
  ProposalResult,
  PsetResult,
  SignedVoteResult,
  SpendOutput,
  WireUtxo,
  VoteInput,
} from "../types";

type ContractModule = typeof import("../generated/contracts/simplicity_native_multisig_wasm.js");

let modulePromise: Promise<ContractModule> | undefined;

async function contracts(): Promise<ContractModule> {
  modulePromise ??= import("../generated/contracts/simplicity_native_multisig_wasm.js").then(
    async (contractModule) => {
      await contractModule.default();
      return contractModule;
    },
  );
  return modulePromise;
}

async function callJson<T>(call: (contractModule: ContractModule) => string): Promise<T> {
  return JSON.parse(call(await contracts())) as T;
}

export async function liquidTestnetInfo(): Promise<LiquidTestnetInfo> {
  return callJson((contractModule) => contractModule.liquidTestnetInfo());
}

export async function deriveParticipantKey(
  mnemonic: string,
  account: number,
): Promise<ParticipantKey> {
  return callJson((contractModule) =>
    contractModule.deriveParticipantKey(mnemonic, account),
  );
}

export async function createMultisigDescriptor(
  threshold: number,
  participantPubkeys: string[],
): Promise<MultisigDescriptor> {
  return callJson((contractModule) =>
    contractModule.createMultisigDescriptor(
      threshold,
      JSON.stringify(participantPubkeys),
    ),
  );
}

export async function inspectMultisigDescriptor(
  descriptorJson: string,
): Promise<MultisigDescriptor> {
  return callJson((contractModule) =>
    contractModule.inspectMultisigDescriptor(descriptorJson),
  );
}

export async function appendParticipantAnnouncementOutputs(
  announcementPsetBase64: string,
  multisigDescriptor: MultisigDescriptor,
  participantDescriptor: string,
  mnemonic: string,
): Promise<ParticipantAnnouncementAppendResult> {
  return callJson((contractModule) =>
    contractModule.appendParticipantAnnouncementOutputs(
      announcementPsetBase64,
      JSON.stringify(multisigDescriptor),
      participantDescriptor,
      mnemonic,
    ),
  );
}

export async function decodeParticipantAnnouncementTransaction(
  multisigDescriptor: MultisigDescriptor,
  txHex: string,
): Promise<ParticipantAnnouncement> {
  return callJson((contractModule) =>
    contractModule.decodeParticipantAnnouncementTransaction(
      JSON.stringify(multisigDescriptor),
      txHex,
    ),
  );
}

export async function createSessionFromParticipantAnnouncements(
  multisigDescriptor: MultisigDescriptor,
  announcements: ParticipantAnnouncement[],
): Promise<MultisigSession> {
  return callJson((contractModule) =>
    contractModule.createSessionFromParticipantAnnouncements(
      JSON.stringify(multisigDescriptor),
      JSON.stringify(announcements),
    ),
  );
}

export async function createProposedSpend(
  session: MultisigSession,
  utxos: WireUtxo[],
  outputs: SpendOutput[],
): Promise<ProposalResult> {
  const wireOutputs = outputs.map((output) => ({
    kind: output.kind,
    address: output.kind === "transfer" ? output.address : undefined,
    scriptPubkey: output.scriptPubkey,
    asset: output.asset,
    value: output.value,
  }));

  const result = await callJson<Omit<ProposalResult, "inputUtxos">>((contractModule) =>
    contractModule.createProposedSpend(
      JSON.stringify(session),
      JSON.stringify(utxos),
      JSON.stringify(wireOutputs),
    ),
  );
  return { ...result, inputUtxos: utxos };
}

export async function createSignedVote(
  session: MultisigSession,
  proposedPsetBase64: string,
  totalProposedOutputs: number,
  mnemonic: string,
): Promise<SignedVoteResult> {
  return callJson((contractModule) =>
    contractModule.createSignedVote(
      JSON.stringify(session),
      proposedPsetBase64,
      totalProposedOutputs,
      mnemonic,
    ),
  );
}

export async function appendVoteCarrierOutputs(
  votePsetBase64: string,
  proposedPsetBase64: string,
  participantSignatureHex: string,
): Promise<PsetResult> {
  return callJson((contractModule) =>
    contractModule.appendVoteCarrierOutputs(
      votePsetBase64,
      proposedPsetBase64,
      participantSignatureHex,
    ),
  );
}

export async function decodeVoteTransaction(
  session: MultisigSession,
  txHex: string,
  totalProposedOutputs: number,
): Promise<DecodedVoteResult> {
  return callJson((contractModule) =>
    contractModule.decodeVoteTransaction(
      JSON.stringify(session),
      txHex,
      totalProposedOutputs,
    ),
  );
}

export async function decodeVoteTransactionAuto(
  session: MultisigSession,
  txHex: string,
): Promise<DecodedVoteResult> {
  return callJson((contractModule) =>
    contractModule.decodeVoteTransactionAuto(JSON.stringify(session), txHex),
  );
}

type SpendPlan = {
  session: MultisigSession;
  proposedPsetBase64: string;
  multisigUtxos: WireUtxo[];
  voteInputs: VoteInput[];
  totalProposedOutputs: number;
};

export async function finalizeSpendPlan(
  plan: SpendPlan,
): Promise<Omit<FinalizedSpendResult, "explorerUrl">> {
  return callJson((contractModule) =>
    contractModule.finalizeSpendPlan(JSON.stringify(plan)),
  );
}

export async function prepareExecutorFundedSpend(
  plan: SpendPlan & {
    executorPsetBase64: string;
    executorInputSecrets: ExecutorInputSecret[];
  },
): Promise<PsetResult> {
  return callJson((contractModule) =>
    contractModule.prepareExecutorFundedSpend(JSON.stringify(plan)),
  );
}

export async function finalizePreparedSpendPlan(
  plan: SpendPlan & { preparedPsetBase64: string },
): Promise<Omit<FinalizedSpendResult, "explorerUrl">> {
  return callJson((contractModule) =>
    contractModule.finalizePreparedSpendPlan(JSON.stringify(plan)),
  );
}
