import type * as Lwk from "lwk_wasm";
import {
  appendParticipantAnnouncementOutputs,
  appendVoteCarrierOutputs,
} from "../contracts";
import type {
  ClaimedParticipant,
  LiquidTestnetInfo,
  MultisigDescriptor,
  ProposalResult,
  SignedVoteResult,
} from "../../types";
import { loadLwk, walletScanIndex } from "./core";
import { esploraClient, scanDescriptor, waterfallsClient } from "./network";

export const publishFundingFeeRate = 1_000;

type PublishedVoteResult = {
  txid: string;
  txHex: string;
  explorerUrl: string;
};

function assertPositiveSafeSats(value: number, label: string) {
  if (!Number.isSafeInteger(value) || value <= 0) {
    throw new Error(`${label} must be a whole positive satoshi amount.`);
  }
}

export async function publishVote(
  info: LiquidTestnetInfo,
  claimed: ClaimedParticipant,
  proposal: ProposalResult,
  vote: SignedVoteResult,
  stakeSats: number,
): Promise<PublishedVoteResult> {
  assertPositiveSafeSats(stakeSats, "Vote amount");
  const lwk = await loadLwk();
  const network = lwk.Network.testnet();
  const client = await waterfallsClient(lwk, network, info);
  const ownerScan = await scanDescriptor(
    lwk,
    network,
    client,
    claimed.voteDescriptor,
    info,
    walletScanIndex,
  );
  const signer = new lwk.Signer(new lwk.Mnemonic(claimed.mnemonic), network);
  const builder = new lwk.TxBuilder(network)
    .feeRate(publishFundingFeeRate)
    .addExplicitRecipient(
      new lwk.Address(vote.voteAddress),
      BigInt(stakeSats),
      lwk.AssetId.fromString(info.policyAsset),
    );
  const unsignedVotePset = builder.finish(ownerScan.wallet);
  const appended = await appendVoteCarrierOutputs(
    unsignedVotePset.toString(),
    proposal.psetBase64,
    vote.signatureHex,
  );
  const signed = signer.sign(new lwk.Pset(appended.psetBase64));
  const finalized = ownerScan.wallet.finalize(signed);
  const tx = finalized.extractTx();
  const txid = await esploraClient(lwk, network, info).broadcast(finalized);
  return {
    txid: txid.toString(),
    txHex: tx.toString(),
    explorerUrl: `${info.explorerTxUrlPrefix}${txid.toString()}`,
  };
}

export async function publishParticipantAnnouncement(
  info: LiquidTestnetInfo,
  multisigDescriptor: MultisigDescriptor,
  mnemonic: string,
  stakeSats: number,
): Promise<{
  txid: string;
  participantIndex: number;
  participantDescriptor: string;
  explorerUrl: string;
}> {
  assertPositiveSafeSats(stakeSats, "Dust amount");
  const lwk = await loadLwk();
  const network = lwk.Network.testnet();
  const trimmed = mnemonic.trim();
  const signer: Lwk.Signer = new lwk.Signer(new lwk.Mnemonic(trimmed), network);
  const privateFundingDescriptor = signer.wpkhSlip77Descriptor().toString();
  const participantDescriptor = `elwpkh(${signer.keyoriginXpub(lwk.Bip.bip84())}/0/*)`;
  const ownerScan = await scanDescriptor(
    lwk,
    network,
    await waterfallsClient(lwk, network, info),
    privateFundingDescriptor,
    info,
    walletScanIndex,
  );
  const builder = new lwk.TxBuilder(network)
    .feeRate(publishFundingFeeRate)
    .addExplicitRecipient(
      new lwk.Address(multisigDescriptor.multisigAddress),
      BigInt(stakeSats),
      lwk.AssetId.fromString(info.policyAsset),
    );
  const unsigned = builder.finish(ownerScan.wallet);
  const appended = await appendParticipantAnnouncementOutputs(
    unsigned.toString(),
    multisigDescriptor,
    participantDescriptor,
    trimmed,
  );
  const signed = signer.sign(new lwk.Pset(appended.psetBase64));
  const finalized = ownerScan.wallet.finalize(signed);
  const txid = await esploraClient(lwk, network, info).broadcast(finalized);

  return {
    txid: txid.toString(),
    participantIndex: appended.participantIndex,
    participantDescriptor,
    explorerUrl: `${info.explorerTxUrlPrefix}${txid.toString()}`,
  };
}
