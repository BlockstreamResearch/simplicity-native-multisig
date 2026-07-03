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
import { assertPositiveSats } from "../sats";
import { loadLwk, walletScanIndex } from "./core";
import { esploraClient, scanDescriptor, waterfallsClient } from "./network";

export const publishFundingFeeRate = 1_000;

type PublishedCarrier = {
  txid: string;
  txHex: string;
  explorerUrl: string;
};

/**
 * Fund a dust payment to `payToAddress` from `fundingDescriptor`, let
 * `appendOutputs` attach the OP_RETURN carrier records, then sign and
 * broadcast. Votes and participant announcements share this shape.
 */
async function publishCarrierTransaction(
  info: LiquidTestnetInfo,
  fundingDescriptor: string,
  mnemonic: string,
  payToAddress: string,
  stakeSats: number,
  appendOutputs: (unsignedPsetBase64: string) => Promise<string>,
): Promise<PublishedCarrier> {
  const lwk = await loadLwk();
  const network = lwk.Network.testnet();
  const ownerScan = await scanDescriptor(
    lwk,
    network,
    await waterfallsClient(lwk, network, info),
    fundingDescriptor,
    info,
    walletScanIndex,
  );
  const unsigned = new lwk.TxBuilder(network)
    .feeRate(publishFundingFeeRate)
    .addExplicitRecipient(
      new lwk.Address(payToAddress),
      BigInt(stakeSats),
      lwk.AssetId.fromString(info.policyAsset),
    )
    .finish(ownerScan.wallet);
  const appended = await appendOutputs(unsigned.toString());
  const signer = new lwk.Signer(new lwk.Mnemonic(mnemonic), network);
  const signed = signer.sign(new lwk.Pset(appended));
  const finalized = ownerScan.wallet.finalize(signed);
  const txHex = finalized.extractTx().toString();
  const txid = (await esploraClient(lwk, network, info).broadcast(finalized)).toString();

  return {
    txid,
    txHex,
    explorerUrl: `${info.explorerTxUrlPrefix}${txid}`,
  };
}

export async function publishVote(
  info: LiquidTestnetInfo,
  claimed: ClaimedParticipant,
  proposal: ProposalResult,
  vote: SignedVoteResult,
  stakeSats: number,
): Promise<PublishedCarrier> {
  assertPositiveSats(stakeSats, "Vote amount");

  return publishCarrierTransaction(
    info,
    claimed.voteDescriptor,
    claimed.mnemonic,
    vote.voteAddress,
    stakeSats,
    async (unsignedPsetBase64) =>
      (
        await appendVoteCarrierOutputs(
          unsignedPsetBase64,
          proposal.psetBase64,
          vote.signatureHex,
        )
      ).psetBase64,
  );
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
  assertPositiveSats(stakeSats, "Dust amount");
  const lwk = await loadLwk();
  const trimmed = mnemonic.trim();
  const signer = new lwk.Signer(new lwk.Mnemonic(trimmed), lwk.Network.testnet());
  const participantDescriptor = `elwpkh(${signer.keyoriginXpub(lwk.Bip.bip84())}/0/*)`;

  let participantIndex = -1;
  const published = await publishCarrierTransaction(
    info,
    signer.wpkhSlip77Descriptor().toString(),
    trimmed,
    multisigDescriptor.multisigAddress,
    stakeSats,
    async (unsignedPsetBase64) => {
      const appended = await appendParticipantAnnouncementOutputs(
        unsignedPsetBase64,
        multisigDescriptor,
        participantDescriptor,
        trimmed,
      );
      participantIndex = appended.participantIndex;
      return appended.psetBase64;
    },
  );

  return {
    txid: published.txid,
    participantIndex,
    participantDescriptor,
    explorerUrl: published.explorerUrl,
  };
}
