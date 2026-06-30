import type * as Lwk from "lwk_wasm";
import {
  finalizePreparedSpendPlan,
  finalizeSpendPlan,
  prepareExecutorFundedSpend,
} from "../contracts";
import type {
  ExecutorInputSecret,
  FinalizedSpendResult,
  LiquidTestnetInfo,
  MultisigSession,
  ProposalResult,
  ScanVote,
  VoteInput,
} from "../../types";
import { loadLwk, walletScanIndex } from "./core";
import { esploraClient, scanDescriptor, waterfallsClient } from "./network";

type ExecutorFeeFunding = {
  mnemonic: string;
  feeRate: number;
};

export async function finalizeAndBroadcastSpend(
  info: LiquidTestnetInfo,
  session: MultisigSession,
  proposal: ProposalResult,
  votes: ScanVote[],
  executorFunding?: ExecutorFeeFunding,
): Promise<FinalizedSpendResult> {
  const voteInputs = votes.flatMap((vote): VoteInput[] =>
    vote.voteUtxo
      ? [
          {
            participantIndex: vote.participantIndex,
            signatureHex: vote.signatureHex,
            utxo: vote.voteUtxo,
          },
        ]
      : [],
  );
  const lwk = await loadLwk();
  const network = lwk.Network.testnet();
  const client = esploraClient(lwk, network, info);
  const spendPlan = {
    session,
    proposedPsetBase64: proposal.psetBase64,
    multisigUtxos: proposal.inputUtxos,
    voteInputs,
    totalProposedOutputs: proposal.totalProposedOutputs,
  };
  let finalized: Omit<FinalizedSpendResult, "explorerUrl">;

  if (executorFunding?.mnemonic.trim()) {
    const signer = new lwk.Signer(new lwk.Mnemonic(executorFunding.mnemonic.trim()), network);
    const executorScan = await scanDescriptor(
      lwk,
      network,
      await waterfallsClient(lwk, network, info),
      signer.wpkhSlip77Descriptor().toString(),
      info,
      walletScanIndex,
    );
    const lbtcUtxos = executorScan.wallet
      .utxos()
      .filter((utxo) => utxo.unblinded().asset().toString() === info.policyAsset)
      .sort((left, right) => Number(right.unblinded().value() - left.unblinded().value()));
    if (lbtcUtxos.length === 0) {
      throw new Error("Executor wallet has no L-BTC UTXOs for finalization fees");
    }

    let executorPset: Lwk.Pset | undefined;
    let executorInputSecrets: ExecutorInputSecret[] = [];
    let executorFundingError: unknown;
    for (let count = 1; count <= lbtcUtxos.length; count += 1) {
      const selected = lbtcUtxos.slice(0, count);
      try {
        executorPset = new lwk.TxBuilder(network)
          .feeRate(executorFunding.feeRate)
          .setWalletUtxos(selected.map((utxo) => utxo.outpoint()))
          .drainLbtcTo(executorScan.wallet.address(0).address())
          .finish(executorScan.wallet);
        executorPset.addDetails(executorScan.wallet);
        executorInputSecrets = selected.map((utxo) => {
          const unblinded = utxo.unblinded();
          return {
            asset: unblinded.asset().toString(),
            value: Number(unblinded.value()),
            assetBlindingFactor: unblinded.assetBlindingFactor().toString(),
            valueBlindingFactor: unblinded.valueBlindingFactor().toString(),
          };
        });
        break;
      } catch (error) {
        executorFundingError = error;
      }
    }
    if (!executorPset) {
      const message =
        executorFundingError instanceof Error
          ? executorFundingError.message
          : String(executorFundingError);
      throw new Error(`Could not build executor fee funding PSET: ${message}`);
    }

    const prepared = await prepareExecutorFundedSpend({
      ...spendPlan,
      executorPsetBase64: executorPset.toString(),
      executorInputSecrets,
    });
    const signed = signer.sign(new lwk.Pset(prepared.psetBase64));
    const blinded = executorScan.wallet.finalize(signed);
    finalized = await finalizePreparedSpendPlan({
      ...spendPlan,
      preparedPsetBase64: blinded.toString(),
    });
  } else {
    finalized = await finalizeSpendPlan(spendPlan);
  }

  const txid = await client.broadcastTx(lwk.Transaction.fromString(finalized.txHex));

  return {
    ...finalized,
    txid: txid.toString(),
    explorerUrl: `${info.explorerTxUrlPrefix}${txid.toString()}`,
  };
}
