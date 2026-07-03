import { Plus, Trash2 } from "lucide-react";
import type { ReactNode } from "react";
import { amountFromInput, randomId } from "../app-helpers";
import type { AppModel } from "../app-model";
import { CodeBlock, Panel } from "../components";
import { middle, sats } from "../lib/format";
import type { SpendOutput } from "../types";

type ProposeSpendPanelProps = {
  icon: ReactNode;
  model: AppModel;
  outputValue: number;
  proposedSpendValue: number;
  selectedValue: number;
};

export function ProposeSpendPanel({
  icon,
  model,
  outputValue,
  proposedSpendValue,
  selectedValue,
}: ProposeSpendPanelProps) {
  const {
    buildProposal,
    feeAmount,
    info,
    outputs,
    policyChangeValue,
    proposal,
    proposalAmountErrors,
    proposalAmountsValid,
    selectedUtxos,
    session,
    setFeeAmount,
    setOutputs,
    underfundedAssets,
  } = model;

  function updateOutput(id: string, patch: Partial<SpendOutput>) {
    setOutputs((current) =>
      current.map((output) => (output.id === id ? { ...output, ...patch } : output)),
    );
  }

  return (
    <Panel title="Propose spend" icon={icon} wide>
      <div className="proposal-head">
        <div>
          <span className="muted-label">Selected</span>
          <strong>{sats(selectedValue)}</strong>
        </div>
        <div>
          <span className="muted-label">Outputs</span>
          <strong>{sats(outputValue)}</strong>
          <span>{sats(proposedSpendValue)} with fee</span>
        </div>
        <div>
          <span className="muted-label">Change</span>
          <strong>{sats(policyChangeValue)}</strong>
          <span>Back to multisig</span>
        </div>
        <div>
          <span className="muted-label">Fee</span>
          <input
            className="fee-input"
            type="number"
            min={0}
            step={1}
            value={feeAmount}
            onChange={(event) => setFeeAmount(amountFromInput(event.target.value))}
          />
        </div>
        <button
          onClick={() =>
            setOutputs((current) => [
              ...current,
              {
                id: randomId(),
                kind: "transfer",
                address: "",
                asset: info?.policyAsset ?? "",
                value: 1_000,
              },
            ])
          }
        >
          <Plus size={15} />
          Output
        </button>
      </div>

      <div className="outputs-list">
        {outputs.map((output) => (
          <div className="output-row" key={output.id}>
            <select
              value={output.kind}
              onChange={(event) =>
                updateOutput(output.id, {
                  kind: event.target.value as SpendOutput["kind"],
                })
              }
            >
              <option value="transfer">Transfer</option>
              <option value="burn">Burn</option>
            </select>
            <input
              value={output.address}
              disabled={output.kind !== "transfer"}
              onChange={(event) => updateOutput(output.id, { address: event.target.value })}
              placeholder={output.kind === "transfer" ? "Liquid testnet address" : ""}
            />
            <input
              value={output.asset}
              onChange={(event) => updateOutput(output.id, { asset: event.target.value })}
              placeholder="Asset id"
            />
            <input
              type="number"
              min={0}
              step={1}
              value={output.value}
              onChange={(event) =>
                updateOutput(output.id, { value: amountFromInput(event.target.value) })
              }
            />
            <button
              className="icon-only"
              onClick={() => setOutputs((current) => current.filter((item) => item.id !== output.id))}
            >
              <Trash2 size={15} />
            </button>
          </div>
        ))}
      </div>

      <div className="button-row end">
        <button
          className="primary"
          onClick={buildProposal}
          disabled={
            !session ||
            !info ||
            selectedUtxos.length === 0 ||
            !proposalAmountsValid ||
            underfundedAssets.length > 0
          }
        >
          Build proposal
        </button>
      </div>
      {proposalAmountErrors.length > 0 && <p className="empty-copy">{proposalAmountErrors[0]}</p>}
      {proposal && (
        <div className="proposal-result">
          <div className="inline-stat">
            <span>Message hash</span>
            <strong>{middle(proposal.messageHash, 12)}</strong>
          </div>
          <CodeBlock
            label={`Proposal PSET, ${proposal.totalProposedOutputs} signed outputs`}
            value={proposal.psetBase64}
          />
        </div>
      )}
    </Panel>
  );
}
