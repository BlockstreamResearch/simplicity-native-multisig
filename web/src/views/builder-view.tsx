import { AlertTriangle, CircleDot, Fingerprint, KeyRound, Send, ShieldCheck, Vote } from "lucide-react";
import type { AppModel } from "../app-model";
import { FlowSteps, Metric } from "../components";
import type { FlowStep } from "../components";
import { ClaimParticipantPanel, MultisigInputsPanel } from "./builder-inputs";
import { ProposeSpendPanel } from "./builder-proposal-panel";
import { ExecuteSpendPanel, VotesPanel } from "./builder-vote-panels";

type BuilderViewProps = {
  model: AppModel;
};

export function BuilderView({ model }: BuilderViewProps) {
  const {
    canFinalize,
    eligibleVotes,
    finalSpend,
    outputValue,
    proposal,
    proposalGroups,
    proposedSpendValue,
    scan,
    selectedUtxos,
    selectedValue,
    session,
    setActiveTab,
  } = model;

  const threshold = session?.threshold;
  const votesReady = threshold !== undefined && eligibleVotes.length >= threshold;
  const spendSteps: FlowStep[] = [
    {
      label: "Select inputs",
      state: selectedUtxos.length > 0 ? "done" : "active",
    },
    {
      label: "Build proposal",
      state: proposal ? "done" : selectedUtxos.length > 0 ? "active" : "todo",
    },
    {
      label: "Collect votes",
      meta: proposal ? `${eligibleVotes.length}/${threshold ?? "-"}` : undefined,
      state: votesReady && proposal ? "done" : proposal ? "active" : "todo",
    },
    {
      label: "Finalize spend",
      state: finalSpend ? "done" : canFinalize ? "active" : "todo",
    },
  ];

  return (
    <>
      {!session && (
        <div className="empty-state">
          <div>
            <strong>No multisig descriptor loaded</strong>
            <span>Load an existing descriptor or create a demo descriptor before scanning.</span>
          </div>
          <button className="primary" onClick={() => setActiveTab("setup")}>
            <KeyRound size={15} />
            Open setup
          </button>
        </div>
      )}

      <div className="flow-bar">
        <FlowSteps steps={spendSteps} />
        <span className="flow-note">
          <AlertTriangle size={14} />
          Liquid testnet demo. Proposal outputs are limited to transfers and burns.
        </span>
      </div>

      <section className="summary-grid">
        <Metric label="Multisig UTXOs" value={scan.utxos.length.toString()} />
        <Metric label="Proposals" value={proposalGroups.length.toString()} />
        <Metric
          label="Eligible votes"
          value={proposal ? `${eligibleVotes.length}/${session?.threshold ?? "-"}` : "No proposal"}
        />
        <Metric label="Owner UTXOs" value={scan.ownerUtxos.length.toString()} />
      </section>

      <section className="content-grid">
        <MultisigInputsPanel icon={<CircleDot size={16} />} model={model} />
        <ClaimParticipantPanel icon={<Fingerprint size={16} />} model={model} />
        <ProposeSpendPanel
          icon={<Send size={16} />}
          model={model}
          outputValue={outputValue}
          proposedSpendValue={proposedSpendValue}
          selectedValue={selectedValue}
        />
        <VotesPanel icon={<Vote size={16} />} model={model} />
        <ExecuteSpendPanel icon={<ShieldCheck size={16} />} model={model} />
      </section>
    </>
  );
}
