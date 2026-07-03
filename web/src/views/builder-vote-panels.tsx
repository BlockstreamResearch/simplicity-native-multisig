import { ExternalLink, Loader2, Radio } from "lucide-react";
import type { ReactNode } from "react";
import { amountFromInput } from "../app-helpers";
import { satsAmountError } from "../lib/sats";
import type { AppModel, ExecutorFundingSource, FeeRateStatus } from "../app-model";
import { Panel } from "../components";
import { middle } from "../lib/format";

type BuilderPanelProps = {
  icon: ReactNode;
  model: AppModel;
};

const feeRateStatusLabels: Record<FeeRateStatus, string> = {
  loading: "fetching",
  fetched: "fetched",
  fallback: "fallback",
  manual: "manual",
};

export function VotesPanel({ icon, model }: BuilderPanelProps) {
  const {
    actionBusy,
    broadcastVote,
    builderVotes,
    claimed,
    decodeManualVote,
    info,
    isCreatingVote,
    isPublishingVote,
    loadProposalFromVote,
    manualVoteTx,
    proposal,
    session,
    setManualVoteTx,
    setVoteStake,
    signVote,
    vote,
    voteStake,
    voteStakeValid,
  } = model;

  return (
    <Panel title="Votes" icon={icon}>
      <div className="button-row">
        <button className="primary" onClick={signVote} disabled={!session || !proposal || actionBusy}>
          {isCreatingVote && <Loader2 className="spin" size={15} />}
          {isCreatingVote ? "Creating" : "Create vote"}
        </button>
        <input
          className="stake-input"
          type="number"
          min={1}
          step={1}
          value={voteStake}
          disabled={actionBusy}
          onChange={(event) => setVoteStake(amountFromInput(event.target.value))}
        />
        <button
          onClick={broadcastVote}
          disabled={!info || !claimed || !proposal || !vote || !voteStakeValid || actionBusy}
        >
          {isPublishingVote ? <Loader2 className="spin" size={15} /> : <Radio size={15} />}
          {isPublishingVote ? "Publishing" : "Publish"}
        </button>
      </div>
      {!voteStakeValid && <p className="empty-copy">{satsAmountError("Vote amount")}</p>}
      {vote ? (
        <div className="vote-detail">
          <span>Participant {vote.participantIndex + 1}</span>
          <strong>{middle(vote.messageHash, 12)}</strong>
          <small>{middle(vote.voteAddress, 18)}</small>
        </div>
      ) : (
        <p className="empty-copy">No local vote created for the active proposal.</p>
      )}
      <div className="manual-decode">
        <textarea
          value={manualVoteTx}
          onChange={(event) => setManualVoteTx(event.target.value)}
          rows={3}
          placeholder="Paste vote transaction hex or txid to decode"
        />
        <button onClick={decodeManualVote} disabled={!session || !manualVoteTx}>
          Decode
        </button>
      </div>
      <div className="vote-list">
        {builderVotes.length === 0 ? (
          <p className="empty-copy">No spendable votes discovered.</p>
        ) : (
          builderVotes.map((item, index) => (
            <div className="vote-row" key={`${item.txid}-${index}`}>
              <span>
                {item.participantIndex >= 0
                  ? `Participant ${item.participantIndex + 1}`
                  : "Manual"}
              </span>
              <strong>{middle(item.messageHash, 10)}</strong>
              <small>
                {item.voteUtxo
                  ? middle(`${item.voteUtxo.txid}:${item.voteUtxo.vout}`, 8)
                  : "No vote UTXO"}
              </small>
              <div className="row-actions">
                {!proposal && <button onClick={() => loadProposalFromVote(item)}>Use</button>}
                {item.explorerUrl && (
                  <a href={item.explorerUrl} target="_blank" rel="noreferrer">
                    <ExternalLink size={14} />
                  </a>
                )}
              </div>
            </div>
          ))
        )}
      </div>
    </Panel>
  );
}

export function ExecuteSpendPanel({ icon, model }: BuilderPanelProps) {
  const {
    actionBusy,
    broadcastSpend,
    canFinalize,
    claimed,
    eligibleVotes,
    executorFeeRate,
    executorFeeRateStatus,
    executorFundingEnabled,
    executorFundingSource,
    executorMnemonic,
    finalSpend,
    isFinalizingSpend,
    proposal,
    session,
    setExecutorFeeRate,
    setExecutorFeeRateStatus,
    setExecutorFundingEnabled,
    setExecutorFundingSource,
    setExecutorMnemonic,
  } = model;

  return (
    <Panel title="Execute spend" icon={icon}>
      <div className="execute-head">
        <div>
          <span className="muted-label">Eligible votes</span>
          <strong>
            {eligibleVotes.length}/{session?.threshold ?? "-"}
          </strong>
        </div>
        <button className="primary" onClick={broadcastSpend} disabled={!canFinalize || actionBusy}>
          {isFinalizingSpend ? <Loader2 className="spin" size={15} /> : <Radio size={15} />}
          {isFinalizingSpend ? "Finalizing" : "Finalize"}
        </button>
      </div>
      <div className={`execute-funding ${executorFundingEnabled ? "enabled" : ""}`}>
        <div className="execute-funding-top">
          <label className="toggle-row">
            <input
              type="checkbox"
              checked={executorFundingEnabled}
              disabled={actionBusy}
              onChange={(event) => setExecutorFundingEnabled(event.target.checked)}
            />
            <span>Executor fee input</span>
          </label>
          <span className={`fee-rate-status ${executorFeeRateStatus}`}>
            Fee rate {feeRateStatusLabels[executorFeeRateStatus]}
          </span>
        </div>
        {executorFundingEnabled && (
          <>
            <div className="executor-controls">
              <label>
                Source
                <select
                  value={executorFundingSource}
                  disabled={actionBusy}
                  onChange={(event) =>
                    setExecutorFundingSource(event.target.value as ExecutorFundingSource)
                  }
                >
                  <option value="verified" disabled={!claimed}>
                    Verified participant
                  </option>
                  <option value="mnemonic">Mnemonic</option>
                </select>
              </label>
              <label>
                Fee rate
                <input
                  type="number"
                  min={0.1}
                  step={0.1}
                  value={executorFeeRate}
                  disabled={actionBusy}
                  onChange={(event) => {
                    setExecutorFeeRate(Number(event.target.value));
                    setExecutorFeeRateStatus("manual");
                  }}
                />
              </label>
            </div>
            {executorFundingSource === "mnemonic" && (
              <label>
                Executor mnemonic
                <textarea
                  className="mnemonic compact"
                  value={executorMnemonic}
                  disabled={actionBusy}
                  onChange={(event) => setExecutorMnemonic(event.target.value)}
                  rows={3}
                  placeholder="Mnemonic used only to fund and sign executor fee inputs"
                />
              </label>
            )}
            {executorFundingSource === "verified" && (
              <p className="empty-copy">
                {claimed
                  ? `Using Participant ${claimed.participantIndex + 1} wallet for fee inputs.`
                  : "Verify a participant or switch source to mnemonic."}
              </p>
            )}
          </>
        )}
      </div>
      <div className="vote-list">
        {eligibleVotes.length === 0 ? (
          <p className="empty-copy">
            {proposal
              ? "No discovered vote transactions can fund the final spend yet."
              : "Build a proposal or load one from a discovered vote before finalizing."}
          </p>
        ) : (
          eligibleVotes.map((item) => (
            <div className="vote-row" key={`execute-${item.participantIndex}`}>
              <span>Participant {item.participantIndex + 1}</span>
              <strong>{middle(item.signatureHex, 10)}</strong>
              <small>
                {item.voteUtxo
                  ? middle(`${item.voteUtxo.txid}:${item.voteUtxo.vout}`, 8)
                  : "No vote UTXO"}
              </small>
              {item.explorerUrl && (
                <a href={item.explorerUrl} target="_blank" rel="noreferrer">
                  <ExternalLink size={14} />
                </a>
              )}
            </div>
          ))
        )}
      </div>
      {finalSpend && (
        <div className="faucet-result">
          <div>
            <span>Final spend</span>
            <strong>{middle(finalSpend.txid, 16)}</strong>
          </div>
          <a href={finalSpend.explorerUrl} target="_blank" rel="noreferrer">
            <ExternalLink size={14} />
            Tx
          </a>
        </div>
      )}
    </Panel>
  );
}
