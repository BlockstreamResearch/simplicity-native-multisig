import { ExternalLink, Loader2, RefreshCcw } from "lucide-react";
import type { AppModel } from "../app-model";
import { Metric } from "../components";
import { middle, sats } from "../lib/format";

type ProposalsViewProps = {
  model: AppModel;
};

export function ProposalsView({ model }: ProposalsViewProps) {
  const {
    info,
    loadProposalFromVote,
    proposalGroups,
    rescan,
    scan,
    session,
    spendableVotes,
  } = model;

  return (
    <section className="proposal-stack">
      <section className="summary-grid">
        <Metric label="Spendable proposals" value={proposalGroups.length.toString()} />
        <Metric label="Spendable votes" value={spendableVotes.length.toString()} />
        <Metric label="Ready" value={proposalGroups.filter((item) => item.ready).length.toString()} />
        <Metric label="Threshold" value={(session?.threshold ?? "-").toString()} />
      </section>

      {proposalGroups.length === 0 ? (
        <div className="empty-state">
          <div>
            <strong>No spendable proposals discovered</strong>
            <span>Scan after votes are published. Spent or invalidated proposals are hidden.</span>
          </div>
          <button onClick={rescan} disabled={!session || !info || scan.status === "scanning"}>
            {scan.status === "scanning" ? (
              <Loader2 className="spin" size={15} />
            ) : (
              <RefreshCcw size={15} />
            )}
            Scan
          </button>
        </div>
      ) : (
        <div className="proposal-cards">
          {proposalGroups.map((group) => (
            <article className="proposal-card" key={group.messageHash}>
              <div className="proposal-card-head">
                <div>
                  <span className="muted-label">Proposal</span>
                  <strong>{middle(group.messageHash, 14)}</strong>
                </div>
                <span className={`proposal-state ${group.ready ? "ready" : "collecting"}`}>
                  {group.ready ? "Ready" : "Collecting"}
                </span>
              </div>

              <div className="proposal-meta">
                <div>
                  <span>Inputs</span>
                  <strong>{group.inputOutpoints.length}</strong>
                </div>
                <div>
                  <span>Input value</span>
                  <strong>{sats(group.inputValue)}</strong>
                </div>
                <div>
                  <span>Signed outputs</span>
                  <strong>{group.totalProposedOutputs}</strong>
                </div>
                <div>
                  <span>Votes</span>
                  <strong>
                    {group.votes.length}/{session?.threshold ?? "-"}
                  </strong>
                </div>
              </div>

              <div className="proposal-voters">
                {group.votes.map((item) => (
                  <div className="proposal-voter" key={`${group.messageHash}-${item.participantIndex}`}>
                    <span>
                      {item.participantIndex >= 0
                        ? `Participant ${item.participantIndex + 1}`
                        : "Manual"}
                    </span>
                    <strong>{middle(item.signatureHex, 10)}</strong>
                    {item.explorerUrl && (
                      <a href={item.explorerUrl} target="_blank" rel="noreferrer">
                        <ExternalLink size={14} />
                      </a>
                    )}
                  </div>
                ))}
              </div>

              <div className="proposal-card-actions">
                <button className="primary" onClick={() => loadProposalFromVote(group.votes[0])}>
                  Use proposal
                </button>
              </div>
            </article>
          ))}
        </div>
      )}
    </section>
  );
}
