import { ExternalLink, Radio } from "lucide-react";
import type { AppModel, TransactionSourceFilter } from "../app-model";
import { EmptyRow, Metric, Panel } from "../components";
import { middle } from "../lib/format";

type TransactionsViewProps = {
  model: AppModel;
};

const transactionTimeFormat = new Intl.DateTimeFormat("en", {
  month: "short",
  day: "numeric",
  hour: "2-digit",
  minute: "2-digit",
});

export function TransactionsView({ model }: TransactionsViewProps) {
  const {
    scan,
    setTransactionQuery,
    setTransactionSource,
    transactionQuery,
    transactionSource,
    visibleTransactions,
    voteTxids,
  } = model;

  return (
    <section className="transaction-stack">
      <section className="summary-grid compact">
        <Metric label="All tx" value={scan.transactions.length.toString()} />
        <Metric label="Shown" value={visibleTransactions.length.toString()} />
        <Metric label="Votes" value={scan.votes.length.toString()} />
        <Metric label="Participant UTXOs" value={scan.ownerUtxos.length.toString()} />
      </section>

      <Panel title="Transactions" icon={<Radio size={16} />} wide>
        <div className="transaction-toolbar">
          <div className="segmented">
            {(["all", "multisig", "participants", "votes"] as TransactionSourceFilter[]).map(
              (source) => (
                <button
                  key={source}
                  className={transactionSource === source ? "active" : ""}
                  onClick={() => setTransactionSource(source)}
                >
                  {source === "all"
                    ? "All"
                    : source === "multisig"
                      ? "Multisig"
                      : source === "participants"
                        ? "Participants"
                        : "Votes"}
                </button>
              ),
            )}
          </div>
          <input
            className="transaction-search"
            value={transactionQuery}
            onChange={(event) => setTransactionQuery(event.target.value)}
            placeholder="Search txid, type, source"
          />
        </div>
        <div className="table-wrap transaction-table">
          <table>
            <thead>
              <tr>
                <th>Source</th>
                <th>Txid</th>
                <th>Type</th>
                <th>Height</th>
                <th>Time</th>
                <th></th>
              </tr>
            </thead>
            <tbody>
              {visibleTransactions.length === 0 ? (
                <EmptyRow colSpan={6} label="No wallet transactions discovered" />
              ) : (
                visibleTransactions.map((tx) => (
                  <tr key={tx.txid}>
                    <td>
                      {[...new Set([...tx.sources, ...(voteTxids.has(tx.txid) ? ["Vote"] : [])])].join(
                        ", ",
                      )}
                    </td>
                    <td>{middle(tx.txid, 12)}</td>
                    <td>{voteTxids.has(tx.txid) ? "vote" : tx.type}</td>
                    <td>{tx.height ?? "mempool"}</td>
                    <td>
                      {tx.timestamp
                        ? transactionTimeFormat.format(new Date(tx.timestamp * 1000))
                        : "mempool"}
                    </td>
                    <td>
                      <a href={tx.explorerUrl} target="_blank" rel="noreferrer">
                        <ExternalLink size={15} />
                      </a>
                    </td>
                  </tr>
                ))
              )}
            </tbody>
          </table>
        </div>
      </Panel>
    </section>
  );
}
