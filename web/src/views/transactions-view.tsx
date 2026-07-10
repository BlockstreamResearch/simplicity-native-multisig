import { ExternalLink, Loader2, Radio, RefreshCcw } from "lucide-react";
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
    actionBusy,
    activeMultisigDescriptor,
    info,
    rescan,
    scan,
    session,
    setTransactionQuery,
    setTransactionSource,
    transactionQuery,
    transactionSource,
    visibleTransactions,
    voteTxids,
  } = model;

  const mempoolCount = scan.transactions.filter((tx) => tx.height === undefined).length;

  return (
    <section className="transaction-stack">
      {scan.transactions.length > 0 && (
        <section className="summary-grid">
          <Metric label="All tx" value={scan.transactions.length.toString()} />
          <Metric label="Shown" value={visibleTransactions.length.toString()} />
          <Metric label="Votes" value={scan.votes.length.toString()} />
          <Metric label="In mempool" value={mempoolCount.toString()} />
        </section>
      )}

      <Panel
        title="Transactions"
        icon={<Radio size={16} />}
        wide
        actions={
          <button
            onClick={rescan}
            disabled={
              (!session && !activeMultisigDescriptor) ||
              !info ||
              scan.status === "scanning" ||
              actionBusy
            }
          >
            {scan.status === "scanning" ? (
              <Loader2 className="spin" size={15} />
            ) : (
              <RefreshCcw size={15} />
            )}
            Scan
          </button>
        }
      >
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
                <EmptyRow
                  colSpan={6}
                  label={
                    session
                      ? "No wallet transactions discovered — scan to refresh."
                      : "Transactions appear after the session is ready: they cover the multisig covenant, announced participants, and votes."
                  }
                />
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
                        : "pending"}
                    </td>
                    <td>
                      <a
                        href={tx.explorerUrl}
                        target="_blank"
                        rel="noreferrer"
                        aria-label={`View transaction ${middle(tx.txid, 6)} in explorer`}
                      >
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
