import {
  AlertTriangle,
  Check,
  CircleDot,
  Droplets,
  KeyRound,
  Loader2,
  Megaphone,
  Radio,
  RefreshCcw,
  Send,
  ShieldCheck,
  Vote,
} from "lucide-react";
import type { AppModel } from "./app-model";
import { middle } from "./lib/format";
import { BuilderView } from "./views/builder-view";
import { CreateView } from "./views/create-view";
import { FaucetView } from "./views/faucet-view";
import { ProposalsView } from "./views/proposals-view";
import { SetupView } from "./views/setup-view";
import { TransactionsView } from "./views/transactions-view";

type AppShellProps = {
  model: AppModel;
};

export function AppShell({ model }: AppShellProps) {
  const {
    actionBusy,
    activeMultisigDescriptor,
    activeTab,
    activity,
    announcementScan,
    currentMultisigAddress,
    info,
    scan,
    session,
    setActiveTab,
    setToast,
    toast,
    rescan,
  } = model;

  return (
    <main className="app-shell">
      <section className="workspace">
        <header className="topbar">
          <div className="brand">
            <div className="brand-mark">
              <ShieldCheck size={18} />
            </div>
            <div>
              <p className="muted-label">Simplicity coordination surface</p>
              <h1>Simplicity Native Multisig</h1>
              <h2>{currentMultisigAddress ? middle(currentMultisigAddress, 18) : "No descriptor loaded"}</h2>
            </div>
          </div>
          <div className="topbar-actions">
            <div className={`status ${scan.status}`}>
              {scan.status === "scanning" ? <Loader2 className="spin" /> : <CircleDot />}
              <span>{activity}</span>
            </div>
            <button
              className="icon-button"
              onClick={rescan}
              disabled={
                (!session && !activeMultisigDescriptor) ||
                !info ||
                scan.status === "scanning" ||
                announcementScan.status === "scanning" ||
                actionBusy
              }
            >
              <RefreshCcw />
              Scan
            </button>
          </div>
        </header>

        <nav className="tabs" aria-label="Workspace sections">
          <button
            className={activeTab === "builder" ? "active" : ""}
            onClick={() => setActiveTab("builder")}
          >
            <Send size={15} />
            Builder
          </button>
          <button
            className={activeTab === "proposals" ? "active" : ""}
            onClick={() => setActiveTab("proposals")}
          >
            <Vote size={15} />
            Proposals
          </button>
          <button
            className={activeTab === "create" ? "active" : ""}
            onClick={() => setActiveTab("create")}
          >
            <Megaphone size={15} />
            Create
          </button>
          <button
            className={activeTab === "setup" ? "active" : ""}
            onClick={() => setActiveTab("setup")}
          >
            <KeyRound size={15} />
            Setup
          </button>
          <button
            className={activeTab === "faucet" ? "active" : ""}
            onClick={() => setActiveTab("faucet")}
          >
            <Droplets size={15} />
            Faucet
          </button>
          <button
            className={activeTab === "transactions" ? "active" : ""}
            onClick={() => setActiveTab("transactions")}
          >
            <Radio size={15} />
            Transactions
          </button>
        </nav>

        {toast && (
          <div className="toast-stack" role="status" aria-live="polite">
            <div className={`toast ${toast.tone}`} key={toast.id}>
              {toast.tone === "error" ? <AlertTriangle size={17} /> : <Check size={17} />}
              <div>
                <strong>{toast.title}</strong>
                <span>{toast.message}</span>
              </div>
              <button onClick={() => setToast(undefined)}>Dismiss</button>
            </div>
          </div>
        )}
        {activeTab === "builder" && <BuilderView model={model} />}
        {activeTab === "proposals" && <ProposalsView model={model} />}
        {activeTab === "create" && <CreateView model={model} />}
        {activeTab === "setup" && <SetupView model={model} />}
        {activeTab === "faucet" && <FaucetView model={model} />}
        {activeTab === "transactions" && <TransactionsView model={model} />}
      </section>
    </main>
  );
}
