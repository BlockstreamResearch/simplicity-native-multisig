import {
  AlertTriangle,
  Check,
  CircleDot,
  Copy,
  Droplets,
  ExternalLink,
  FileText,
  KeyRound,
  Loader2,
  Megaphone,
  Radio,
  RefreshCcw,
  Send,
  ShieldCheck,
  Vote,
} from "lucide-react";
import { useEffect, useRef, useState } from "react";
import type { AppModel, AppTab } from "./app-model";
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

const tabItems: { tab: AppTab; label: string; icon: typeof Send }[] = [
  { tab: "setup", label: "Setup", icon: KeyRound },
  { tab: "create", label: "Create", icon: Megaphone },
  { tab: "faucet", label: "Faucet", icon: Droplets },
  { tab: "builder", label: "Builder", icon: Send },
  { tab: "proposals", label: "Proposals", icon: Vote },
  { tab: "transactions", label: "Transactions", icon: Radio },
];

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
      <header className="topband">
        <div className="topband-inner">
          <div className="brand">
            <div className="brand-mark">
              <ShieldCheck size={20} />
            </div>
            <div>
              <p className="muted-label">Liquid testnet · covenant coordination</p>
              <h1>Simplicity Native Multisig</h1>
            </div>
          </div>
          <div className="topbar-actions">
            <AddressChip address={currentMultisigAddress} />
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
            <a
              className="button-link"
              href={`${import.meta.env.BASE_URL}paper.pdf`}
              target="_blank"
              rel="noreferrer"
            >
              <FileText size={15} />
              Whitepaper
            </a>
          </div>
        </div>
        <nav className="tabs" aria-label="Workspace sections">
          {tabItems.map(({ tab, label, icon: Icon }) => (
            <button
              key={tab}
              className={activeTab === tab ? "active" : ""}
              onClick={() => setActiveTab(tab)}
            >
              <Icon size={15} />
              {label}
            </button>
          ))}
        </nav>
      </header>

      <section className="workspace">
        {toast && (
          <div className="toast-stack">
            <div
              className={`toast ${toast.tone}`}
              key={toast.id}
              role={toast.tone === "error" ? "alert" : "status"}
            >
              {toast.tone === "error" ? <AlertTriangle size={17} /> : <Check size={17} />}
              <div>
                <strong>{toast.title}</strong>
                <span>{toast.message}</span>
                {toast.linkUrl && (
                  <a href={toast.linkUrl} target="_blank" rel="noreferrer">
                    <ExternalLink size={13} />
                    View in explorer
                  </a>
                )}
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

function AddressChip({ address }: { address?: string }) {
  const [copied, setCopied] = useState(false);
  const resetTimer = useRef<number>(undefined);

  useEffect(() => () => window.clearTimeout(resetTimer.current), []);

  if (!address) {
    return <span className="address-chip placeholder">No descriptor loaded</span>;
  }

  return (
    <button
      className="address-chip"
      title={address}
      aria-label={`Copy multisig address ${address}`}
      onClick={() => {
        navigator.clipboard.writeText(address);
        setCopied(true);
        window.clearTimeout(resetTimer.current);
        resetTimer.current = window.setTimeout(() => setCopied(false), 1600);
      }}
    >
      {middle(address, 18)}
      {copied ? <Check size={12} /> : <Copy size={12} />}
    </button>
  );
}
