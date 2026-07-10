import { CircleDot, Copy, FileSearch, Fingerprint, Loader2, RefreshCcw } from "lucide-react";
import { randomId } from "../app-helpers";
import type { AppModel } from "../app-model";
import { Panel } from "../components";
import { demoMnemonics } from "../lib/demo";
import { middle } from "../lib/format";
import { liquidTestnetTestAssetId } from "./liquid-testnet-display";

type SetupViewProps = {
  model: AppModel;
};

export function SetupView({ model }: SetupViewProps) {
  const {
    activeMultisigDescriptor,
    announcementScan,
    descriptorText,
    info,
    loadDescriptor,
    participantKeys,
    refreshAnnouncements,
    session,
    setAnnouncementMnemonic,
    setActiveTab,
    setClaimMnemonic,
    setDescriptorText,
    setToast,
  } = model;

  return (
    <section className="setup-grid">
      <Panel title="Descriptor" icon={<FileSearch size={16} />}>
        <p className="panel-note">
          Paste a descriptor shared by the multisig creator, then scan announcements to recover
          the participant descriptors and unlock the full session.
        </p>
        <textarea
          value={descriptorText}
          onChange={(event) => setDescriptorText(event.target.value)}
          placeholder="Paste multisig descriptor JSON"
          rows={10}
        />
        <div className="button-row">
          <button className="primary" onClick={() => loadDescriptor()}>
            Load
          </button>
          <button onClick={() => refreshAnnouncements()} disabled={!activeMultisigDescriptor || !info}>
            {announcementScan.status === "scanning" ? (
              <Loader2 className="spin" size={15} />
            ) : (
              <RefreshCcw size={15} />
            )}
            Scan announcements
          </button>
          <button onClick={() => setActiveTab("create")}>Create a new multisig</button>
        </div>
        {activeMultisigDescriptor && !session && (
          <p className="hint">
            Descriptor loaded. Next step: every participant publishes an announcement on the{" "}
            <button className="inline-link" onClick={() => setActiveTab("create")}>
              Create tab
            </button>{" "}
            so the session can be recovered.
          </p>
        )}
      </Panel>

      <Panel title="Demo setup" icon={<Fingerprint size={16} />} wide>
        <p className="panel-note">
          Three throwaway participant wallets for the demo flow. "Use" fills the mnemonic into the
          Announce form (Create tab) and the Claim form (Builder tab).
        </p>
        <div className="demo-list">
          {demoMnemonics.map((mnemonic, index) => (
            <div className="demo-row" key={mnemonic}>
              <div>
                <span>Participant {index + 1}</span>
                <strong>
                  {participantKeys[index] ? middle(participantKeys[index], 12) : "Key not derived"}
                </strong>
              </div>
              <code>{mnemonic}</code>
              <div className="row-actions">
                <button
                  onClick={() => {
                    setClaimMnemonic(mnemonic);
                    setAnnouncementMnemonic(mnemonic);
                    setToast({
                      id: randomId(),
                      tone: "success",
                      title: `Demo participant ${index + 1} selected`,
                      message:
                        "Mnemonic filled into the Announce form (Create tab) and Claim form (Builder tab).",
                    });
                  }}
                >
                  Use
                </button>
                <button
                  aria-label={`Copy mnemonic for participant ${index + 1}`}
                  onClick={() => {
                    navigator.clipboard.writeText(mnemonic);
                    setToast({
                      id: randomId(),
                      tone: "success",
                      title: "Mnemonic copied",
                      message: `Demo participant ${index + 1} mnemonic is on the clipboard.`,
                    });
                  }}
                >
                  <Copy size={14} />
                </button>
              </div>
            </div>
          ))}
        </div>
      </Panel>

      <Panel title="Network" icon={<CircleDot size={16} />} wide>
        <div className="network-grid">
          <div>
            <span>Policy asset</span>
            <strong>{info ? middle(info.policyAsset) : "loading"}</strong>
          </div>
          <div>
            <span>TEST asset</span>
            <strong>{middle(liquidTestnetTestAssetId, 10)}</strong>
          </div>
          <div>
            <span>Waterfalls</span>
            <strong>{info ? new URL(info.defaultWaterfallsUrl).hostname : "loading"}</strong>
          </div>
          <div>
            <span>Explorer</span>
            <strong>{info ? new URL(info.explorerTxUrlPrefix).hostname : "loading"}</strong>
          </div>
        </div>
      </Panel>
    </section>
  );
}
