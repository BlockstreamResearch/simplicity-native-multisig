import { Copy, Droplets, ExternalLink, Loader2 } from "lucide-react";
import { assetLabel } from "../app-helpers";
import type { AppModel } from "../app-model";
import { Panel } from "../components";
import { middle } from "../lib/format";
import type { FaucetAsset, FaucetTarget } from "../types";
import { liquidTestnetTestAssetId } from "./liquid-testnet-display";

type FaucetViewProps = {
  model: AppModel;
};

// In-app faucet requests go through the Vite dev-server proxy (the faucet API
// does not send CORS headers), so they only work in local development. Static
// deployments fall back to the external faucet page.
const inAppRequestsAvailable = import.meta.env.DEV;

export function FaucetView({ model }: FaucetViewProps) {
  const { claimed, currentMultisigAddress, faucetBusy, faucetResult, fundFromFaucet, info } = model;

  return (
    <section className="content-grid">
      <Panel title="Faucet funding" icon={<Droplets size={16} />} wide>
        <div className="funding-grid">
          <FundingTarget
            title="Multisig covenant"
            address={currentMultisigAddress}
            disabled={!currentMultisigAddress || !info}
            busy={faucetBusy}
            onFund={fundFromFaucet}
            target="multisig"
          />
          <FundingTarget
            title="Participant wallet"
            address={claimed?.fundingAddress}
            disabled={!claimed || !info}
            busy={faucetBusy}
            onFund={fundFromFaucet}
            target="participant"
          />
        </div>
        <div className="faucet-note">
          <span>
            {inAppRequestsAvailable
              ? "Faucet sends 100,000 L-BTC sats or 5,000 TEST units."
              : "In-app faucet requests need the local dev proxy. Copy an address and use the external faucet page instead."}
          </span>
          <span>TEST asset {middle(liquidTestnetTestAssetId, 10)}</span>
        </div>
        {faucetResult && (
          <div className="faucet-result">
            <div>
              <span>
                {faucetResult.target === "multisig" ? "Multisig" : "Participant"} ·{" "}
                {assetLabel(faucetResult.asset)}
              </span>
              <strong>{faucetResult.message}</strong>
            </div>
            {faucetResult.explorerUrl && (
              <a href={faucetResult.explorerUrl} target="_blank" rel="noreferrer">
                <ExternalLink size={14} />
                Tx
              </a>
            )}
          </div>
        )}
      </Panel>
    </section>
  );
}

function FundingTarget({
  title,
  address,
  disabled,
  busy,
  target,
  onFund,
}: {
  title: string;
  address?: string;
  disabled: boolean;
  busy?: string;
  target: FaucetTarget;
  onFund: (target: FaucetTarget, asset: FaucetAsset) => void;
}) {
  return (
    <div className="funding-target">
      <div>
        <span>{title}</span>
        <strong>{address ? middle(address, 18) : "Not available"}</strong>
      </div>
      <div className="button-row">
        {inAppRequestsAvailable && (
          <>
            <button onClick={() => onFund(target, "lbtc")} disabled={disabled || busy !== undefined}>
              {busy === `${target}:lbtc` ? (
                <Loader2 className="spin" size={15} />
              ) : (
                <Droplets size={15} />
              )}
              L-BTC
            </button>
            <button onClick={() => onFund(target, "test")} disabled={disabled || busy !== undefined}>
              {busy === `${target}:test` ? (
                <Loader2 className="spin" size={15} />
              ) : (
                <Droplets size={15} />
              )}
              TEST
            </button>
          </>
        )}
        {address && (
          <>
            <button onClick={() => navigator.clipboard.writeText(address)}>
              <Copy size={14} />
              Copy address
            </button>
            <a
              className="button-link"
              href="https://liquidtestnet.com/faucet"
              target="_blank"
              rel="noreferrer"
            >
              <ExternalLink size={14} />
              Open
            </a>
          </>
        )}
      </div>
    </div>
  );
}
