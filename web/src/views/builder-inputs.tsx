import { Check } from "lucide-react";
import type { ReactNode } from "react";
import type { AppModel } from "../app-model";
import { EmptyRow, Panel } from "../components";
import { middle, sats } from "../lib/format";
import { utxoKey } from "../app-helpers";

type BuilderPanelProps = {
  icon: ReactNode;
  model: AppModel;
};

export function MultisigInputsPanel({ icon, model }: BuilderPanelProps) {
  const { scan, selectedInputs, setSelectedInputs } = model;

  return (
    <Panel title="Multisig inputs" icon={icon}>
      <div className="table-wrap fixed-table">
        <table>
          <thead>
            <tr>
              <th></th>
              <th>Outpoint</th>
              <th>Amount</th>
              <th>Asset</th>
            </tr>
          </thead>
          <tbody>
            {scan.utxos.length === 0 ? (
              <EmptyRow colSpan={4} label="No multisig UTXOs from the current scan" />
            ) : (
              scan.utxos.map((utxo) => (
                <tr key={utxoKey(utxo)}>
                  <td>
                    <input
                      type="checkbox"
                      checked={selectedInputs.has(utxoKey(utxo))}
                      onChange={() =>
                        setSelectedInputs((current) => {
                          const next = new Set(current);
                          const key = utxoKey(utxo);
                          if (next.has(key)) next.delete(key);
                          else next.add(key);
                          return next;
                        })
                      }
                    />
                  </td>
                  <td>{middle(`${utxo.txid}:${utxo.vout}`, 10)}</td>
                  <td>{sats(utxo.value)}</td>
                  <td>{middle(utxo.asset)}</td>
                </tr>
              ))
            )}
          </tbody>
        </table>
      </div>
    </Panel>
  );
}

export function ClaimParticipantPanel({ icon, model }: BuilderPanelProps) {
  const { claim, claimed, claimMnemonic, session, setClaimMnemonic } = model;

  return (
    <Panel title="Claim participant" icon={icon}>
      <label>
        Mnemonic
        <textarea
          className="mnemonic"
          value={claimMnemonic}
          onChange={(event) => setClaimMnemonic(event.target.value)}
          rows={4}
          placeholder="Participant mnemonic"
        />
      </label>
      <button className="primary" onClick={claim} disabled={!session || !claimMnemonic}>
        Verify ownership
      </button>
      {!claimMnemonic && (
        <p className="hint">
          Paste the mnemonic of an announced participant to unlock voting and publishing.
        </p>
      )}
      {claimed && (
        <div className="claim-box">
          <Check size={16} />
          <div>
            <strong>Participant {claimed.participantIndex + 1}</strong>
            <span>{claimed.derivationPath}</span>
          </div>
        </div>
      )}
    </Panel>
  );
}
