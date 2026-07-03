import type { WireUtxo } from "../types";

type Outpoint = {
  txid: string;
  vout: number;
};

export function utxoKey(outpoint: Outpoint): string {
  return `${outpoint.txid}:${outpoint.vout}`;
}

/** True when every outpoint is present in the given unspent set. */
export function outpointsAreLive(outpoints: Outpoint[], utxos: WireUtxo[]): boolean {
  const live = new Set(utxos.map(utxoKey));
  return outpoints.every((outpoint) => live.has(utxoKey(outpoint)));
}
