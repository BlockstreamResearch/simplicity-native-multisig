import type * as Lwk from "lwk_wasm";
import type {
  LiquidTestnetInfo,
  MultisigDescriptor,
  ScanTransaction,
  WireUtxo,
} from "../../types";

const waterfallsServerRecipient =
  "age1xxzrgrfjm3yrwh3u6a7exgrldked0pdauvr3mx870wl6xzrwm5ps8s2h0p";

type EsploraStatus = {
  confirmed?: boolean;
  block_height?: number;
  block_time?: number;
};

type EsploraUtxo = {
  txid: string;
  vout: number;
  value?: number;
  asset?: string;
  status?: EsploraStatus;
};

type EsploraTransaction = {
  txid: string;
  status?: EsploraStatus;
  vout?: EsploraOutput[];
};

type EsploraOutput = {
  scriptpubkey_address?: string;
};

function esploraBaseUrl(info: LiquidTestnetInfo): string {
  return info.defaultEsploraUrl.replace(/\/$/, "");
}

export async function scanDescriptor(
  lwk: typeof Lwk,
  network: Lwk.Network,
  client: Lwk.EsploraClient,
  descriptor: string,
  info: LiquidTestnetInfo,
  scanToIndex?: number,
): Promise<{
  wallet: Lwk.Wollet;
  utxos: WireUtxo[];
  transactions: ScanTransaction[];
}> {
  const wallet = new lwk.Wollet(network, new lwk.WolletDescriptor(descriptor));
  let update: Lwk.Update | undefined;
  let scanned = false;
  let lastScanError: unknown;
  for (let attempt = 0; attempt < 4; attempt += 1) {
    try {
      const scan =
        scanToIndex === undefined
          ? client.fullScan(wallet)
          : client.fullScanToIndex(wallet, scanToIndex);
      update = await new Promise<Lwk.Update | undefined>((resolve, reject) => {
        const timer = window.setTimeout(
          () => reject(new Error("LWK scan timed out")),
          45_000,
        );
        scan.then(
          (value) => {
            window.clearTimeout(timer);
            resolve(value);
          },
          (error: unknown) => {
            window.clearTimeout(timer);
            reject(error);
          },
        );
      });
      scanned = true;
      break;
    } catch (error) {
      lastScanError = error;
      const message = error instanceof Error ? error.message : String(error);
      const transient =
        message.includes("HTTP 404") ||
        message.includes("Block not found") ||
        message.includes("Failed to fetch");
      if (!transient || attempt === 3) {
        throw error;
      }
      await new Promise((resolve) => window.setTimeout(resolve, 1_500 * (attempt + 1)));
    }
  }
  if (!scanned) {
    throw lastScanError;
  }

  if (update) {
    wallet.applyUpdate(update);
  }

  return {
    wallet,
    utxos: wallet.utxos().flatMap((output) => {
      try {
        const outpoint = output.outpoint();
        const secrets = output.unblinded();
        return [
          {
            txid: outpoint.txid().toString(),
            vout: outpoint.vout(),
            scriptPubkey: output.scriptPubkey().toString(),
            asset: secrets.asset().toString(),
            value: Number(secrets.value()),
          },
        ];
      } catch {
        return [];
      }
    }),
    transactions: wallet.transactions().map((tx) => ({
      txid: tx.txid().toString(),
      type: tx.txType(),
      height: tx.height(),
      timestamp: tx.timestamp(),
      sources: [],
      explorerUrl: `${info.explorerTxUrlPrefix}${tx.txid().toString()}`,
    })),
  };
}

export async function scanMultisigAddress(
  descriptor: MultisigDescriptor,
  info: LiquidTestnetInfo,
): Promise<{
  utxos: WireUtxo[];
  transactions: ScanTransaction[];
  oldestUtxoHeight?: number;
}> {
  const addressPath = encodeURIComponent(descriptor.multisigAddress);
  const [utxos, transactions] = await Promise.all([
    esploraJson<EsploraUtxo[]>(info, `/address/${addressPath}/utxo`),
    esploraJson<EsploraTransaction[]>(info, `/address/${addressPath}/txs`),
  ]);
  const confirmedHeights = utxos.flatMap((utxo) =>
    utxo.status?.confirmed && utxo.status.block_height !== undefined
      ? [utxo.status.block_height]
      : [],
  );

  return {
    oldestUtxoHeight: confirmedHeights.length > 0 ? Math.min(...confirmedHeights) : undefined,
    utxos: utxos.flatMap((utxo) =>
      utxo.asset === undefined || utxo.value === undefined
        ? []
        : [
            {
              txid: utxo.txid,
              vout: utxo.vout,
              scriptPubkey: descriptor.multisigScriptPubkey,
              asset: utxo.asset,
              value: utxo.value,
            },
          ],
    ),
    transactions: transactions.map((tx) => {
      const receivesToMultisig = tx.vout?.some(
        (output) => output.scriptpubkey_address === descriptor.multisigAddress,
      );
      return {
        txid: tx.txid,
        type: receivesToMultisig ? "received" : "spent",
        height: tx.status?.confirmed ? tx.status.block_height : undefined,
        timestamp: tx.status?.confirmed ? tx.status.block_time : undefined,
        sources: ["Multisig"],
        explorerUrl: `${info.explorerTxUrlPrefix}${tx.txid}`,
      };
    }),
  };
}

export async function esploraJson<T>(info: LiquidTestnetInfo, path: string): Promise<T> {
  const response = await fetch(`${esploraBaseUrl(info)}${path}`);
  if (!response.ok) {
    throw new Error(`Esplora request failed with HTTP ${response.status}`);
  }
  return (await response.json()) as T;
}

export async function esploraTxHex(info: LiquidTestnetInfo, txid: string): Promise<string> {
  const response = await fetch(`${esploraBaseUrl(info)}/tx/${txid}/hex`);
  if (!response.ok) {
    throw new Error(`Esplora request failed with HTTP ${response.status}`);
  }
  return response.text();
}

export async function esploraFeeRateSatsPerVbyte(info: LiquidTestnetInfo): Promise<number> {
  const estimates = await esploraJson<Record<string, number>>(info, "/fee-estimates");
  const estimate = estimates["1"] ?? estimates["2"] ?? estimates["3"] ?? estimates["6"];
  if (!Number.isFinite(estimate) || estimate <= 0) {
    throw new Error("Esplora fee estimates did not include a usable fee rate");
  }
  return estimate;
}

export function esploraClient(
  lwk: typeof Lwk,
  network: Lwk.Network,
  info: LiquidTestnetInfo,
): Lwk.EsploraClient {
  return new lwk.EsploraClient(network, info.defaultEsploraUrl, false, 4, false);
}

export async function waterfallsClient(
  lwk: typeof Lwk,
  network: Lwk.Network,
  info: LiquidTestnetInfo,
): Promise<Lwk.EsploraClient> {
  const client = new lwk.EsploraClient(network, info.defaultWaterfallsUrl, true, 4, false);
  await client.setWaterfallsServerRecipient(waterfallsServerRecipient);
  return client;
}

type WaterfallsTxSeen = {
  txid: string;
  height?: number;
};

/**
 * Full script-level transaction history of a descriptor from the waterfalls
 * service. Unlike an LWK wallet scan this needs no blinding key and also
 * reports transactions whose wallet-facing outputs are all confidential.
 */
export async function waterfallsScriptHistory(
  info: LiquidTestnetInfo,
  descriptor: string,
): Promise<WaterfallsTxSeen[]> {
  const base = info.defaultWaterfallsUrl.replace(/\/$/, "");
  const response = await fetch(
    `${base}/v1/waterfalls?descriptor=${encodeURIComponent(descriptor)}`,
  );
  if (!response.ok) {
    throw new Error(`Waterfalls request failed with HTTP ${response.status}`);
  }
  const data = (await response.json()) as {
    txs_seen: Record<string, WaterfallsTxSeen[][]>;
  };
  return Object.values(data.txs_seen).flat(2);
}
