import type { FaucetAsset, FaucetResult, FaucetTarget, LiquidTestnetInfo } from "../types";

type FaucetApiResponse = {
  result?: string;
  result_test?: string;
  error?: string;
  txid?: string;
  balance?: number;
  balance_test?: number;
};

export async function requestFaucetFunds(
  info: LiquidTestnetInfo,
  target: FaucetTarget,
  address: string,
  asset: FaucetAsset,
): Promise<FaucetResult> {
  const normalizedAddress = address.trim();
  if (!normalizedAddress) {
    throw new Error("Faucet address is required");
  }

  const query = new URLSearchParams({ address: normalizedAddress, action: asset });
  const response = await fetch(`/liquidtestnet-api/faucet?${query.toString()}`, {
    headers: { accept: "application/json" },
    cache: "no-store",
  });
  const text = await response.text();

  if (!response.ok) {
    const plainText = text
      .replace(/<[^>]*>/g, " ")
      .replace(/\s+/g, " ")
      .trim();
    throw new Error(`Faucet rejected the request (${response.status}): ${plainText}`);
  }

  let data: FaucetApiResponse;
  try {
    data = JSON.parse(text) as FaucetApiResponse;
  } catch {
    throw new Error("Faucet did not return JSON. Check the local Vite proxy configuration.");
  }
  const message = asset === "test" ? data.result_test : data.result;
  const error =
    data.error ||
    (!message
      ? "missing faucet result"
      : ["error", "missing address"].includes(message.trim().toLowerCase())
        ? message
        : undefined);
  if (error) {
    throw new Error(`Faucet error: ${error}`);
  }

  return {
    target,
    asset,
    address: normalizedAddress,
    message:
      message ||
      (asset === "test" ? "TEST faucet request submitted" : "L-BTC faucet request submitted"),
    txid: data.txid,
    explorerUrl: data.txid ? `${info.explorerTxUrlPrefix}${data.txid}` : undefined,
    balance: data.balance,
    balanceTest: data.balance_test,
  };
}
