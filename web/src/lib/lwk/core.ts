import type * as Lwk from "lwk_wasm";

let lwkPromise: Promise<typeof Lwk> | undefined;

export const walletScanIndex = 1;

export async function loadLwk(): Promise<typeof Lwk> {
  lwkPromise ??= import("lwk_wasm");
  return lwkPromise;
}
