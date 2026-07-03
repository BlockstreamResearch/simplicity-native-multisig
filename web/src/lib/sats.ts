export function isPositiveSats(value: number): boolean {
  return Number.isSafeInteger(value) && value > 0;
}

export function satsAmountError(label: string): string {
  return `${label} must be a whole positive satoshi amount.`;
}

export function assertPositiveSats(value: number, label: string) {
  if (!isPositiveSats(value)) {
    throw new Error(satsAmountError(label));
  }
}
