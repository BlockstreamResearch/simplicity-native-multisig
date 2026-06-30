export function middle(value: string, size = 8): string {
  if (value.length <= size * 2 + 3) {
    return value;
  }
  return `${value.slice(0, size)}...${value.slice(-size)}`;
}

export function sats(value: number | bigint): string {
  const numberValue = typeof value === "bigint" ? Number(value) : value;
  return `${new Intl.NumberFormat("en-US").format(numberValue)} sats`;
}
