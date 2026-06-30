import { Copy } from "lucide-react";
import type { ReactNode } from "react";

export function Metric({ label, value }: { label: string; value: string }) {
  return (
    <div className="metric">
      <span>{label}</span>
      <strong>{value}</strong>
    </div>
  );
}

export function Panel({
  title,
  icon,
  children,
  wide = false,
}: {
  title: string;
  icon: ReactNode;
  children: ReactNode;
  wide?: boolean;
}) {
  return (
    <section className={`panel ${wide ? "wide" : ""}`}>
      <div className="panel-title">
        {icon}
        <h3>{title}</h3>
      </div>
      {children}
    </section>
  );
}

export function EmptyRow({ colSpan, label }: { colSpan: number; label: string }) {
  return (
    <tr>
      <td className="empty-row" colSpan={colSpan}>
        {label}
      </td>
    </tr>
  );
}

export function CodeBlock({ label, value }: { label: string; value: string }) {
  return (
    <div className="code-block">
      <div>
        <span>{label}</span>
        <button onClick={() => navigator.clipboard.writeText(value)}>
          <Copy size={14} />
          Copy
        </button>
      </div>
      <code>{value}</code>
    </div>
  );
}
