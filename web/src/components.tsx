import { Check, Copy } from "lucide-react";
import { useEffect, useRef, useState } from "react";
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
  actions,
  children,
  wide = false,
}: {
  title: string;
  icon: ReactNode;
  actions?: ReactNode;
  children: ReactNode;
  wide?: boolean;
}) {
  return (
    <section className={`panel ${wide ? "wide" : ""}`}>
      <div className="panel-title">
        <span className="panel-icon">{icon}</span>
        <h3>{title}</h3>
        {actions && <div className="panel-actions">{actions}</div>}
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
  const [copied, setCopied] = useState(false);
  const resetTimer = useRef<number>(undefined);

  useEffect(() => () => window.clearTimeout(resetTimer.current), []);

  return (
    <div className="code-block">
      <div>
        <span>{label}</span>
        <button
          className={copied ? "copied" : ""}
          onClick={() => {
            navigator.clipboard.writeText(value);
            setCopied(true);
            window.clearTimeout(resetTimer.current);
            resetTimer.current = window.setTimeout(() => setCopied(false), 1600);
          }}
        >
          {copied ? <Check size={14} /> : <Copy size={14} />}
          {copied ? "Copied" : "Copy"}
        </button>
      </div>
      <code>{value}</code>
    </div>
  );
}

export type FlowStepState = "done" | "active" | "todo";

export type FlowStep = {
  label: string;
  state: FlowStepState;
  meta?: string;
};

export function FlowSteps({ steps }: { steps: FlowStep[] }) {
  return (
    <ol className="flow-steps">
      {steps.map((step, index) => (
        <li key={step.label} className={step.state}>
          <span className="flow-dot">
            {step.state === "done" ? <Check size={12} /> : index + 1}
          </span>
          <span>{step.label}</span>
          {step.meta && <span className="flow-meta">{step.meta}</span>}
        </li>
      ))}
    </ol>
  );
}
