import { emptyAnnouncementScan, emptyScan, outputId } from "./app-helpers";
import type { AppActionContext } from "./app-action-context";
import type { ToastMessage } from "./app-model";
import type { MultisigDescriptor } from "./types";
import { clearProposalState } from "./app-state-reset";

export function showToast(
  ctx: AppActionContext,
  tone: ToastMessage["tone"],
  title: string,
  message: string,
) {
  ctx.setToast({
    id: outputId(),
    tone,
    title,
    message,
  });
}

export async function run<T>(
  ctx: AppActionContext,
  label: string,
  action: () => Promise<T>,
): Promise<T | undefined> {
  ctx.setActivity(label);
  ctx.setToast(undefined);
  try {
    const value = await action();
    ctx.setActivity("Ready");
    return value;
  } catch (nextError) {
    const message = nextError instanceof Error ? nextError.message : String(nextError);
    showToast(ctx, "error", label, message);
    ctx.setActivity("Needs attention");
    return undefined;
  }
}

export function applyLoadedDescriptor(ctx: AppActionContext, next: MultisigDescriptor) {
  const {
    setAnnouncementScan,
    setClaimed,
    setMultisigDescriptor,
    setParticipantKeys,
    setScan,
    setSession,
    setThreshold,
  } = ctx;

  setMultisigDescriptor(next);
  setSession(undefined);
  setThreshold(next.threshold);
  setParticipantKeys(next.participants.map((participant) => participant.xOnlyPublicKey));
  setScan(emptyScan);
  setAnnouncementScan(emptyAnnouncementScan);
  clearProposalState(ctx);
  setClaimed(undefined);
}
