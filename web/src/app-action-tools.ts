import { emptyAnnouncementScan, emptyScan, randomId } from "./app-helpers";
import type { AppActionContext } from "./app-action-context";
import type { ToastMessage } from "./app-model";
import type { MultisigDescriptor } from "./types";

export function showToast(
  ctx: AppActionContext,
  tone: ToastMessage["tone"],
  title: string,
  message: string,
  linkUrl?: string,
) {
  ctx.setToast({
    id: randomId(),
    tone,
    title,
    message,
    linkUrl,
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
    showToast(ctx, "error", `${label} failed`, message);
    ctx.setActivity(`${label} failed`);
    return undefined;
  }
}

export function clearVoteState(ctx: Pick<AppActionContext, "setFinalSpend" | "setVote">) {
  ctx.setVote(undefined);
  ctx.setFinalSpend(undefined);
}

export function clearProposalState(
  ctx: Pick<AppActionContext, "setFinalSpend" | "setProposal" | "setVote">,
) {
  ctx.setProposal(undefined);
  clearVoteState(ctx);
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
