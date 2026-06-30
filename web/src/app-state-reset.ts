import type { AppActionContext } from "./app-action-context";

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
