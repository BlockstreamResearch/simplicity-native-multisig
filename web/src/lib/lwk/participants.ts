import { deriveParticipantKey } from "../contracts";
import type { ClaimedParticipant, MultisigSession } from "../../types";
import { loadLwk } from "./core";

export async function claimParticipant(
  session: MultisigSession,
  mnemonic: string,
): Promise<ClaimedParticipant> {
  const trimmed = mnemonic.trim();
  for (const participant of session.participants) {
    const derived = await deriveParticipantKey(trimmed, participant.index);
    if (derived.xOnlyPublicKey === participant.xOnlyPublicKey) {
      const lwk = await loadLwk();
      const network = lwk.Network.testnet();
      const signer = new lwk.Signer(new lwk.Mnemonic(trimmed), network);
      const descriptor = signer.wpkhSlip77Descriptor();
      const wallet = new lwk.Wollet(network, descriptor);
      return {
        participantIndex: participant.index,
        xOnlyPublicKey: derived.xOnlyPublicKey,
        derivationPath: derived.derivationPath,
        mnemonic: trimmed,
        voteDescriptor: descriptor.toString(),
        fundingAddress: wallet.address(0).address().toString(),
      };
    }
  }

  throw new Error("Mnemonic does not match any participant key in this descriptor");
}
