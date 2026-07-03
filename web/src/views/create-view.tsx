import {
  Check,
  ExternalLink,
  FileSearch,
  KeyRound,
  Loader2,
  Megaphone,
  Radio,
  RefreshCcw,
  ShieldCheck,
} from "lucide-react";
import { amountFromInput } from "../app-helpers";
import { satsAmountError } from "../lib/sats";
import type { AppModel } from "../app-model";
import { CodeBlock, FlowSteps, Panel } from "../components";
import type { FlowStep } from "../components";
import { middle } from "../lib/format";

type CreateViewProps = {
  model: AppModel;
};

export function CreateView({ model }: CreateViewProps) {
  const {
    actionBusy,
    activeMultisigDescriptor,
    announcementMnemonic,
    announcementScan,
    announcementStake,
    announcementStakeValid,
    createDescriptor,
    fillDemo,
    info,
    isPublishingAnnouncement,
    participantKeys,
    publishAnnouncement,
    refreshAnnouncements,
    session,
    setAnnouncementMnemonic,
    setAnnouncementStake,
    setParticipantKeys,
    setThreshold,
    threshold,
  } = model;

  const announcedCount = announcementScan.announcements.length;
  const participantCount = activeMultisigDescriptor?.participants.length;
  const allAnnounced = participantCount !== undefined && announcedCount >= participantCount;
  const coordinationSteps: FlowStep[] = [
    {
      label: "Create or load descriptor",
      state: activeMultisigDescriptor ? "done" : "active",
    },
    {
      label: "Publish announcements",
      meta: participantCount !== undefined ? `${announcedCount}/${participantCount}` : undefined,
      state: allAnnounced ? "done" : activeMultisigDescriptor ? "active" : "todo",
    },
    {
      label: "Session ready",
      state: session ? "done" : allAnnounced ? "active" : "todo",
    },
  ];

  return (
    <section className="setup-grid">
      <div className="flow-bar wide">
        <FlowSteps steps={coordinationSteps} />
      </div>

      <Panel title="Create multisig" icon={<KeyRound size={16} />}>
        <label>
          Threshold
          <input
            type="number"
            min={1}
            max={3}
            value={threshold}
            onChange={(event) => setThreshold(Number(event.target.value))}
          />
        </label>
        {participantKeys.map((key, index) => (
          <div className="participant-input" key={`create-key-${index}`}>
            <label>
              Participant key {index + 1}
              <input
                value={key}
                onChange={(event) =>
                  setParticipantKeys((current) =>
                    current.map((item, currentIndex) =>
                      currentIndex === index ? event.target.value.trim() : item,
                    ),
                  )
                }
                placeholder="32-byte x-only pubkey"
              />
            </label>
          </div>
        ))}
        <div className="button-row">
          <button className="primary" onClick={createDescriptor} disabled={actionBusy}>
            Create multisig
          </button>
          <button onClick={fillDemo} disabled={actionBusy}>
            Demo keys
          </button>
        </div>
      </Panel>

      <Panel title="Multisig descriptor" icon={<FileSearch size={16} />}>
        {activeMultisigDescriptor ? (
          <>
            <div className="network-grid tight">
              <div>
                <span>Address</span>
                <strong>{middle(activeMultisigDescriptor.multisigAddress, 16)}</strong>
              </div>
              <div>
                <span>Announcements</span>
                <strong>
                  {announcementScan.announcements.length}/
                  {activeMultisigDescriptor.participants.length}
                </strong>
              </div>
            </div>
            <CodeBlock
              label="Shareable multisig descriptor"
              value={JSON.stringify(activeMultisigDescriptor, null, 2)}
            />
          </>
        ) : (
          <p className="empty-copy">Create or load a multisig descriptor first.</p>
        )}
      </Panel>

      <Panel title="Announce participant" icon={<Megaphone size={16} />}>
        <label>
          Mnemonic
          <textarea
            className="mnemonic"
            value={announcementMnemonic}
            disabled={actionBusy}
            onChange={(event) => setAnnouncementMnemonic(event.target.value)}
            rows={4}
            placeholder="Participant mnemonic"
          />
        </label>
        <label>
          Dust amount
          <input
            type="number"
            min={1}
            step={1}
            value={announcementStake}
            disabled={actionBusy}
            onChange={(event) => setAnnouncementStake(amountFromInput(event.target.value))}
          />
        </label>
        {!announcementStakeValid && <p className="empty-copy">{satsAmountError("Dust amount")}</p>}
        <button
          className="primary full"
          onClick={publishAnnouncement}
          disabled={
            !info ||
            !activeMultisigDescriptor ||
            !announcementMnemonic.trim() ||
            !announcementStakeValid ||
            actionBusy
          }
        >
          {isPublishingAnnouncement ? <Loader2 className="spin" size={15} /> : <Radio size={15} />}
          {isPublishingAnnouncement ? "Publishing" : "Publish announcement"}
        </button>
      </Panel>

      <Panel
        title="Recovered participants"
        icon={<ShieldCheck size={16} />}
        wide
        actions={
          <button
            onClick={() => refreshAnnouncements()}
            disabled={
              !info ||
              !activeMultisigDescriptor ||
              announcementScan.status === "scanning" ||
              actionBusy
            }
          >
            {announcementScan.status === "scanning" ? (
              <Loader2 className="spin" size={15} />
            ) : (
              <RefreshCcw size={15} />
            )}
            Scan
          </button>
        }
      >
        <p className="panel-note">{announcementScan.message}</p>
        <div className="announcement-list">
          {activeMultisigDescriptor?.participants.map((participant) => {
            const announcement = announcementScan.announcements.find(
              (item) => item.participantIndex === participant.index,
            );
            return (
              <div className="announcement-row" key={participant.index}>
                <div>
                  <span>Participant {participant.index + 1}</span>
                  <strong>{middle(participant.xOnlyPublicKey, 12)}</strong>
                </div>
                {announcement ? (
                  <>
                    <code>{middle(announcement.participantDescriptor, 28)}</code>
                    {announcement.explorerUrl && (
                      <a href={announcement.explorerUrl} target="_blank" rel="noreferrer">
                        <ExternalLink size={14} />
                      </a>
                    )}
                  </>
                ) : (
                  <span className="empty-copy">Waiting for announcement</span>
                )}
              </div>
            );
          })}
          {!activeMultisigDescriptor && <p className="empty-copy">No multisig descriptor loaded.</p>}
        </div>
        {session && (
          <div className="claim-box">
            <Check size={16} />
            <div>
              <strong>Full session ready</strong>
              <span>Participant descriptors were recovered from announcements.</span>
            </div>
          </div>
        )}
      </Panel>
    </section>
  );
}
