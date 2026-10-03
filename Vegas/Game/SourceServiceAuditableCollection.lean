/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceNoncanonicalBinding
import Vegas.Game.SourceServiceGuardFailure
import Vegas.Game.SourceServiceSignedCollection
import Vegas.Game.SourceServiceAuthorizationBreach
import Vegas.Game.SourceServiceNodeKindBreach
import Interaction.ReactiveLocalContinuation
import Interaction.ReactiveSubmissionSerial
import Vegas.Pending.EvidenceNormalization
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Information-local auditable responses and actual collection

Own recall and the current view reconstruct the next signed envelope. The
charged classes are constructor-level breaches, invalid readiness tokens,
packets addressed to another actor's event or the wrong event constructor, a
commitment to the current owned event with a noncanonical handle, and an
opening of that event whose public guard check fails. The guard check reads
the public store and signed opened value, so no private oracle is needed.

Committing a classified response produces actual traffic. That traffic
persists, and complete play supplies its final forbidden verdict under every
later policy. Authentic final-record observation and conditional report
delivery coverage bound the actual one-time collection probability. Private
binding material and guard-passing certificate capability are not classified.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Constructor, authorization and node-kind breaches need no opportunity.
Handle and guard failures refer to the owner's ready event and public metadata. -/
def AuditableServicePacket (view : PublicView (graph setup)) (who : Player)
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  SignedContentBreach message ∨ ServiceAuthorizationBreach message ∨
    ServiceNodeKindBreach message ∨
    ∃ event, view.ownTurn? who = some event ∧
      ((∃ candidate, message.payload.call = .commitment event candidate ∧
          candidate ≠ (who, .prepared (view.bindingCount who))) ∨
        ∃ candidate raw, message.payload.call = .opening event candidate raw ∧
          view.openingGuardsAccepted message.payload = false)

/-- Compute the actual next envelope using only the player's own recall,
observed candidate meanings, known packets and public readiness tokens. -/
def localServiceEnvelope (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (material : (application setup leaks).Submission) :
    Message Player (WitnessedPacket (graph setup)) :=
  ⟨(who, (application setup leaks).submissionCount past),
    ⟨material.call.packet,
      material.evidence.resolve who (material.call.candidateAfter who view.application.candidates)
        (ReactiveApplication.ResponseMenu.knownPackets past view),
      view.application.publicView.tokenFor material.call.packet⟩⟩

/-- A predicate on the real local response input, with no quantification over
hidden executions. Silence is not classified as signed evidence. -/
def auditableServiceResponse (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action) :
    Prop :=
  ∃ material, response.transmission = some material ∧
    AuditableServicePacket setup view.application.publicView who
      (localServiceEnvelope setup leaks who past view material)

/-- Legal own recall and observation reconstruct the entire actual envelope.
This uses neither a prescribed source policy nor a hidden intention table. -/
theorem localServiceEnvelope_actual
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) (who : Player) (material : (application setup leaks).Submission) :
    localServiceEnvelope setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) material =
      (⟨(who, control.execution.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit control.execution.application who material) who
          (control.execution.network.known who) material⟩ :
            Message Player (WitnessedPacket (graph setup))) := by
  let app := application setup leaks
  have input : control.execution.InputRecall app :=
    app.history_inputRecall (initialLaw setup) horizon scheduler trace
  have serial : control.execution.SerialRecall app :=
    app.serialRecall_history scheduler (initialLaw setup) horizon trace
  have known : ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
      (control.execution.observe app who) = control.execution.network.known who :=
    (app.known_from_recall control.execution who input).symm
  unfold localServiceEnvelope
  rw [← serial who, known]
  apply congrArg (Message.mk (who, control.execution.network.nextSerial who))
  change WitnessedPacket.mk _ _ _ = material.emit
    (app.submit control.execution.application who material) who
      (control.execution.network.known who)
  rw [WitnessedSubmission.emit_eq_resolve,
    (runtime setup).reactiveApplication_submit_publicView leaks]
  have candidates : (fun slot => (app.submit control.execution.application who
      material).candidates.lookup (who, slot)) =
      material.call.candidateAfter who
        (control.execution.observe app who).application.candidates := by
    funext slot
    exact material.call.candidateAfter_eq who control.execution.application slot
  rw [candidates]
  rfl

variable [Fintype Player]

/-- The classifier applies directly to one information state and available
choice. Both its response and all data used to classify it are owner-local. -/
def auditableServiceChoice (menu : (application setup leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler) (who : Player)
    (info : (menu.information (initialLaw setup) horizon scheduler).InfoState who)
    (choice : (menu.information (initialLaw setup) horizon scheduler).Choice who info) : Prop :=
  ∃ past view response, info = some (past, view) ∧ choice.1 = some response ∧
    auditableServiceResponse setup leaks who past view response

omit [Fintype Player] in
/-- Every classified actual packet is forbidden at every reachable complete
record. Receipt soundness checks authorization of the actual emitted packet;
the other classes use constructor, ordinal and public guard checks. -/
theorem auditableServicePacket_forbidden_reaches
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {first last :
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).History}
    {fuel : Nat}
    (path : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (application setup leaks).Control)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (who : Player) (message : Message Player (WitnessedPacket (graph setup)))
    (authored : message.sender = who)
    (classified : AuditableServicePacket setup before.execution.application.publicView who message)
    (emitted : Emitted setup leaks after.execution message)
    (complete : after.execution.application.config.cut.Terminal) :
    ((runtime setup).settledRecord leaks after.execution).permits message = false := by
  rcases classified with signed | unauthorized | wrongKind |
      ⟨event, turn, noncanonical | guarded⟩
  · exact signed.forbidden (runtime setup) leaks after.execution complete
  · exact unauthorized.forbidden_history (lastState ▸ last.trace) emitted complete
  · exact wrongKind.forbidden_history (lastState ▸ last.trace) emitted complete
  · obtain ⟨candidate, committed, different⟩ := noncanonical
    have ready := (before.execution.application.publicView_eventReady event).mp
      ((before.execution.application.publicView.ownTurn?_spec who event turn).1)
    apply (noncanonicalCommitment_forbidden_reaches path before after firstState lastState
      event ready message candidate committed ?_ complete).2
    simpa only [authored] using different
  · obtain ⟨candidate, raw, opened, rejected⟩ := guarded
    have ready := (before.execution.application.publicView_eventReady event).mp
      ((before.execution.application.publicView.ownTurn?_spec who event turn).1)
    exact (guardFailingOpening_forbidden_reaches path before after firstState lastState
      event ready message candidate raw opened rejected complete).2

open Classical in
/-- Committing an information-local classified choice creates actual signed
traffic and gives the final-record backend's collection bound under arbitrary
later policies. No hidden-history uniformity, packet-verdict or fuel premise
is supplied by the caller. -/
theorem auditableServiceChoice_collection_committed
    (menu : (application setup leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (backend : EvidenceReportService (SettledEvidence setup))
    (profile : ∀ player,
      (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : (menu.information (initialLaw setup) horizon scheduler).InfoState who)
    (choice : (menu.information (initialLaw setup) horizon scheduler).Choice who info)
    (observed : (menu.information (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info)
    (classified : auditableServiceChoice setup leaks menu horizon scheduler who info choice)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
        (Profile.update
          (sig := (menu.information (initialLaw setup) horizon scheduler).behavioralSignature)
          profile who ((profile who).commit info choice)) history)
        (fun final => TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks backend.sample) final.state who) := by
  classical
  let app := application setup leaks
  obtain ⟨past, view, response, inputEq, chosen, material, sent, auditable⟩ := classified
  have observedInput : info = app.observe who history.state :=
    observed.symm.trans (menu.info (initialLaw setup) horizon scheduler who history.trace)
  rw [current] at observedInput
  simp only [ReactiveApplication.observe, ↓reduceIte] at observedInput
  have same := Option.some.inj (inputEq.symm.trans observedInput)
  have pastEq := congrArg Prod.fst same
  have viewEq := congrArg Prod.snd same
  dsimp only at pastEq viewEq
  rw [pastEq, viewEq] at auditable
  have responseEq : response = ⟨some material⟩ := by
    cases response with
    | mk transmission =>
        change transmission = some material at sent
        cases sent
        rfl
  have selected : choice.1 = some ⟨some material⟩ :=
    chosen.trans (congrArg some responseEq)
  have rawTrace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    current ▸ menu.toRawTrace (initialLaw setup) horizon scheduler history.trace
  rw [localServiceEnvelope_actual setup leaks rawTrace who material] at auditable
  apply settledPacket_collection_committed setup leaks menu horizon scheduler completes backend
    profile history who remaining execution current info choice observed material selected ?_
    observationRate deliveryRate delivery_nonnegative coverage
  intro fuel final path control finalState complete emitted
  exact auditableServicePacket_forbidden_reaches setup leaks path
    ⟨remaining, some who, execution⟩ control current finalState who _ rfl auditable emitted complete

end Vegas
