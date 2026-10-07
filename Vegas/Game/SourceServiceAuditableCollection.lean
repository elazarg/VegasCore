/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceNoncanonicalBinding
import Vegas.Game.SourceServiceGuardFailure
import Vegas.Game.SourceServiceSignedCollection
import Vegas.Game.SourceServiceConformantResponse
import Interaction.ReactiveLocalContinuation
import Interaction.ReactiveSubmissionSerial
import Vegas.Pending.EvidenceNormalization
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Information-local auditable responses and actual collection

Own recall and the current view reconstruct the next signed envelope. The
charged classes are constructor-level breaches, a commitment to the current
owned event with a noncanonical handle, and an opening of that event whose
public guard check fails. The guard check reads the public store and signed
opened value, so this classification needs no private configuration oracle.

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
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Constructor breaches need no opportunity. The two additional classes
refer to the owner's currently ready event and public application metadata. -/
def AuditableServicePacket (view : PublicView (serviceGraph setup mode)) (who : Player)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  SignedContentBreach message ∨
    ∃ event, view.ownTurn? who = some event ∧
      ((∃ candidate, message.payload.call = .commitment event candidate ∧
          candidate ≠ (who, .prepared (view.bindingCount who))) ∨
        ∃ candidate raw, message.payload.call = .opening event candidate raw ∧
          view.openingGuardsAccepted message.payload = false)

/-- A predicate on the real local response input, with no quantification over
hidden executions. Silence is not classified as signed evidence. -/
def auditableServiceResponse (who : Player)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView) (response :
      (serviceApplication setup mode deadline leaks).Action) :
    Prop :=
  ∃ material, response.transmission = some material ∧
    AuditableServicePacket setup view.application.publicView who
      ((serviceRuntime setup mode deadline).localEnvelope leaks who past view material)

variable [Fintype Player]

/-- The classifier applies directly to one information state and available
choice. Both its response and all data used to classify it are owner-local. -/
def auditableServiceChoice (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) (who :
      Player)
    (info : (menu.information (serviceInitialLaw setup mode) horizon scheduler).InfoState who)
    (choice : (menu.information (serviceInitialLaw setup mode) horizon scheduler).Choice who
      info) : Prop :=
  ∃ past view response, info = some (past, view) ∧ choice.1 = some response ∧
    auditableServiceResponse setup leaks who past view response

omit [Fintype Player] in
/-- Every classified actual packet is forbidden at every reachable complete
record. The current-opportunity classes use the checked ordinal and public
guard persistence results; constructor breaches need no readiness premise. -/
theorem auditableServicePacket_forbidden_reaches
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {first last :
      ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).History}
    {fuel : Nat}
    (path : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (serviceApplication setup mode deadline leaks).Control)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (who : Player) (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (authored : message.sender = who)
    (classified : AuditableServicePacket setup before.execution.application.publicView who message)
    (complete : after.execution.application.config.cut.Terminal) :
    ((serviceRuntime setup mode deadline).settledRecord leaks after.execution).permits message =
      false := by
  rcases classified with signed | ⟨event, turn, noncanonical | guarded⟩
  · exact signed.forbidden (serviceRuntime setup mode deadline) leaks after.execution complete
  · obtain ⟨candidate, committed, different⟩ := noncanonical
    have ready := (before.execution.application.publicView_eventReady event).mp
      ((before.execution.application.publicView.ownTurn?_spec who event turn).1)
    have owned : (serviceGraph setup mode).actor? event = some message.sender := by
      rw [authored]
      exact (before.execution.application.publicView.ownTurn?_spec who event turn).2
    apply (noncanonicalCommitment_forbidden_reaches path before after firstState lastState
      event ready message owned candidate committed ?_ complete).2
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
    (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (completes : CompletesPlay (serviceRuntime setup mode deadline) leaks (serviceInitialLaw setup
      mode) horizon scheduler)
    (backend : EvidenceReportService (SettledEvidence setup mode))
    (profile : ∀ player,
      (menu.information (serviceInitialLaw setup mode) horizon scheduler).BehavioralPolicy player)
    (history : (menu.protocol (serviceInitialLaw setup mode) horizon scheduler).History)
    (who : Player) (remaining : Nat) (execution : (serviceApplication setup mode deadline
      leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : (menu.information (serviceInitialLaw setup mode) horizon scheduler).InfoState who)
    (choice : (menu.information (serviceInitialLaw setup mode) horizon scheduler).Choice who info)
    (observed : (menu.information (serviceInitialLaw setup mode) horizon scheduler).infoOf who
      history.trace = info)
    (classified : auditableServiceChoice setup leaks menu horizon scheduler who info choice)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information (serviceInitialLaw setup mode) horizon
        scheduler).runBehavioralTerminalFrom
        (menu.bounded (serviceInitialLaw setup mode) horizon scheduler).wellFoundedHistories
        (Profile.update
          (sig := (menu.information (serviceInitialLaw setup mode) horizon
            scheduler).behavioralSignature)
          profile who ((profile who).commit info choice)) history)
        (fun final => TerminalAudit.charge ((serviceRuntime setup mode
          deadline).serviceAuditObservation leaks)
          (serviceSourceAudit setup mode deadline leaks backend.sample) final.state who) := by
  classical
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨past, view, response, inputEq, chosen, material, sent, auditable⟩ := classified
  have observedInput : info = app.observe who history.state :=
    observed.symm.trans (menu.info (serviceInitialLaw setup mode) horizon scheduler who
      history.trace)
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
  have rawTrace : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    current ▸ menu.toRawTrace (serviceInitialLaw setup mode) horizon scheduler history.trace
  rw [localEnvelope_actual rawTrace who material] at auditable
  apply forbiddenTraffic_collection_committed setup leaks menu horizon scheduler completes backend
    profile history who remaining execution current info choice observed material selected ?_
    observationRate deliveryRate delivery_nonnegative coverage
  intro fuel next final nextState path control finalState complete
  have present : (⟨execution.application.publicView, execution.network.ledger,
      ⟨(who, execution.network.nextSerial who), app.packet
        (app.submit execution.application who material) who
          (execution.network.known who) material⟩⟩ : app.TrafficRecord) ∈
      app.stateTraffic next.state := by
    rw [nextState]
    exact (serviceRuntime setup mode deadline).signed_response_traffic leaks execution who
      material rawTrace
  have kept := (app.stateTraffic_reaches (serviceInitialLaw setup mode) horizon scheduler
    path).subset present
  rw [finalState] at kept
  refine ⟨_, kept, rfl, ?_⟩
  have classified : AuditableServicePacket setup
      (execution.respond app who ⟨some material⟩).application.publicView who
      ⟨(who, execution.network.nextSerial who), app.packet
        (app.submit execution.application who material) who
          (execution.network.known who) material⟩ := by
    rw [((serviceRuntime setup mode deadline).reactive_respond_application leaks execution who
      ⟨some material⟩).2]
    exact auditable
  exact auditableServicePacket_forbidden_reaches setup leaks path
    ⟨remaining, none, execution.respond app who ⟨some material⟩⟩ control nextState finalState
    who _ rfl classified complete

end Vegas
