/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceSignedTraffic
import Vegas.Game.RevealServiceRosterEvidence

/-! # A send-time rule for revelation rosters

One fresh certified opening per phase is admitted. The envelope serial is
checked against its author's entries in the prior ledger. Each fresh opening
allocates a new serial. No audit verdict
uses this rule: it is a proof device, and on a ledger without repeated
identifiers its breach breaches the service rule
(`Vegas.permittedRosterEnvelope_of_permittedService`), which dooms the author at
settlement.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

open Classical in
/-- The rule reads the phase, preceding ledger and signed envelope without
inspecting any player's private state. -/
def permittedRosterEnvelope (evidence : EnvelopeEvidence setup leaks) : Bool :=
  decide (evidence.2.2.id ∈ evidence.2.1.map Message.id ∨
    (evidence.2.2.id.2 =
      evidence.2.1.countP (fun message => message.sender = evidence.2.2.sender) ∧
    openingTraffic setup leaks ⟨evidence.1, evidence.2.1, evidence.2.2⟩))

theorem permittedRosterEnvelope_iff (record : (application setup leaks).TrafficRecord)
    (_authored : record.envelope.sender = record.envelope.sender) :
    permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = true ↔
      record.envelope.id ∈ record.ledger.map Message.id ∨
        (record.envelope.id.2 =
          record.ledger.countP (fun message => message.sender = record.envelope.sender) ∧
          openingTraffic setup leaks record) := by
  classical
  simp only [permittedRosterEnvelope, envelopeEvidence, decide_eq_true_eq]

/-- At a completed source prefix all allocated fresh envelopes have been
included once, so the next per-author serial is the public count. -/
theorem PublicCheckpoint.serial_eq_ledger_count
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : Vegas.ContextRefs (graph setup).layout Γ}
    {rank : Nat} {execution : (application setup leaks).Execution}
    (checkpoint : PublicCheckpoint setup leaks initial source refs rank execution)
    (who : Player) :
    execution.network.nextSerial who =
      execution.network.ledger.countP (fun message => message.sender = who) := by
  rw [checkpoint.counters, checkpoint.ledger]
  exact publicationSerial_eq_ledger_count _ _ who

/-- In a reveal-only graph, on a ledger without repeated identifiers, the
roster rule is no stricter than the service rule. A breach of the roster rule
therefore breaches the service rule. -/
theorem permittedRosterEnvelope_of_permittedService (reveals : setup.program.RevealOnly)
    (view : (application setup leaks).PublicObservation)
    (ledger : List (Message Player (application setup leaks).Payload))
    (message : Message Player (application setup leaks).Payload)
    (nodup : (ledger.map Message.id).Nodup)
    (allowed : (runtime setup).permittedServiceEnvelope view ledger message = true) :
    permittedRosterEnvelope setup leaks (view, ledger, message) = true := by
  classical
  rw [(runtime setup).permittedServiceEnvelope_iff] at allowed
  unfold permittedRosterEnvelope
  apply decide_eq_true
  rcases allowed with published | ⟨serial, fresh⟩
  · exact Or.inl published
  · refine Or.inr ⟨?_, openingTraffic_of_fresh setup leaks reveals view ledger message fresh⟩
    rw [serial, Message.distinctAuthoredCount_eq_countP ledger message.sender nodup]

variable [Fintype Player]

/-- Silence belongs to the roster menu. Every additional effective response
therefore allocates a fresh envelope. -/
theorem roster_extra_submission (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who past view)
    (excluded : response ∉ (rosterMenu setup leaks bounds rosters).actions who past view) :
    ∃ submission, response = ⟨some submission⟩ := by
  classical
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact (excluded (silence_roster setup leaks bounds rosters who past view)).elim
  | some submission => exact ⟨submission, rfl⟩

/-- On every legal retained owner history, the public serial test is exactly
the private recall test for whether the phase still permits a fresh opening. -/
theorem roster_fresh_iff_serial [setup.FiniteInitialLaw] (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (readyNow : control.execution.application.config.cut.Ready event)
    (ownedEvent : (graph setup).actor? event = some who)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (openingNow : rosterOpening? setup leaks who event
      (control.execution.observe (application setup leaks) who) = some (candidate, raw)) :
    rosterFresh? setup leaks rosters who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) =
        some ((runtime setup).windowOpening leaks event candidate raw) ↔
      control.execution.network.nextSerial who =
        control.execution.network.ledger.countP (fun message => message.sender = who) := by
  classical
  let menu := rosterMenu setup leaks bounds rosters
  let profile : BehavioralProfile setup.program :=
    fun owner => RevealOnly.uniformPolicy owner setup.program reveals
  obtain ⟨phase, slot, phaseStart, prior, sample, initial, state, selected, initialSupport,
      related, _, startReady, offset, serials, published, reached, activated,
      unchanged, _⟩ :=
    roster_decision_phase setup leaks bounds rosters network reveals openable
      who control trace active
  have samePhase : phase = event := by
    have now : phaseStart.application.publicView.EventReady event := by
      rw [← unchanged]
      exact (control.execution.application.publicView_eventReady event).mpr readyNow
    exact ((soleReady_of_ready setup phaseStart.application startReady).2 event now).symm
  subst phase
  have data := owner_choices_at_prefix setup leaks bounds profile who initial initialSupport
    setup.program reveals profile
    (Vegas.ContextRefs.initial setup.context (Vegas.outputLayout setup.program))
    (Revelations.initial setup.context) (Vegas.outputEmbedding setup.program)
    (Vegas.initialRefsBefore setup.program) 0
    (Vegas.CompiledPolicySuffix.whole setup.program profile)
    event.val event.isLt state phaseStart related event (by omega) ownedEvent startReady
  obtain ⟨expected, expectedRaw, priorOpening, owned, valid, _, _⟩ := data.2.2
  have same := rosterOpening?_application_eq setup leaks who event control.execution phaseStart
    unchanged
  rw [openingNow, priorOpening] at same
  cases Option.some.inj same
  have covered : ∀ player past view response,
      response ∈ (menu.uniformResponses player past view).support →
        response ∈ rosterActions setup leaks bounds rosters player past view := by
    intro player past view response supported
    exact (menu.uniformResponses_support player past view response).mp supported
  obtain ⟨chosen, frame, earlier, recorded, _⟩ := roster_window_posterior setup leaks bounds rosters
    phaseStart event who (soleReady_of_ready setup phaseStart.application startReady)
      ownedEvent candidate
    raw priorOpening owned valid (offset who) serials
    published menu.uniformResponses covered network ((rosters event).take slot)
    (roster_count_before selected).le prior reached
  obtain ⟨context, source, refs, checkpoint⟩ := related.checkpoint setup.program
    (Vegas.ContextRefs.initial setup.context (Vegas.outputLayout setup.program))
    (Revelations.initial setup.context) (Vegas.outputRef setup.program) 0 event.val state
    phaseStart
  have baseline := checkpoint.serial_eq_ledger_count setup leaks who
  have counter := congrFun frame.counters who
  have zero_iff : prior.network.nextSerial who =
      prior.network.ledger.countP (fun message => message.sender = who) ↔ chosen = none := by
    rw [frame.ledger, counter, baseline]
    cases chosen with
    | none => simp only [openingPassed, Option.any_none, Bool.false_eq_true, and_false,
        ↓reduceIte, Nat.add_zero]
    | some index =>
        have passed := earlier index rfl
        simp [openingPassed, passed]
  rw [activated]
  change rosterFresh? setup leaks rosters who (prior.recall who)
      ((prior.sampledActivation (application setup leaks) who sample).observe
        (application setup leaks) who) =
      some ((runtime setup).windowOpening leaks event candidate raw) ↔
    prior.network.nextSerial who =
      prior.network.ledger.countP (fun message => message.sender = who)
  rw [zero_iff]
  refine ⟨?_, ?_⟩
  · intro fresh
    obtain ⟨otherEvent, _, _, otherTurn, _, _, _, absent⟩ :=
      rosterFresh?_shape setup leaks rosters who _ _ _ fresh
    change prior.application.publicView.ownTurn? who = some otherEvent at otherTurn
    rw [frame.application, ownTurn?_of_ready setup phaseStart.application startReady ownedEvent]
      at otherTurn
    cases Option.some.inj otherTurn
    cases chosen with
    | none => rfl
    | some index =>
        obtain ⟨entry, member, emitted⟩ := recorded.mp rfl
        exact (absent entry member emitted).elim
  · intro unopened
    have absent : ¬ ∃ entry ∈ (prior.recall who).drop (rosterOffset setup rosters who event),
        entry.action = (runtime setup).windowOpening leaks event candidate raw := by
      intro present
      have seen := recorded.mpr present
      rw [unopened] at seen
      cases seen
    have currentTurn : ((prior.sampledActivation (application setup leaks) who sample).observe
        (application setup leaks) who).application.publicView.ownTurn? who = some event := by
      change prior.application.publicView.ownTurn? who = some event
      rw [frame.application]
      exact ownTurn?_of_ready setup phaseStart.application startReady ownedEvent
    have currentOpening : rosterOpening? setup leaks who event
        ((prior.sampledActivation (application setup leaks) who sample).observe
          (application setup leaks) who) = some (candidate, raw) := by
      rw [rosterOpening?_application_eq setup leaks who event
        (prior.sampledActivation (application setup leaks) who sample) phaseStart frame.application]
      exact priorOpening
    unfold rosterFresh?
    apply Option.bind_eq_some_iff.mpr
    refine ⟨event, currentTurn, ?_⟩
    rw [ite_eq_right (not_not_intro ownedEvent)]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨(candidate, raw), currentOpening, ?_⟩
    dsimp only [bind, Option.bind]
    simp only [List.any_eq_true, decide_eq_true_eq]
    exact ite_eq_right absent

end Vegas
