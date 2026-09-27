/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceSignedTraffic
import Vegas.Game.RevealServiceRosterEvidence

/-! # Single-record audit evidence for revelation rosters

One fresh certified opening per phase is admitted. The envelope serial is
checked against its author's entries in the authenticated prior ledger. A
second fresh opening changes the serial; replaying an existing envelope does
not. No missing audit record is treated as evidence of an omitted action.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

open Classical in
/-- The checker authenticates the phase, preceding ledger and signed envelope.
It does not identify the rebroadcaster or inspect any player's private state. -/
def permittedRosterEnvelope (evidence : EnvelopeEvidence setup leaks) : Bool :=
  decide (evidence.2.2.id ∈ evidence.2.1.map Message.id ∨
    (evidence.2.2.id.2 =
      evidence.2.1.countP (fun message => message.sender = evidence.2.2.sender) ∧
    openingTraffic setup leaks ⟨evidence.1, evidence.2.1,
      ⟨evidence.2.2.sender, evidence.2.2⟩⟩))

theorem permittedRosterEnvelope_iff (record : (application setup leaks).TrafficRecord)
    (authored : record.input.broadcaster = record.input.envelope.sender) :
    permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = true ↔
      record.input.envelope.id ∈ record.ledger.map Message.id ∨
        (record.input.envelope.id.2 =
          record.ledger.countP (fun message => message.sender = record.input.envelope.sender) ∧
          openingTraffic setup leaks record) := by
  classical
  rcases record with ⟨observation, ledger, broadcaster, envelope⟩
  change broadcaster = envelope.sender at authored
  subst broadcaster
  simp only [permittedRosterEnvelope, envelopeEvidence, decide_eq_true_eq]

theorem permittedRosterEnvelope_published (record : (application setup leaks).TrafficRecord)
    (published : record.input.envelope.id ∈ record.ledger.map Message.id) :
    permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  classical
  exact decide_eq_true (Or.inl published)

/-- The serial witnesses a forbidden fresh envelope even when all other
transmissions are absent from the auditor's sample. -/
theorem permittedRosterEnvelope_wrong_serial
    (record : (application setup leaks).TrafficRecord)
    (unpublished : record.input.envelope.id ∉ record.ledger.map Message.id)
    (wrong : record.input.envelope.id.2 ≠
      record.ledger.countP (fun message => message.sender = record.input.envelope.sender)) :
    permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = false := by
  classical
  simp only [permittedRosterEnvelope, envelopeEvidence, unpublished, wrong, false_and,
    or_self, decide_false]

/-- At a completed source prefix all allocated fresh envelopes have been
included once, so the next per-author serial is the public count. -/
theorem PublicCheckpoint.serial_eq_ledger_count
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : EventLowering.ContextRefs (graph setup).layout Γ}
    {rank : Nat} {execution : (application setup leaks).Execution}
    (checkpoint : PublicCheckpoint setup leaks initial source refs rank execution)
    (who : Player) :
    execution.network.nextSerial who =
      execution.network.ledger.countP (fun message => message.sender = who) := by
  rw [checkpoint.counters, checkpoint.ledger]
  exact publicationSerial_eq_ledger_count _ _ who

variable [Fintype Player]

/-- Silence and every effective known replay already belong to the roster
menu. Thus every additional effective response allocates a fresh envelope. -/
theorem roster_extra_submission (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who past view)
    (excluded : response ∉ (rosterMenu setup leaks bounds rosters).actions who past view) :
    ∃ submission, response = ⟨some (.submit submission)⟩ := by
  classical
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact (excluded (silence_roster setup leaks bounds rosters who past view)).elim
  | some transmission =>
      cases transmission with
      | submit submission => exact ⟨submission, rfl⟩
      | replay id =>
          apply False.elim
          apply excluded
          apply replay_roster setup leaks bounds rosters who past view
          apply (application setup leaks).replayPolicy_support past view (some id)
          have known := ((bounds.menu_mem (runtime setup) leaks who past view _).mp effective).1
          change ReactiveApplication.SubmissionNormalization.ReplayKnown past view id at known
          obtain ⟨message, member, identified⟩ := known
          apply Finset.mem_insert_of_mem
          exact Finset.mem_image.mpr
            ⟨id, List.mem_toFinset.mpr (List.mem_map.mpr ⟨message, member, identified⟩), rfl⟩

/-- On every legal retained owner history, the public serial test is exactly
the private recall test for whether the phase still permits a fresh opening. -/
theorem roster_fresh_iff_serial (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (grantedNow : control.execution.application.serviceGrant = some event)
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
  obtain ⟨phase, slot, granted, prior, sample, initial, state, selected, initialSupport,
      related, _, grant, offset, serials, published, reached, activated,
      unchanged, _⟩ :=
    roster_decision_phase setup leaks bounds rosters network reveals openable
      who control trace active
  have samePhase : phase = event := by
    rw [unchanged, grant] at grantedNow
    exact Option.some.inj grantedNow
  subst phase
  have data := owner_choices_at_prefix setup leaks bounds profile who initial initialSupport
    setup.program reveals profile
    (EventLowering.ContextRefs.initial setup.context (EventLowering.outputLayout setup.program))
    (Revelations.initial setup.context) (EventLowering.outputEmbedding setup.program)
    (EventLowering.initialRefsBefore setup.program) 0
    (EventLowering.CompiledPolicySuffix.whole setup.program profile)
    event.val event.isLt state granted related event (by omega) ownedEvent grant
  obtain ⟨expected, expectedRaw, priorOpening, owned, valid, _, _⟩ := data.2.2
  have same := rosterOpening?_application_eq setup leaks who event control.execution granted
    unchanged
  rw [openingNow, priorOpening] at same
  cases Option.some.inj same
  have covered : ∀ player past view response,
      response ∈ (menu.uniformResponses player past view).support →
        response ∈ rosterActions setup leaks bounds rosters player past view := by
    intro player past view response supported
    exact (menu.uniformResponses_support player past view response).mp supported
  obtain ⟨chosen, frame, earlier, recorded, _⟩ := roster_window_posterior setup leaks bounds rosters
    granted event who grant ownedEvent candidate raw priorOpening owned valid (offset who) serials
    published menu.uniformResponses covered network ((rosters event).take slot)
    (roster_count_before selected).le prior reached
  obtain ⟨context, source, refs, checkpoint⟩ := related.checkpoint setup.program
    (EventLowering.ContextRefs.initial setup.context (EventLowering.outputLayout setup.program))
    (Revelations.initial setup.context) (EventLowering.outputRef setup.program) 0 event.val state
    granted
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
    obtain ⟨otherEvent, _, _, otherGrant, _, _, _, absent⟩ :=
      rosterFresh?_shape setup leaks rosters who _ _ _ fresh
    change prior.application.serviceGrant = some otherEvent at otherGrant
    rw [frame.application, grant] at otherGrant
    cases Option.some.inj otherGrant
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
    have currentGrant :
        (prior.sampledActivation (application setup leaks) who sample).application.serviceGrant =
          some event := by
      change prior.application.serviceGrant = some event
      rw [frame.application]
      exact grant
    have currentOpening : rosterOpening? setup leaks who event
        ((prior.sampledActivation (application setup leaks) who sample).observe
          (application setup leaks) who) = some (candidate, raw) := by
      rw [rosterOpening?_application_eq setup leaks who event
        (prior.sampledActivation (application setup leaks) who sample) granted frame.application]
      exact priorOpening
    unfold rosterFresh?
    apply Option.bind_eq_some_iff.mpr
    refine ⟨event, currentGrant, ?_⟩
    rw [ite_eq_right (not_not_intro ownedEvent)]
    apply Option.bind_eq_some_iff.mpr
    refine ⟨(candidate, raw), currentOpening, ?_⟩
    dsimp only [bind, Option.bind]
    simp only [List.any_eq_true, decide_eq_true_eq]
    exact ite_eq_right absent

end Vegas.SourceProgram.RevealService
