/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptFirstPassage
import Vegas.Pending.PhaseRetryCompletion
import Vegas.Pending.PhaseClearTraceProgress

/-! # Genuine attempt entries contributing to clear full-information hits -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (initial : PMF (phaseApplication runtime leaks).State)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "E" => menu.protocol initial horizon scheduler
local notation "N" => menu.information initial horizon scheduler

private theorem stopped_phases
    (initialized : ∀ state ∈ initial.support, state.Ordered)
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ owner, (N).BehavioralPolicy owner)
    (entry final : (app).Control)
    (entryTrace : (E).Trace (some entry)) (finalTrace : (E).Trace (some final))
    (stopped : (E).History → Prop)
    (going_same : ∀ history : (E).History, ¬ stopped history → ∀ current,
      history.state = some current → current.execution.application.attempt =
        entry.execution.application.attempt)
    (supported : ⟨some final, finalTrace⟩ ∈
      ((N).runBehavioralUntil certificate profile stopped ⟨some entry, entryTrace⟩).support)
    (same : final.execution.application.attempt = entry.execution.application.attempt) :
    final.execution.application.phases = entry.execution.application.phases := by
  let property := fun state : (app).ProtocolState => ∃ current, state = some current ∧
    (current.execution.application.attempt = entry.execution.application.attempt →
      current.execution.application.phases = entry.execution.application.phases)
  have preserved : ∀ history : (E).History, ¬ stopped history →
      ¬ (E).terminal history.state → ∀ joint (legal : (E).Legal history.state joint) target,
      property history.state → target ∈ ((E).step history.state ⟨joint, legal⟩).support →
        property target := by
    intro history going _running joint _legal target holds reached
    obtain ⟨current, state, previous⟩ := holds
    have rawTrace := menu.toRawTrace initial horizon scheduler (state ▸ history.trace)
    have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
      initialized rawTrace
    have attempt := going_same history going current state
    have realized : target ∈ ((app).transition initial horizon scheduler (some current)
        joint).support := by
      change target ∈ ((app).transition initial horizon scheduler history.state joint).support
        at reached
      simpa only [state] using reached
    obtain ⟨next, rfl, _recall⟩ := (app).transition_recall_prefix initial horizon scheduler current
      target joint realized
    refine ⟨next, rfl, fun nextSame => ?_⟩
    exact ((phaseApplication_sameAttempt_phases runtime leaks).transition initial horizon
      scheduler current next joint realized ordered (attempt.trans nextSame.symm)).trans
        (previous attempt)
  obtain ⟨next, state, kept⟩ := (N).runBehavioralUntil_support_closed_of_going certificate profile
    stopped property preserved ⟨some entry, entryTrace⟩ ⟨entry, rfl, fun _ => rfl⟩
      ⟨some final, finalTrace⟩ supported
  cases Option.some.inj state
  exact kept same

/-- Every first-entry tag contributing to a clear active input is the actual
idle, clear entry to that SAME full namespace and SAME installed descriptor
list. Terminal, skipped and first-exclusion tags cannot contribute. The full
original execution and every earlier raw response remain in the entry. -/
theorem phase_attempt_entry_of_supported_hit
    (initialized : ∀ state ∈ initial.support, state.Ordered)
    (certificate : (E).WellFoundedHistories)
    (entryProfile profile : ∀ owner, (N).BehavioralPolicy owner)
    {who : Player} (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (final : (app).Control) (finalTrace : (E).Trace (some final))
    (atSite : (N).infoOf who finalTrace = site.1)
    (active : final.actor = some who)
    (clear : final.execution.application.current.excluded = ∅)
    (entry : (E).History) :
    let entryStop := fun history : (E).History =>
      phaseAttemptEntryStop runtime leaks view.application.2.attempt history.state
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ view.application.2.attempt ∨
          (N).infoOf who history.trace = site.1
    entry ∈ ((N).runBehavioralUntil certificate entryProfile entryStop (E).initHistory).support →
    ⟨some final, finalTrace⟩ ∈ ((N).runBehavioralUntil certificate profile stopped entry).support →
      ∃ current : (app).Control, entry.state = some current ∧
        current.actor = none ∧ current.execution.application.current.excluded = ∅ ∧
        current.execution.application.attempt = final.execution.application.attempt ∧
        current.execution.application.phases = final.execution.application.phases ∧
        ∀ owner, ∀ record ∈ current.execution.recall owner,
          record.beforeView.application.2.attempt ≠ current.execution.application.attempt := by
  classical
  intro entryStop stopped entrySupported hitSupported
  have finalRunning : ¬ (E).terminal (some final) := by
    change ¬ (final.remaining = 0 ∧ final.actor = none)
    rintro ⟨_remaining, absent⟩
    rw [active] at absent
    cases absent
  have entryRunning : ¬ (E).terminal entry.state := by
    intro ended
    have sameHistory := hitSupported
    rw [(N).runBehavioralUntil_of_terminal certificate profile ended,
      PMF.mem_support_pure_iff] at sameHistory
    have sameState := congrArg (fun history : (E).History => history.state) sameHistory
    rw [← sameState] at ended
    exact finalRunning ended
  have entryStopped := ((N).mem_support_runBehavioralUntil certificate entryProfile entryStop
    (E).initHistory entry entrySupported).resolve_right entryRunning
  obtain ⟨visible, finalState, _excluded, finalAttempt⟩ := phase_information_control_of_view
    runtime leaks menu initial horizon scheduler site past view observed
      ⟨⟨some final, finalTrace⟩, atSite⟩
  cases Option.some.inj finalState
  have retained :=  (N).runBehavioralUntil_support_prefix certificate profile stopped entry
    ⟨some final, finalTrace⟩ hitSupported
  rcases entry with ⟨state, entryTrace⟩
  cases state with
  | none => exact False.elim entryStopped
  | some current =>
      have earlierClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
        scheduler current final entryTrace finalTrace retained clear).1
      change current.execution.application.current.excluded ≠ ∅ ∨
        current.execution.application.attempt = view.application.2.attempt at entryStopped
      have currentAttempt : current.execution.application.attempt = view.application.2.attempt :=
        entryStopped.resolve_left (fun failed => failed earlierClear)
      have fresh := phase_attempt_first_visit_fresh runtime leaks menu initial initialized horizon
        scheduler certificate entryProfile view.application.2.attempt
          ⟨some current, entryTrace⟩ entrySupported current rfl currentAttempt
      refine ⟨current, rfl, fresh.1, earlierClear, currentAttempt.trans finalAttempt.symm, ?_, ?_⟩
      · apply Eq.symm
        apply stopped_phases runtime leaks menu initial horizon scheduler initialized certificate
          profile current final entryTrace finalTrace stopped ?_ hitSupported
            (finalAttempt.trans currentAttempt.symm)
        intro history going control state
        by_contra different
        apply going
        simp only [stopped, state]
        exact Or.inr (Or.inl fun same => different (same.trans currentAttempt.symm))
      · simpa only [currentAttempt] using fresh.2

end Vegas.EventGraphRuntime
