/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceCompletion
import Vegas.Game.SourceServiceTurnPolicy
import Vegas.Pending.ReactiveAsyncContract

/-! # Protection of the owner's first ready turn

Every completed scheduler round answers an activation, regardless of the
activated player's policy. The opportunity contract therefore bounds the
clock at an owner's first ready turn: a later clock would require an earlier
answered activation in the same readiness episode. The timing budget leaves
that first turn inside the protected inclusion window.

Foreign policies are unrestricted. No submission or silence premise is used
to infer protection of the current turn.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The opportunity requirement: an owner whose ready event's deadline is
past its reaction bound has had a turn there. -/
theorem opportunity_turn {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound) {remaining : Nat}
    {execution : (serviceApplication setup mode duration leaks).Execution}
    (trace :
        ((serviceApplication setup mode duration leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution) {owner : Player}
    {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event) (entered : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (late : entered + delay event < execution.application.clock) : ∃ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨scheduled, member, activate, _, seenReady⟩ := contract.opportunity _ trace event owner
    entered owned ((execution.application.publicView_eventReady event).mpr ready) activated late
  obtain ⟨answer, answerMember, viewEq⟩ := answered scheduled member owner activate
  have seen : answer.beforeView.application.publicView.EventReady event := by
    rw [viewEq]
    exact seenReady
  exact ⟨answer, answerMember, ownTurn?_of_entry_ready setup leaks execution facts.eventStable
    owner answer answerMember event owned seen ready⟩

/-- The first ready own turn is protected under the reaction and inclusion
budget. The view may be the freshly sampled activation view: only its first
turn count is needed, while the clock and readiness come from the actual raw
scheduler boundary. -/
theorem firstTurn_inclusionFits {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup mode duration) delay bound)
    {remaining : Nat} {execution : (serviceApplication setup mode duration leaks).Execution}
    (trace :
        ((serviceApplication setup mode duration leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    {view : (serviceApplication setup mode duration leaks).PlayerView}
    (first : serviceTurn setup mode duration leaks owner event (execution.logs owner) view =
        some 0) :
    execution.application.publicView.InclusionFitsDeadline (serviceTimeouts setup mode duration)
        bound event := by
  have nativeTrace := trace
  rw [serviceInitialLaw_eq_inputs setup] at nativeTrace
  obtain ⟨inputs, _, invariant⟩ :=
    (reactive_history_invariant (serviceTimeouts setup mode duration)) leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready
    (by rw [owned]; rfl)
  have early : execution.application.clock ≤ entered + delay event := by
    by_contra late
    obtain ⟨answer, member, turn⟩ := opportunity_turn contract trace answered owned ready entered
      activated (by omega)
    exact (sourceServiceTurn_first first).2 answer member turn
  have budget := timely event (by rw [owned]; rfl)
  change (match execution.application.activatedAt event with
    | none => False
    | some started => execution.application.clock - started + bound event <
        (serviceTimeouts setup mode duration).duration event)
  rw [activated]
  omega

end Vegas
