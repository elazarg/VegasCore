module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceCompletion
public import Vegas.Game.SourceServiceTurnPolicy
public import Vegas.Pending.ReactiveAsyncContract

@[expose] public section

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
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- The opportunity requirement: an owner whose ready event's deadline is
past its reaction bound has had a turn there. -/
theorem opportunity_turn {event : (serviceGraph setup deps).EventId}
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler delay bound) {remaining : Nat}
    {execution : (serviceApplication setup deps duration leaks).Execution}
    (trace :
        ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution) {owner : Player}
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event) (entered : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (late : entered + delay event < execution.application.clock) :
    ∃ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨scheduled, member, activate, _, seenReady⟩ := contract.opportunity _ trace event owner
    entered owned ((execution.application.publicView_eventReady event).mpr ready) activated late
  obtain ⟨answer, answerMember, viewEq⟩ := answered scheduled member owner activate
  have seen : answer.beforeView.application.publicView.EventReady event := by
    rw [viewEq]
    exact seenReady
  exact ⟨answer, answerMember,
    ownTurn?_of_entry_ready setup leaks execution facts.eventStable owner answer
      answerMember event ownerSolitary owned seen ready⟩

/-- The first ready own turn is protected under the reaction and inclusion
budget. The view may be the freshly sampled activation view: only its first
turn count is needed, while the clock and readiness come from the actual raw
scheduler boundary. -/
theorem firstTurn_inclusionFits {event : (serviceGraph setup deps).EventId}
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    {remaining : Nat} {execution : (serviceApplication setup deps duration leaks).Execution}
    (trace :
        ((serviceApplication setup deps duration leaks).protocol (serviceInitialLaw setup deps)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    {owner : Player}
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    {view : (serviceApplication setup deps duration leaks).PlayerView}
    (first : serviceTurn setup deps duration leaks owner event (execution.logs owner) view =
        some 0) :
    execution.application.publicView.InclusionFitsDeadline (serviceTimeouts setup deps duration)
        bound event := by
  have nativeTrace := trace
  rw [serviceInitialLaw_eq_inputs setup] at nativeTrace
  obtain ⟨inputs, _, invariant⟩ :=
    (reactive_history_invariant (serviceTimeouts setup deps duration)) leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready
    (by rw [owned]; rfl)
  have early : execution.application.clock ≤ entered + delay event := by
    by_contra late
    obtain ⟨answer, member, turn⟩ := opportunity_turn ownerSolitary contract trace answered
      owned ready entered activated (by omega)
    exact (sourceServiceTurn_first first).2 answer member turn
  have budget := timely event (by rw [owned]; rfl)
  change (match execution.application.activatedAt event with
    | none => False
    | some started => execution.application.clock - started + bound event <
        (serviceTimeouts setup deps duration).duration event)
  rw [activated]
  omega

end Vegas
