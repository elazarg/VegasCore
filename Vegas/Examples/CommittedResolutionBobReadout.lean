/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionBobService
import Vegas.Game.RevealServiceRosterContinuation

/-! # Complete typed readout after an immutable final disclosure

At a legal Bob prefix every field except his publication is already fixed.
Raw preparation changes neither the configuration nor its stored values.
Store persistence therefore identifies the entire typed source outcome of
any two continuations with the same Bob result, including private inputs.
-/

noncomputable section

namespace Vegas.Examples.CommittedResolutionBobReadout

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability
open CommittedResolutionService CommittedResolutionBobService

/-- Every graph field other than Bob's last publication is available at his
ready prefix. This is a property of the actual source dependencies. -/
theorem bob_prefix_other_field_available (physical : EventGraphRuntime.State nativeGraph)
    (ready : physical.config.cut.Ready bobEvent) (field : nativeGraph.Field)
    (different : field ≠ .inr bobEvent) : (physical.config.store field).isSome = true := by
  cases field with
  | inl input => rfl
  | inr event =>
      apply (physical.config.output_available event).mpr
      have predecessor : event ∈ nativeGraph.order.predecessors bobEvent := by
        change Fin 3 at event
        fin_cases event
        · decide
        · decide
        · exact False.elim (different rfl)
      exact ready.2 predecessor

/-- Arbitrary raw responses and arbitrary future controllers preserve every
previously fixed source field. Private preparation and packet aliases do not
change the original private inputs or the earlier publication result. -/
theorem bob_continuation_other_fields (players : Player → app.Policy)
    (scheduler : app.Scheduler) (count : Nat) (execution final : app.Execution)
    (ready : execution.application.config.cut.Ready bobEvent) (response : app.Action)
    (reached : final ∈ (app.runRounds scheduler players count
      (execution.respond app bob response)).support) :
    ∀ field : nativeGraph.Field, field ≠ .inr bobEvent →
      final.application.config.store field = execution.application.config.store field := by
  intro field different
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
    (bob_prefix_other_field_available execution.application ready field different)
  have before : (execution.respond app bob response).application.config.store field =
      some value := by
    rw [((runtime setup).reactive_respond_application leaks execution bob response).1]
    exact stored
  have after := (ReactiveApplication.Invariant.policyInvariant app
    ((runtime setup).reactiveStoreInvariant leaks field value) players).runRounds
      scheduler count (execution.respond app bob response) final before reached
  exact after.trans stored.symm

/-- The full source-state readout depends only on Bob's publication result
once its legal decision prefix is fixed. Both continuations may use arbitrary
raw submissions and completely different future policies and schedulers. -/
theorem bob_continuation_readout_eq (execution : app.Execution)
    (ready : execution.application.config.cut.Ready bobEvent)
    (firstPlayers secondPlayers : Player → app.Policy)
    (firstScheduler secondScheduler : app.Scheduler)
    (firstCount secondCount : Nat) (firstResponse secondResponse : app.Action)
    (firstFinal secondFinal : app.Execution)
    (firstReached : firstFinal ∈ (app.runRounds firstScheduler firstPlayers firstCount
      (execution.respond app bob firstResponse)).support)
    (secondReached : secondFinal ∈ (app.runRounds secondScheduler secondPlayers secondCount
      (execution.respond app bob secondResponse)).support)
    (sameResult : firstFinal.application.config.store (.inr bobEvent) =
      secondFinal.application.config.store (.inr bobEvent)) :
    sourceReadout setup leaks (app.finished firstFinal) =
      sourceReadout setup leaks (app.finished secondFinal) := by
  have first := bob_continuation_other_fields firstPlayers firstScheduler firstCount execution
    firstFinal ready firstResponse firstReached
  have second := bob_continuation_other_fields secondPlayers secondScheduler secondCount execution
    secondFinal ready secondResponse secondReached
  have stores : firstFinal.application.config.store = secondFinal.application.config.store := by
    funext field
    by_cases current : field = .inr bobEvent
    · subst field
      exact sameResult
    · exact (first field current).trans (second field current).symm
  change sourceReadout setup leaks (some ⟨0, none, firstFinal⟩) =
    sourceReadout setup leaks (some ⟨0, none, secondFinal⟩)
  rw [sourceReadout_eq_decode, sourceReadout_eq_decode]
  exact congrArg (decodeState? (terminalRefs program)) stores

/-- In particular every accepting response has the canonical successful
complete typed outcome; raw aliases cannot improve its source base payoff. -/
theorem bob_success_continuation_readout_eq (execution : app.Execution)
    (ready : execution.application.config.cut.Ready bobEvent)
    (firstPlayers secondPlayers : Player → app.Policy)
    (firstScheduler secondScheduler : app.Scheduler)
    (firstCount secondCount : Nat) (firstResponse secondResponse : app.Action)
    (firstFinal secondFinal : app.Execution)
    (firstReached : firstFinal ∈ (app.runRounds firstScheduler firstPlayers firstCount
      (execution.respond app bob firstResponse)).support)
    (secondReached : secondFinal ∈ (app.runRounds secondScheduler secondPlayers secondCount
      (execution.respond app bob secondResponse)).support)
    (firstSuccess : firstFinal.application.config.store (.inr bobEvent) = some (.success true))
    (secondSuccess : secondFinal.application.config.store (.inr bobEvent) = some (.success true)) :
    sourceReadout setup leaks (app.finished firstFinal) =
      sourceReadout setup leaks (app.finished secondFinal) :=
  bob_continuation_readout_eq execution ready firstPlayers secondPlayers firstScheduler
    secondScheduler firstCount secondCount firstResponse secondResponse firstFinal secondFinal
    firstReached secondReached (firstSuccess.trans secondSuccess.symm)

/-- Every actual Bob horizon continuation has a complete typed source state,
even after a malformed response. Existence follows from the actual all-history
completion contract and the compiler's typed decoder. -/
theorem bob_horizon_readout_exists (players : Player → app.Policy) (control : app.Control)
    (trace : (app.protocol (initialLaw setup) CommittedResolutionService.horizon
      CommittedResolutionRecovery.scheduler).Trace (some control))
    (active : control.actor = some bob) (response : app.Action) (final : app.Execution)
    (reached : final ∈ (app.runRounds CommittedResolutionRecovery.scheduler players 5
      (control.execution.respond app bob response)).support) :
    ∃ terminal : State simpleExpr program.terminalCtx,
      sourceReadout setup leaks (app.finished final) = some terminal := by
  have baseTrace := app.trace_of_scheduler_support_subset (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler
      CommittedResolutionService.scheduler
        CommittedResolutionRecovery.scheduler_support_subset trace
  have budget := bob_activation_remaining control baseTrace active
  rcases control with ⟨remaining, actor, execution⟩
  dsimp only at active budget
  subst actor
  subst remaining
  obtain ⟨responded⟩ := app.raw_trace_respond (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler 5 execution bob
      response trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (initialLaw setup)
    CommittedResolutionService.horizon CommittedResolutionRecovery.scheduler players 0 5
      (execution.respond app bob response) final responded reached
  have completed := CommittedResolutionRecovery.contract.completes ⟨0, none, final⟩
    finalTrace ⟨rfl, rfl⟩
  have present : (sourceReadout setup leaks (app.finished final)).isSome = true := by
    change (sourceReadout setup leaks (some ⟨0, none, final⟩)).isSome = true
    rw [sourceReadout_eq_decode]
    exact decodeState?_isSome_of_available _ _
      (fun field => final.application.config.store_available_of_terminal completed field)
  exact Option.isSome_iff_exists.mp present

end Vegas.Examples.CommittedResolutionBobReadout
