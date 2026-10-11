/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFirstOpportunity
import Interaction.ReactiveRawRoundTrace

/-! # Repeated actual prescribed opportunities -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- An actual prescribed focal player cannot redraw a previously recorded source
turn in an initialized run, even when every opponent uses an arbitrary raw policy. -/
theorem prescribedReactivePolicy_silent_after_turn_of_initialized_support
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (focal : players who = runtime.prescribedReactivePolicy leaks who policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (state : State graph) (execution : (runtime.reactiveApplication leaks).Execution)
    (reached : execution ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)).support)
    (event : graph.EventId) (owned : graph.actor? event = some who)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (retained : entry ∈ execution.recall who)
    (earlierTurn : entry.beforeView.application.publicView.ownTurn? who = some event)
    (turn : execution.application.publicView.ownTurn? who = some event) :
    runtime.prescribedReactivePolicy leaks who policy (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who) = PMF.pure ⟨none⟩ := by
  let app := runtime.reactiveApplication leaks
  have consistent := (app.consistentRecall_policyInvariant players).runRounds scheduler count
    (ReactiveApplication.Execution.initial app state) execution (fun owner => .nil) reached
  have ownConsistent := consistent who
  rw [focal] at ownConsistent
  have quiet := (app.silentEmission_invariant players who).runRounds scheduler count
    (ReactiveApplication.Execution.initial app state) execution
    (by simp [ReactiveApplication.Execution.initial]) reached
  have sent := (runtime.reactiveEmission_call_invariant leaks players who).runRounds scheduler
    count (ReactiveApplication.Execution.initial app state) execution
    (by simp [ReactiveApplication.Execution.initial]) reached
  have initialized :
      execution ∈ (app.roundsFrom (PMF.pure state) scheduler players count).support := by
    simpa only [ReactiveApplication.roundsFrom, PMF.pure_bind] using reached
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (PMF.pure state) count scheduler players count
    le_rfl execution initialized
  obtain ⟨before, _, _, viewed⟩ := app.recorded_response_prefix (PMF.pure state) count scheduler
    ⟨count - count, none, execution⟩ trace who entry retained
  have identity : entry.beforeView.application.who = who := by
    rw [viewed]
    rfl
  exact runtime.prescribedReactivePolicy_silent_after_recorded_turn leaks who policy
    (execution.recall who) ownConsistent quiet sent event entry retained earlierTurn identity
    owned (execution.observe app who) turn

end Vegas.EventGraphRuntime
