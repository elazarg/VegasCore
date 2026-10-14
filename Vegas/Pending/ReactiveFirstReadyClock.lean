/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceOpportunity

/-! # The exact first-ready clock of an actual dispatched event

A clock advance retains all activation timestamps. Every other command has
zero clock ticks, so an event newly made ready is stamped at the resulting
public clock.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The actual clock-advance dispatch leaves every activation timestamp unchanged. -/
theorem dispatch_advanceClock_activatedAt (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players
      (.application .advanceClock) execution).support) :
    next.application.activatedAt = execution.application.activatedAt := by
  simp [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, ReactiveApplication.Execution.environmentStep,
    reactiveApplication, environmentStep] at reached
  subst next
  rfl

/-- Newly activated surviving events begin at the actual resulting clock,
including activation caused by arbitrary accepted packets or expiries. -/
theorem dispatch_newActivation_clock (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command) (event : graph.EventId)
    (entered : Nat) (valid : execution.application.Invariant inputs)
    (absent : execution.application.activatedAt event = none)
    (activated : next.application.activatedAt event = some entered)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players command
      execution).support) :
    entered = next.application.clock := by
  have progress := runtime.reactive_dispatch_progress leaks inputs players execution next command
    valid reached
  have origin := runtime.reactive_dispatch_activationOrigin leaks inputs players execution next
    command valid reached
  have created : execution.application.clock ≤ entered := by
    rcases origin event entered activated unfinished with retained | started
    · rw [absent] at retained
      cases retained
    · exact started
  have bounded := progress.invariant.activated_le event entered activated
  have zero : runtime.reactiveTicks leaks command = 0 := by
    cases command with
    | application operation =>
        cases operation with
        | advanceClock =>
            have same := runtime.dispatch_advanceClock_activatedAt leaks players execution next
              reached
            rw [same, absent] at activated
            cases activated
        | executeSample other => rfl
        | expire other => rfl
    | activate actor => rfl
    | «include» id => rfl
    | wait => rfl
  rw [progress.clock, zero, Nat.add_zero] at bounded ⊢
  exact Nat.le_antisymm bounded created

end Vegas.EventGraphRuntime
