/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDecisionMiss

/-! # Completed decisions remain unmarked

An actual public miss can only be created by expiry while its event is ready.
Once an event has completed without that marker, every later raw response and
environment command preserves both facts.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Completed unmarked decisions are preserved by all raw operations. -/
theorem reactiveCompletedDecisionInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) : (runtime.reactiveApplication leaks).Invariant
      (fun state => event ∈ state.config.cut.completed ∧ event ∉ state.missedEvents) where
  submit state who material valid := by
    have same := runtime.reactive_respond_application leaks
      (.initial (runtime.reactiveApplication leaks) state) who ⟨some material⟩
    have configSame := same.1
    have marked := congrArg PublicView.missedEvents same.2
    change ((runtime.reactiveApplication leaks).submit state who material).config = state.config
      at configSame
    change ((runtime.reactiveApplication leaks).submit state who material).missedEvents =
      state.missedEvents at marked
    constructor
    · rw [configSame]
      exact valid.1
    · rw [marked]
      exact valid.2
  handle state message next valid accepted := by
    refine ⟨handle_completed_subset runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call accepted) valid.1, ?_⟩
    rw [handle_missedEvents runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call accepted)]
    exact valid.2
  environment state command next valid reached := by
    refine ⟨environmentStep_completed_subset runtime state next command reached valid.1, ?_⟩
    intro marked
    have expired := environmentStep_new_missedEvent runtime state next command reached event
      valid.2 marked
    exact expired.2.1.1 valid.1

end Vegas.EventGraphRuntime
