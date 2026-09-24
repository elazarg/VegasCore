/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyInvariant
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.EventStore

/-! # Reachability and immutable fields in reactive continuations -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveApplicationInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (inputs : graph.Inputs) :
    (runtime.reactiveApplication leaks).Invariant (State.Invariant inputs) where
  submit state who material valid :=
    (runtime.reactive_respond_progress leaks inputs
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
      who ⟨some (.submit material)⟩ valid).invariant
  handle state message next valid accepted :=
    handle_invariant runtime state next message valid accepted
  environment state command next valid reached :=
    environmentStep_invariant runtime state next command valid reached

/-- Every fixed field survives arbitrary responses, inclusions, clock ticks,
and application commands. No honesty or service assumption is required. -/
theorem reactiveStoreInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (field : graph.Field) (value : (graph.layout field).Value) :
    (runtime.reactiveApplication leaks).Invariant
      (fun state => state.config.store field = some value) where
  submit state who material stored := by
    change (submitStep (material.register state who) who material.packet).config.store field = _
    rw [submitStep_config, (material.register_facts who state).1]
    exact stored
  handle state message next stored accepted :=
    handle_store_of_some runtime state next message accepted field value stored
  environment state command next stored reached :=
    environmentStep_store_of_some runtime state next command reached field value stored

end Vegas.EventGraphRuntime
