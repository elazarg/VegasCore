/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveInvariant
import Interaction.ReactivePolicyInvariant
import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EventStore

/-! # Reachability and stored values in reactive continuations -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactive_respond_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    (execution.respond (runtime.reactiveApplication leaks) who action).application.config =
        execution.application.config ∧
      (execution.respond (runtime.reactiveApplication leaks) who action).application.publicView =
        execution.application.publicView := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨rfl, rfl⟩
  | some transmission =>
      cases transmission with
      | replay id => exact ⟨rfl, rfl⟩
      | submit material =>
          exact ⟨(submitStep_config _ who material.call.packet).trans
            (material.call.register_facts who execution.application).1,
            (submitStep_publicView _ who material.call.packet).trans
              (material.call.register_facts who execution.application).2.2⟩

theorem reactiveStateInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) :
    (runtime.reactiveApplication leaks).Invariant (State.Invariant inputs) where
  submit state who material valid := by
    apply valid.copy
    · exact (submitStep_config _ who material.call.packet).trans
        (material.call.register_facts who state).1
    · exact congrArg PublicView.clock
        ((submitStep_publicView _ who material.call.packet).trans
          (material.call.register_facts who state).2.2)
    · exact congrArg PublicView.activatedAt
        ((submitStep_publicView _ who material.call.packet).trans
          (material.call.register_facts who state).2.2)
  handle state message next valid accepted :=
    handle_invariant runtime state next ⟨message.id, message.payload.call⟩ valid accepted
  environment state command next valid supported :=
    environmentStep_invariant runtime state next command valid supported

theorem reactiveStoreInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (field : graph.Field)
    (value : (graph.layout field).Value) : (runtime.reactiveApplication leaks).Invariant
      (fun state => state.config.store field = some value) where
  submit state who material stored := by
    change (submitStep (material.call.register state who) who
      material.call.packet).config.store field = _
    rw [submitStep_config, (material.call.register_facts who state).1]
    exact stored
  handle state message next stored accepted :=
    handle_store_of_some runtime state next ⟨message.id, message.payload.call⟩
      accepted field value stored
  environment state command next stored supported :=
    environmentStep_store_of_some runtime state next command supported field value stored

/-- Every initialized native history retains a configuration reachable by
the original graph rules from a supported setup. This allows arbitrary player
responses, scheduling, and passive observations. It asserts legality of game
effects, not equality of strategy spaces or equilibrium outcomes. -/
theorem reactive_history_graph_reachable (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : FinDist graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) {state}
    (trace : ((runtime.reactiveApplication leaks).protocol
      (inputs.map State.initial) horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant (fun state : State graph =>
      ∃ setup ∈ inputs.support, state.config.Reachable setup) state := by
  let preserved : (runtime.reactiveApplication leaks).Invariant
      (fun state : State graph => ∃ setup ∈ inputs.support, state.Invariant setup) := {
    submit := by
      rintro state who material ⟨setup, supported, valid⟩
      exact ⟨setup, supported,
        (runtime.reactiveStateInvariant leaks setup).submit state who material valid⟩
    handle := by
      rintro state message next ⟨setup, supported, valid⟩ accepted
      exact ⟨setup, supported,
        (runtime.reactiveStateInvariant leaks setup).handle state message next valid accepted⟩
    environment := by
      rintro state command next ⟨setup, supported, valid⟩ reached
      exact ⟨setup, supported,
        (runtime.reactiveStateInvariant leaks setup).environment state command next valid reached⟩ }
  have valid := preserved.history (inputs.map State.initial) horizon scheduler (by
    intro state supported
    obtain ⟨setup, chosen, rfl⟩ := FinDist.support_map .. ▸ supported
    exact ⟨setup, chosen, State.initial_invariant setup⟩) trace
  cases state with
  | none => trivial
  | some control =>
      obtain ⟨setup, supported, invariant⟩ := valid
      exact ⟨setup, supported, invariant.reachable⟩

end Vegas.EventGraphRuntime
