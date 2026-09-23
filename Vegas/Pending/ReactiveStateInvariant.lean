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
    (execution : runtime.reactiveApplication.Execution) (who : Player)
    (action : runtime.reactiveApplication.Action) :
    (execution.respond runtime.reactiveApplication who action).application.config =
        execution.application.config ∧
      (execution.respond runtime.reactiveApplication who action).application.publicView =
        execution.application.publicView := by
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => exact ⟨rfl, rfl⟩
  | some transmission =>
      cases transmission with
      | replay id => exact ⟨rfl, rfl⟩
      | submit material =>
          exact ⟨(submitStep_config _ who material.packet).trans
            (material.register_facts who execution.application).1,
            (submitStep_publicView _ who material.packet).trans
              (material.register_facts who execution.application).2.2⟩

theorem reactiveStateInvariant (runtime : EventGraphRuntime graph) (inputs : graph.Inputs) :
    runtime.reactiveApplication.Invariant (State.Invariant inputs) where
  submit state who material valid := by
    apply valid.copy
    · exact (submitStep_config _ who material.packet).trans (material.register_facts who state).1
    · exact congrArg PublicView.clock
        ((submitStep_publicView _ who material.packet).trans
          (material.register_facts who state).2.2)
    · exact congrArg PublicView.activatedAt
        ((submitStep_publicView _ who material.packet).trans
          (material.register_facts who state).2.2)
  handle state message next valid accepted :=
    handle_invariant runtime state next message valid accepted
  environment state command next valid supported :=
    environmentStep_invariant runtime state next command valid supported

theorem reactiveStoreInvariant (runtime : EventGraphRuntime graph) (field : graph.Field)
    (value : (graph.layout field).Value) : runtime.reactiveApplication.Invariant
      (fun state => state.config.store field = some value) where
  submit state who material stored := by
    change (submitStep (material.register state who) who material.packet).config.store field = _
    rw [submitStep_config, (material.register_facts who state).1]
    exact stored
  handle state message next stored accepted :=
    handle_store_of_some runtime state next message accepted field value stored
  environment state command next stored supported :=
    environmentStep_store_of_some runtime state next command supported field value stored

end Vegas.EventGraphRuntime
