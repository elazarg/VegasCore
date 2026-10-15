/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairInclusion
import Vegas.Pending.PhaseFailureCoverage
import Vegas.EventGraph.ResolutionProvenance

/-! # Completed bindings and executed disclosures during directed repair -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace BindingShadow

omit [DecidableEq Player] in
/-- Reconstruction of an actual completion uses the remembered original action
and value exactly at that edge and keeps all earlier private overrides. -/
theorem config_complete (memory : BindingShadow graph) (state : graph.Config)
    (event : graph.EventId) (ready : state.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    memory.config (state.complete event ready action value) =
      (memory.config state).complete event ready ((memory.actions event).getD action)
        ((memory.values (.inr event)).getD value) := by
  classical
  apply Config.ext_fields (left := memory.config (state.complete event ready action value))
    (right := (memory.config state).complete event ready ((memory.actions event).getD action)
      ((memory.values (.inr event)).getD value)) rfl rfl
  · funext query
    by_cases same : query = event
    · subst query
      simp only [config, Config.complete, Function.update_self, Option.map_some]
    · simp only [config, Config.complete, Function.update_of_ne same]
  · change (state.history ++ [(⟨event, action⟩ : graph.Completion)]).map memory.completion =
      state.history.map memory.completion ++ [⟨event, (memory.actions event).getD action⟩]
    rw [List.map_append]
    rfl

/-- Native completion retains public association, clock and refreshed readiness
metadata. The original and repaired dependent values may differ. -/
theorem native_complete (memory : BindingShadow graph) (owner : Player) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    memory.native owner (state.complete event ready action value) =
      (memory.native owner state).complete event ready ((memory.actions event).getD action)
        ((memory.values (.inr event)).getD value) := by
  change (⟨_, state.accepted, _, state.clock, _⟩ : State graph) = ⟨_, _, _, _, _⟩
  rw [State.mk.injEq]
  exact ⟨config_complete memory state.config event ready action value, rfl, rfl, rfl, rfl⟩

end BindingShadow

namespace RecoveryState.FailureCoverage

omit [DecidableEq Player] in
/-- A completed disclosure in a clear actual state read a successful typed
binding. An accepted unusable value cannot have been exposed earlier. -/
theorem completed_publication_binding {state : RecoveryState graph}
    (covered : state.FailureCoverage) (clear : state.excluded = ∅)
    {inputs : graph.Inputs} (reachable : state.native.config.Reachable inputs)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (completed : event ∈ state.native.config.cut.completed) :
    ∃ value, binding.get? state.native.config.store = some (.success value) := by
  classical
  have castNone {α β : Type} (same : α = β) :
      cast (congrArg Option same) (none : Option α) = (none : Option β) := by
    cases same
    rfl
  have castSome {α β : Type} (same : α = β) (value : α) :
      cast (congrArg Option same) (some value) = some (cast same value) := by
    cases same
    rfl
  let ref : FieldRef graph.layout (.publication payload) := ⟨.inr event, outputEq⟩
  have available : (ref.get? state.native.config.store).isSome = true :=
    ref.get?_isSome _ ((state.native.config.output_available event).mpr completed)
  cases published : ref.get? state.native.config.store with
  | none => simp only [published, Option.isSome_none, Bool.false_eq_true] at available
  | some result =>
      cases result with
      | success value => exact ⟨value, reachable.publication_binding event owner payload binding
          checks outputEq codeEq value published⟩
      | failure =>
          have failed : RecoveryState.publicationFailed state.native event = true := by
            rw [RecoveryState.publicationFailed, node]
            cases output : state.native.config.outputs event with
            | none =>
                have absent : ref.get? state.native.config.store = none := by
                  unfold FieldRef.get?
                  change cast (congrArg (fun kind => Option kind.Value) outputEq)
                    (state.native.config.outputs event) = none
                  rw [output]
                  exact castNone (congrArg EventField.Value outputEq)
                rw [absent] at published
                cases published
            | some actual =>
                have result : cast (congrArg EventField.Value outputEq) actual =
                    PublicationResult.failure := by
                  change cast (congrArg (fun kind => Option kind.Value) outputEq)
                    (state.native.config.outputs event) = some PublicationResult.failure
                      at published
                  rw [output] at published
                  have castSome : cast (congrArg (fun kind => Option kind.Value) outputEq)
                      (some actual) = some (cast (congrArg EventField.Value outputEq) actual) :=
                    castSome (congrArg EventField.Value outputEq) actual
                  rw [castSome] at published
                  exact Option.some.inj published
                simp only [result]
          have acting : graph.actor? event = some owner :=
            (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
              (congrArg EventCode.actor codeEq)
          have excluded := covered.covered event owner acting (Or.inr failed)
          simp only [clear, Finset.notMem_empty] at excluded

end RecoveryState.FailureCoverage
end Vegas.EventGraphRuntime
