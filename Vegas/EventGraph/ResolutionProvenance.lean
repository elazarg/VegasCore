/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Execution

/-! # Successful publication comes from the retained binding

Resolution may hide a binding by returning failure. It cannot publish a different
value. The fact holds throughout every graph-reachable configuration.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem cast_option_none {α β : Type} (same : α = β) :
    cast (congrArg Option same) (none : Option α) = (none : Option β) := by
  cases same
  rfl

theorem EventCode.binding_success_of_resolve_success
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (disclose : Bool) (store : Store graph.layout) (value : L.Val payload)
    (resolved : EventCode.resolveOutput? binding checks disclose store =
      some (.success value)) :
    binding.get? store = some (.success value) := by
  unfold EventCode.resolveOutput? at resolved
  cases boundEq : binding.get? store with
  | none => simp [boundEq] at resolved
  | some bound =>
      cases checksEq : GuardCheck.allAccepted? checks store
          (if disclose then bound else .failure) with
      | none => simp [boundEq, checksEq] at resolved
      | some accepted =>
          cases disclose <;> cases accepted <;>
            simp_all

omit R in
private theorem option_value_cast_roundtrip
    {left right : EventField Player L} (same : left = right)
    (value : right.Value) :
    cast (congrArg Option (congrArg EventField.Value same))
        (some (cast (congrArg EventField.Value same.symm) value)) = some value := by
  cases same
  rfl

/-- Completing a resolution through its graph step stores exactly its
deterministic resolution result.  The statement transports the endpoint
value back across the public-output identification so callers need not expose
the evaluator's dependent casts. -/
theorem Config.resolution_step_output
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (config next : graph.Config) (ready : config.cut.Ready event)
    (action : graph.Action event)
    (member : next ∈ (config.step event ready action).support) :
    EventCode.resolveOutput? binding checks
        (cast (congrArg EventField.Action outputEq) action) config.store =
      cast (congrArg Option (congrArg EventField.Value outputEq))
        (next.outputs event) := by
  let disclose := cast (congrArg EventField.Action outputEq) action
  have readsEq : (graph.nodes event).readFields =
      insert binding.field (GuardCheck.listReadFields checks) := by
    calc
      (graph.nodes event).readFields =
          (cast (congrArg (EventCode graph.layout) outputEq)
            (graph.nodes event)).readFields := by
        exact (EventCode.readFields_cast outputEq (graph.nodes event)).symm
      _ = (EventCode.resolve owner payload binding checks).readFields :=
        congrArg EventCode.readFields codeEq
      _ = insert binding.field (GuardCheck.listReadFields checks) := rfl
  have available : ∀ field ∈ insert binding.field
      (GuardCheck.listReadFields checks),
      (config.store field).isSome = true := by
    intro field fieldMem
    apply config.read_available ready
    rw [readsEq]
    exact fieldMem
  have defined := EventCode.resolveOutput?_isSome binding checks disclose
    config.store available
  cases resolved : EventCode.resolveOutput? binding checks disclose config.store with
  | none => simp [resolved] at defined
  | some result =>
      have graphLaw := config.step_eq_map_of_code event ready outputEq
        (.resolve owner payload binding checks) codeEq disclose (FinDist.pure result)
      rw [EventCode.resolve_eval?, resolved] at graphLaw
      specialize graphLaw rfl
      simp only [FinDist.map_pure] at graphLaw
      have actionRoundtrip :
          cast (congrArg EventField.Action outputEq.symm) disclose = action := by
        simp [disclose]
      rw [actionRoundtrip] at graphLaw
      rw [graphLaw, FinDist.mem_support_pure] at member
      subst next
      rw [Config.complete_output_same]
      exact (option_value_cast_roundtrip outputEq result).symm


/-- Every successful resolution in a reachable graph retains the same successful
binding, including after arbitrary subsequent graph events. -/
theorem Config.Reachable.publication_binding {inputs : graph.Inputs} {config : graph.Config}
    (reachable : config.Reachable inputs)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (value : L.Val payload)
    (published : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
      config.store = some (.success value)) :
    binding.get? config.store = some (.success value) := by
  induction reachable with
  | initial =>
      have absent : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
          (Config.initial inputs).store = none := by
        unfold FieldRef.get? Config.store Config.initial
        exact cast_option_none (congrArg EventField.Value outputEq)
      rw [absent] at published
      cases published
  | @step before prior completed ready action after reached ih =>
      apply binding.get?_preserved before.store after.store
        (fun field result stored => before.step_store_of_some after completed ready action
          reached field result stored) (.success value)
      by_cases same : completed = event
      · subst completed
        have resolved := Config.resolution_step_output event owner payload binding checks
          outputEq codeEq before after ready action reached
        change EventCode.resolveOutput? binding checks _ before.store =
          (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
            after.store at resolved
        rw [published] at resolved
        exact EventCode.binding_success_of_resolve_success binding checks _ before.store
          value resolved
      · apply ih
        have storedEq : after.outputs event = before.outputs event := by
          obtain ⟨result, _, rfl⟩ := FinDist.support_map .. ▸ reached
          exact before.complete_output_of_ne completed event ready action result (Ne.symm same)
        have viewEq :=
          (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?_congr
          after.store before.store storedEq
        rwa [viewEq] at published

end Vegas.EventGraph
