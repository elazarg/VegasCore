/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Commutation

/-! # Repair preserves every successful typed binding

A failed binding may be replaced by a successful value. Existing successful
bindings keep their exact values. This relation does not constrain public
results; their equality is a separate part of the runtime repair frame.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr}

namespace EventField

/-- The successful-binding part of the repair relation at one typed field. -/
def BindingRefines (kind : EventField Player L) : Option kind.Value → Option kind.Value → Prop :=
  match kind with
  | .binding _ _ => fun original repaired =>
      ∀ value, original = some (.success value) → repaired = some (.success value)
  | .publicData _ | .privateInput _ _ | .publication _ => fun _ _ => True

theorem BindingRefines.refl (kind : EventField Player L) (value : Option kind.Value) :
    kind.BindingRefines value value := by
  cases kind <;> try trivial
  exact fun _ equal => equal

theorem BindingRefines.cast {first second : EventField Player L} (same : first = second)
    {original repaired : Option first.Value} (preserved : first.BindingRefines original repaired) :
    second.BindingRefines (cast (congrArg (fun kind => Option kind.Value) same) original)
      (cast (congrArg (fun kind => Option kind.Value) same) repaired) := by
  cases same
  exact preserved

theorem BindingRefines.cast_some {first second : EventField Player L} (same : first = second)
    {original repaired : first.Value}
    (preserved : first.BindingRefines (some original) (some repaired)) :
    second.BindingRefines (some (_root_.cast (congrArg EventField.Value same) original))
      (some (_root_.cast (congrArg EventField.Value same) repaired)) := by
  cases same
  exact preserved

end EventField

namespace Store

/-- A pointwise native-store invariant; it includes initialized bindings and
new event outputs without encoding or evaluating source syntax. -/
def BindingRefines {Field : Type} {layout : Field → EventField Player L}
    (original repaired : Store layout) : Prop :=
  ∀ field, (layout field).BindingRefines (original field) (repaired field)

theorem BindingRefines.refl {Field : Type} {layout : Field → EventField Player L}
    (store : Store layout) : store.BindingRefines store :=
  fun _ => EventField.BindingRefines.refl _ _

theorem BindingRefines.update {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {original repaired : Store layout}
    (preserved : original.BindingRefines repaired) (field : Field)
    (left right : Option (layout field).Value)
    (current : (layout field).BindingRefines left right) :
    Store.BindingRefines (Function.update original field left)
      (Function.update repaired field right) :=
  by
  intro query
  by_cases same : query = field
  · subst query
    simpa only [Function.update_self] using current
  · simpa only [Function.update_of_ne same] using preserved query

theorem BindingRefines.success {Field : Type} {layout : Field → EventField Player L}
    {original repaired : Store layout} (preserved : original.BindingRefines repaired)
    {owner : Player} {payload : L.Ty} (binding : FieldRef layout (.binding owner payload))
    (value : L.Val payload) (successful : binding.get? original = some (.success value)) :
    binding.get? repaired = some (.success value) := by
  exact ((preserved binding.field).cast binding.layout_eq) value successful

end Store

variable [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every actual completion preserves the invariant if its new values do.
All unchanged typed fields are covered by the dependent store update. -/
theorem Config.bindingRefines_complete {original repaired : graph.Config}
    (preserved : original.store.BindingRefines repaired.store) (event : graph.EventId)
    (leftReady : original.cut.Ready event) (rightReady : repaired.cut.Ready event)
    (leftAction rightAction : graph.Action event)
    (leftValue rightValue : (graph.outputLayout event).Value)
    (current : (graph.outputLayout event).BindingRefines (some leftValue) (some rightValue)) :
    (original.complete event leftReady leftAction leftValue).store.BindingRefines
      (repaired.complete event rightReady rightAction rightValue).store := by
  rw [store_complete, store_complete]
  exact preserved.update (.inr event) _ _ current

end Vegas.EventGraph
