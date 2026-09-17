/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Compile.EventGraphEvaluation
import Vegas.EventGraph.Commutation

/-! # Source-state agreement across event-graph writes

The lowering names every source cell by a typed `ContextRefs` reference. Source
cells are immutable, so this one view suffices. This module proves that
completing the current source-ranked event preserves the view of the earlier
prefix, and that storing a new cell's value extends it.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

omit [DecidableEq Player] in
/-- A field preceding an event cannot be that event's output field. -/
theorem FieldBefore.ne_output {inputCount eventCount : Nat}
    {event : Fin eventCount}
    {field : Vegas.EventGraph.FieldId inputCount eventCount}
    (before : FieldBefore event field) : field ≠ .inr event := by
  cases field with
  | inl input => intro impossible; cases impossible
  | inr producer =>
      intro same
      have producerEq : producer = event := Sum.inr.inj same
      subst producer
      exact (Nat.lt_irrefl event.val) before

omit [DecidableEq Player] in
/-- Completing the current event leaves every earlier typed reference
unchanged. -/
theorem ContextRefs.Agrees.complete {graph : Vegas.EventGraph Player L}
    {config : graph.Config} {event : graph.EventId}
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    {Γ : SourceCtx Player L} (refs : ContextRefs graph.layout Γ)
    (state : State L Γ) (agree : refs.Agrees state config.store)
    (before : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore event (refs.get source).field) :
    refs.Agrees state (config.complete event ready action value).store := by
  intro name cell source
  rw [← agree source]
  apply (refs.get source).get?_congr
  rw [Vegas.EventGraph.store_complete]
  simp [Function.update, (before source).ne_output]

namespace ContextRefs

omit [DecidableEq Player] R in
/-- Extending the reference environment preserves agreement when the new head
reference stores the new source cell's exact typed value. -/
theorem Agrees.cons {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store)
    {name : VarId} {cell : CellTy Player L}
    (headRef : Vegas.EventGraph.FieldRef layout (cellField cell))
    (headValue : CellVal L cell)
    (headStored : headRef.get? store = some (cellValue headValue)) :
    (refs.cons (name := name) headRef).Agrees
      (Env.cons (x := name) headValue state) store := by
  intro readName readCell source
  cases source with
  | here => exact headStored
  | there source => exact agree source

end ContextRefs

/-- The canonical reference to a completed compiled event reads exactly the
value written by `Vegas.EventGraph.Config.complete`. -/
theorem outputRef_get?_complete {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (config : (toEventGraph program).Config)
    (event : Fin (eventCount program))
    (ready : config.cut.Ready event)
    (action : (toEventGraph program).Action event)
    (value : (outputLayout program event).Value) :
    (outputRef program event).get?
        (config.complete event ready action value).store = some value := by
  change (config.complete event ready action value).outputs event = some value
  exact config.complete_output_same event ready action value

/-- An embedded suffix output reference reads back the uncast source value
written at its whole-graph event. -/
theorem OutputEmbedding.ref_get?_complete
    {Γ0 : SourceCtx Player L} {open0 : Finset VarId}
    (whole : SourceProgram Player L Γ0 open0)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    (embedding : OutputEmbedding (inputLayout Γ0) (outputLayout whole) program)
    (config : (toEventGraph whole).Config)
    (index : Fin (eventCount program))
    (ready : config.cut.Ready (embedding.event index))
    (action : (toEventGraph whole).Action (embedding.event index))
    (outputEq : (toEventGraph whole).outputLayout (embedding.event index) =
      outputLayout program index)
    (value : (outputLayout program index).Value) :
    (embedding.ref index).get?
        (config.complete (embedding.event index) ready action
          (cast (congrArg Vegas.EventGraph.EventField.Value
            outputEq.symm) value)).store = some value := by
  change outputLayout whole (embedding.event index) = outputLayout program index at outputEq
  rw [Vegas.EventGraph.store_complete]
  simp only [OutputEmbedding.ref, Vegas.EventGraph.FieldRef.get?, Function.update_self]
  change cast (congrArg (fun kind => Option kind.Value) (embedding.layout_eq index))
      (some (cast (congrArg Vegas.EventGraph.EventField.Value
        outputEq.symm) value)) = some value
  have castSome {A B : Type} (same : A = B) (item : A) :
      cast (congrArg Option same) (some item) = some (cast same item) := by
    cases same
    rfl
  rw [castSome (congrArg Vegas.EventGraph.EventField.Value
    (embedding.layout_eq index))]
  have proofEq : congrArg Vegas.EventGraph.EventField.Value
      (embedding.layout_eq index) =
      congrArg Vegas.EventGraph.EventField.Value outputEq := Subsingleton.elim _ _
  rw [proofEq]
  have castInverse {A B : Type} (same : A = B) (item : B) :
      cast same (cast same.symm item) = item := by
    cases same
    rfl
  exact congrArg some
    (castInverse (congrArg Vegas.EventGraph.EventField.Value
      (embedding.layout_eq index)) value)

end Vegas.SourceProgram.EventLowering
