/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Compile.EventGraphEvaluation
import Vegas.EventGraph.Execution

/-! # Initial source values in event-graph stores

The input encoding preserves each source cell's typed binding or public value.
Agreement is independent of event outputs, so it also holds after execution has
started.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

omit [DecidableEq Player] R in
/-- Reading an encoded input at its source context position preserves its
original payload type and failure-aware binding value. -/
theorem encodeInputs_get {Γ : SourceCtx Player L} (state : State L Γ)
    {name : VarId} {cell : CellTy Player L} (source : HasVar Γ name cell) :
    cast (congrArg Vegas.EventGraph.EventField.Value (inputLayout_inputId source))
      (encodeInputs state (inputId source)) = cellValue (state.get source) := by
  induction source with
  | @here _ _ headCell => cases headCell <;> rfl
  | @there _ _ _ _ headCell source ih =>
      cases headCell <;> exact ih (fun _ _ ref => state.get (.there ref))

omit [DecidableEq Player] R in
/-- The initial reference environment agrees with any graph store retaining
the encoded inputs, irrespective of which event outputs have been filled. -/
theorem ContextRefs.initial_agrees {Γ : SourceCtx Player L}
    {count : Nat} (outputs : Fin count → Vegas.EventGraph.EventField Player L)
    (state : State L Γ)
    (store : Vegas.EventGraph.Store (Vegas.EventGraph.fieldLayout (inputLayout Γ) outputs))
    (inputs : ∀ input, store (.inl input) = some (encodeInputs state input)) :
    (ContextRefs.initial Γ outputs).Agrees state store := by
  intro name cell source
  change cast (congrArg (fun kind => Option kind.Value) (inputLayout_inputId source))
    (store (.inl (inputId source))) = some (cellValue (state.get source))
  rw [inputs]
  have castSome {A B : Type} (equality : A = B) (value : A) :
      cast (congrArg Option equality) (some value) = some (cast equality value) := by
    cases equality
    rfl
  rw [castSome (congrArg Vegas.EventGraph.EventField.Value (inputLayout_inputId source))]
  exact congrArg some (encodeInputs_get state source)

/-- The actual initial configuration of the whole compiled graph represents
the complete initial source state. -/
theorem initialConfig_agrees {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (state : State L Γ) :
    (ContextRefs.initial Γ (outputLayout program)).Agrees state
      (Vegas.EventGraph.Config.initial (graph := toEventGraph program)
        (encodeInputs state)).store :=
  ContextRefs.initial_agrees (outputLayout program) state _ fun _ => rfl

end Vegas.SourceProgram.EventLowering
