/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.Compile.EventGraphEvaluation
import Vegas.EventGraph.Execution

/-! # Initial source values in event-graph stores

The input encoding preserves each source cell's typed binding or public value.
Agreement is independent of event outputs, so it also holds after execution has
started. Publication status for private cells is a separate compiler invariant.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

omit [DecidableEq Player] R in
/-- Every private cell in a `PrivatePending` source state has pending public
status, not merely the private cell at the head of the context. -/
theorem PrivatePending.get_private {Γ : SourceCtx Player L}
    (state : State L Γ) (pending : PrivatePending state)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (source : HasVar Γ name (.privateData owner payload)) :
    (state.get source).2 = Interaction.Publication.pending := by
  induction Γ with
  | nil => nomatch source
  | cons entry tail ih =>
      obtain ⟨headName, headCell⟩ := entry
      let tailState : State L tail := fun _ _ read => state.get (.there read)
      cases headCell with
      | publicData headPayload =>
          cases source with
          | there source => exact ih tailState pending source
      | privateData headOwner headPayload =>
          cases source with
          | here => exact pending.1
          | there source => exact ih tailState pending.2 source
      | publication headPayload =>
          cases source with
          | there source => exact ih tailState pending source

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
the complete initial source state in both its immutable-cell and retained
publication views. -/
theorem initialConfig_agrees {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (state : State L Γ) (pending : PrivatePending state) :
    let config := Vegas.EventGraph.Config.initial
      (graph := toEventGraph program unique) (encodeInputs state)
    (ContextRefs.initial Γ (outputLayout program)).Agrees state config.store ∧
      PublicationRefs.Agree
        (initialPublications (Field := Vegas.EventGraph.FieldId Γ.length
          (eventCount program))) state config.store := by
  dsimp only
  constructor
  · apply ContextRefs.initial_agrees (outputLayout program) state
    intro input
    rfl
  · apply initialPublications_agree state
    intro owner payload name source
    exact PrivatePending.get_private state pending source

end Vegas.SourceProgram.EventLowering
