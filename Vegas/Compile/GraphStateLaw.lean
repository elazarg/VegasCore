/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphLayout

/-! # State extension laws for the immutable graph layout -/

noncomputable section
namespace Vegas.SourceProgram

open Interaction

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]

@[simp] theorem decodeState_sample {Γ : SourceCtx Player L} {name : VarId}
    {payload : L.Ty} (map : PublicationMap (R := R) Γ)
    (env : VEnv L (graphCtx Γ)) (value : L.Val payload) :
    decodeState (weakenMap map (name := name) (cell := .publicData payload))
      (VEnv.cons value env) =
      Env.cons (τ := CellTy.publicData payload) value (decodeState map env) := by
  funext readName cell read
  cases read with
  | here => rfl
  | there read =>
      cases cell <;> simp [decodeState, fieldRef, weakenMap, Env.cons]

@[simp] theorem decodeState_bind {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (map : PublicationMap (R := R) Γ)
    (env : VEnv L (graphCtx Γ)) (value : BoundValue (L.Val payload)) :
    decodeState (weakenMap map (name := name) (cell := .privateData owner payload))
      (VEnv.cons ((R.valueEquiv payload).symm (BoundValue.resultEquiv _ value)) env) =
      Env.cons (value, Publication.pending) (decodeState map env) := by
  funext readName cell read
  cases read with
  | here => simp [decodeState, fieldRef, weakenMap, Graph.GuardRead.get, Env.cons]
  | there read =>
      cases cell <;> simp [decodeState, fieldRef, weakenMap, Env.cons]

@[simp] theorem decodeState_publication_cons {Γ : SourceCtx Player L} {name : VarId}
    {payload : L.Ty} (map : PublicationMap (R := R) Γ)
    (env : VEnv L (graphCtx Γ)) (value : PublicationResult (L.Val payload)) :
    decodeState (weakenMap map (name := name) (cell := .publication payload))
      (VEnv.cons ((R.valueEquiv payload).symm value) env) =
      Env.cons value (decodeState map env) := by
  funext readName cell read
  cases read with
  | here => simp [decodeState, fieldRef, Env.cons]
  | there read =>
      cases cell <;> simp [decodeState, fieldRef, weakenMap, Env.cons]

/-- Initial private inputs are represented without embedding them in graph
code. Pending statuses are reconstructed from the initial publication map. -/
theorem decodeState_encodeState_initial {Γ : SourceCtx Player L}
    (state : State L Γ) (pending : PrivatePending state) :
    decodeState (initialMap (R := R)) (encodeState state) = state := by
  induction Γ with
  | nil =>
      funext name cell read
      nomatch read
  | cons entry tail ih =>
      obtain ⟨name, cell⟩ := entry
      let rest : State L tail := fun _ _ h => state.get (.there h)
      have map_eq : (initialMap : PublicationMap (R := R) ((name, cell) :: tail)) =
          (weakenMap (initialMap (R := R) (Γ := tail)) :
            PublicationMap (R := R) ((name, cell) :: tail)) := by
        funext readOwner readPayload readName read
        cases cell <;> cases read <;> rfl
      rw [map_eq]
      cases cell with
      | publicData payload =>
          change decodeState (weakenMap (initialMap (R := R))
            (name := name) (cell := .publicData payload))
            (VEnv.cons (state.get .here) (encodeState rest)) = state
          rw [decodeState_sample, ih rest pending]
          funext readName cell read
          cases read <;> rfl
      | publication payload =>
          change decodeState (weakenMap (initialMap (R := R))
            (name := name) (cell := .publication payload))
            (VEnv.cons ((R.valueEquiv payload).symm (state.get .here))
              (encodeState rest)) = state
          rw [decodeState_publication_cons, ih rest pending]
          funext readName cell read
          cases read <;> rfl
      | privateData owner payload =>
          change decodeState (weakenMap (initialMap (R := R))
            (name := name) (cell := .privateData owner payload))
            (VEnv.cons ((R.valueEquiv payload).symm
              (BoundValue.resultEquiv _ (state.get .here).1)) (encodeState rest)) = state
          rw [decodeState_bind, ih rest pending.2]
          funext readName cell read
          cases read with
          | here => exact Prod.ext rfl pending.1.symm
          | there read => rfl

end Vegas.SourceProgram
