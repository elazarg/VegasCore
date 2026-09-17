/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Safety
import Vegas.EventGraph.Basic

/-! # Source layouts for dependency-driven event graphs

This module assigns graph inputs and source-ranked event outputs without
erasing the source payload carried by a binding or publication.  It also
provides the typed reference environments used by the executable lowerer.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- The event-graph field corresponding to one source cell.  In particular,
the original payload remains present in bindings and publications even when
`IExpr.ResultTypes.result` is not injective. -/
def cellField : CellTy Player L → Vegas.EventGraph.EventField Player L
  | .publicData payload => .publicData payload
  | .privateData owner payload => .binding owner payload
  | .publication payload => .publication payload

/-- Initial source cells are graph inputs in their context order. -/
def inputLayout : (Γ : SourceCtx Player L) →
    Fin Γ.length → Vegas.EventGraph.EventField Player L
  | [], input => nomatch input
  | (_, cell) :: Γ, input => Fin.cases (cellField cell) (inputLayout Γ) input

/-- The input position denoted by a typed source-context membership proof. -/
def inputId : {Γ : SourceCtx Player L} → {name : VarId} → {cell : CellTy Player L} →
    HasVar Γ name cell → Fin Γ.length
  | _ :: _, _, _, .here => 0
  | _ :: _, _, _, .there source => Fin.succ (inputId source)

omit [DecidableEq Player] R in
@[simp] theorem inputLayout_inputId {Γ : SourceCtx Player L}
    {name : VarId} {cell : CellTy Player L} (source : HasVar Γ name cell) :
    inputLayout Γ (inputId source) = cellField cell := by
  induction source with
  | here => rfl
  | there source ih => exact ih

/-- Number of executable source operations.  `ret` contributes terminal
readout metadata, not an executable event. -/
def eventCount : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    SourceProgram Player L Γ openNames → Nat
  | _, _, .ret _ => 0
  | _, _, .sample _ _ _ next => (eventCount next).succ
  | _, _, .commit _ _ _ _ next => (eventCount next).succ
  | _, _, .reveal _ _ _ _ _ _ next => (eventCount next).succ

/-- One output per source operation, numbered in source order. -/
def outputLayout : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
      Fin (eventCount program) → Vegas.EventGraph.EventField Player L
  | _, _, .ret _, event => nomatch event
  | _, _, .sample (payload := payload) _ _ _ next, event =>
      Fin.cases (.publicData payload) (outputLayout next) event
  | _, _, .commit (payload := payload) _ owner _ _ next, event =>
      Fin.cases (.binding owner payload) (outputLayout next) event
  | _, _, .reveal (payload := payload) _ _ _ _ _ _ next, event =>
      Fin.cases (.publication payload) (outputLayout next) event

/-- Typed references for every cell in one source prefix. -/
structure ContextRefs {Field : Type}
    (layout : Field → Vegas.EventGraph.EventField Player L)
    (Γ : SourceCtx Player L) where
  get : ∀ {name cell}, HasVar Γ name cell →
    Vegas.EventGraph.FieldRef layout (cellField cell)

namespace ContextRefs

/-- Extend a source reference environment with a newly produced field. -/
def cons {Field : Type} {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {name : VarId} {cell : CellTy Player L}
    (head : Vegas.EventGraph.FieldRef layout (cellField cell))
    (tail : ContextRefs layout Γ) : ContextRefs layout ((name, cell) :: Γ) where
  get source := match source with
    | .here => head
    | .there source => tail.get source

/-- Initial source references target the input half of a combined graph
layout; the output layout is arbitrary here because no initial cell refers to
an event output. -/
def initial (Γ : SourceCtx Player L) {eventCount : Nat}
    (outputs : Fin eventCount → Vegas.EventGraph.EventField Player L) :
    ContextRefs (Vegas.EventGraph.fieldLayout (inputLayout Γ) outputs) Γ where
  get source :=
    { field := .inl (inputId source)
      layout_eq := inputLayout_inputId source }

end ContextRefs

/-- Encode a concrete initial source state as graph inputs. A private input is
encoded by its immutable binding. -/
def encodeInputs : {Γ : SourceCtx Player L} → State L Γ →
    (input : Fin Γ.length) → (inputLayout Γ input).Value
  | [], _, input => nomatch input
  | (_, .publicData _) :: _, state, input => Fin.cases
      (state.get .here)
      (encodeInputs (fun _ _ source => state.get (.there source))) input
  | (_, .privateData _ _payload) :: _, state, input => Fin.cases
      (state.get .here)
      (encodeInputs (fun _ _ source => state.get (.there source))) input
  | (_, .publication _) :: _, state, input => Fin.cases
      (state.get .here)
      (encodeInputs (fun _ _ source => state.get (.there source))) input

end Vegas.SourceProgram.EventLowering
