/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphReadout

/-! # Canonical terminal references along actual compiler suffix traversal

Node-table agreement alone imposes no terminal reference condition at a return.
This independent compiler invariant follows the syntax and records the actual
terminal context and cell references, without constraining source registries.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeOpen)

/-- Traversing a compiled source prefix retains its canonical typed terminal
readout. This concerns only syntax and references, not mutable guard registries. -/
structure CompiledReadoutSuffix {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program) : Prop where
  contextEq : program.terminalCtx = whole.terminalCtx
  refsEq : cast (congrArg (ContextRefs (graphLayout whole)) contextEq)
    (terminalRefsWith program refs embedding.ref) = terminalRefs whole

/-- Initial compilation uses the actual whole-program terminal references. -/
theorem CompiledReadoutSuffix.initial :
    CompiledReadoutSuffix whole whole
      (ContextRefs.initial wholeΓ (outputLayout whole)) (outputEmbedding whole) :=
  ⟨rfl, rfl⟩

theorem CompiledReadoutSuffix.sampleTail
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.sample name fresh law next))
    (aligned : CompiledReadoutSuffix whole (.sample name fresh law next) refs embedding) :
    let head : Fin (eventCount (.sample name fresh law next)) := ⟨0, by simp [eventCount]⟩
    let result : EventGraph.FieldRef (graphLayout whole) (.publicData payload) := by
      simpa [head, outputLayout, eventCount] using embedding.ref head
    CompiledReadoutSuffix whole next (refs.cons result)
      (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) := by
  exact ⟨aligned.contextEq, aligned.refsEq⟩

theorem CompiledReadoutSuffix.commitTail
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard next))
    (aligned : CompiledReadoutSuffix whole (.commit name owner fresh guard next) refs embedding) :
    let head : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let result : EventGraph.FieldRef (graphLayout whole) (.binding owner payload) := by
      simpa [head, outputLayout, eventCount] using embedding.ref head
    CompiledReadoutSuffix whole next (refs.cons result)
      (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) := by
  exact ⟨aligned.contextEq, aligned.refsEq⟩

theorem CompiledReadoutSuffix.revealTail
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.reveal published owner name fresh selected unresolved next))
    (aligned : CompiledReadoutSuffix whole
      (.reveal published owner name fresh selected unresolved next) refs embedding) :
    let head : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let result : EventGraph.FieldRef (graphLayout whole) (.publication payload) := by
      simpa [head, outputLayout, eventCount] using embedding.ref head
    CompiledReadoutSuffix whole next (refs.cons result)
      (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) := by
  exact ⟨aligned.contextEq, aligned.refsEq⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem decodeState?_cast_context {Field : Type}
    {layout : Field → EventGraph.EventField Player L} {Γ Δ : SourceCtx Player L}
    (same : Γ = Δ) (refs : ContextRefs layout Γ) (store : EventGraph.Store layout) :
    decodeState? (cast (congrArg (ContextRefs layout) same) refs) store =
      cast (congrArg (fun context => Option (State L context)) same) (decodeState? refs store) := by
  cases same
  rfl

/-- The canonical terminal decoder is the residual decoder with its actual
terminal context transported, independently of source guard bookkeeping. -/
theorem CompiledReadoutSuffix.decode
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (aligned : CompiledReadoutSuffix whole program refs embedding)
    (store : EventGraph.Store (graphLayout whole)) :
    decodeState? (terminalRefs whole) store =
      cast (congrArg (fun context => Option (State L context)) aligned.contextEq)
        (decodeState? (terminalRefsWith program refs embedding.ref) store) := by
  rw [← aligned.refsEq]
  exact decodeState?_cast_context aligned.contextEq _ store

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem cast_some_context {Γ Δ : SourceCtx Player L} (same : Γ = Δ) (state : State L Γ) :
    cast (congrArg (fun context => Option (State L context)) same) (some state) =
      some (cast (congrArg (State L) same) state) := by
  cases same
  rfl

/-- Actual return-state agreement determines the complete canonical native
readout; accepted or excluded guard registries need not match a static decoder. -/
theorem CompiledReadoutSuffix.decode_ret
    {Γ : SourceCtx Player L} (payoffs : List (Player × L.Expr (SourcePublicCtx L Γ) L.int))
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (.ret payoffs))
    (aligned : CompiledReadoutSuffix whole (.ret payoffs) refs embedding)
    (terminal : State L Γ) (store : EventGraph.Store (graphLayout whole))
    (agrees : refs.Agrees terminal store) :
    decodeState? (terminalRefs whole) store =
      some (cast (congrArg (State L) aligned.contextEq) terminal) := by
  rw [aligned.decode whole (.ret payoffs) refs embedding store]
  change cast (congrArg (fun context => Option (State L context)) aligned.contextEq)
    (decodeState? refs store) = _
  rw [decodeState?_eq_some refs terminal store agrees]
  exact cast_some_context aligned.contextEq terminal

end Vegas
