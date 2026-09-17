/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphEvaluation

/-! # Source observations decoded from event-graph stores

The decoder is partial because an arbitrary graph observation need not contain
the fields required by a source decision point. It never manufactures a source
value: missing bindings, public cells, or publication fields produce `none`.
Foreign private cells remain intentionally hidden.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

namespace ContextRefs

/-- Restrict source-cell references past one context head. -/
def tail {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {name : VarId} {cell : CellTy Player L} {Γ : SourceCtx Player L}
    (refs : ContextRefs layout ((name, cell) :: Γ)) : ContextRefs layout Γ where
  get source := refs.get (.there source)

end ContextRefs

/-- Decode exactly the source observation visible to `who` at one compiler
prefix. The outer option records malformed or unavailable graph views. -/
def decodeObservation? {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} (who : Player) :
    {Γ : SourceCtx Player L} → ContextRefs layout Γ →
      Vegas.EventGraph.Store layout → Option (SourceObservation L who Γ)
  | [], _, _ => some ⟨Env.empty (SourceObservationVal L)⟩
  | (name, .publicData payload) :: Γ, refs, store => do
      let head ← (refs.get (HasVar.here :
        HasVar ((name, .publicData payload) :: Γ) name (.publicData payload))).get? store
      let tail ← decodeObservation? who refs.tail store
      pure ⟨Env.cons head tail.cells⟩
  | (name, .publication payload) :: Γ, refs, store => do
      let head ← (refs.get (HasVar.here :
        HasVar ((name, .publication payload) :: Γ) name (.publication payload))).get? store
      let tail ← decodeObservation? who refs.tail store
      pure ⟨Env.cons head tail.cells⟩
  | (name, .privateData owner payload) :: Γ, refs, store =>
      if _same : owner = who then do
        let binding ← (refs.get (HasVar.here :
          HasVar ((name, .privateData owner payload) :: Γ) name
            (.privateData owner payload))).get? store
        let tail ← decodeObservation? who refs.tail store
        pure ⟨Env.cons (some binding) tail.cells⟩
      else do
        let tail ← decodeObservation? who refs.tail store
        pure ⟨Env.cons none tail.cells⟩

/-- Decoding depends only on public fields and `who`'s own bindings. It can
therefore consume an actual masked player observation without recovering any
foreign private value. -/
theorem decodeObservation?_playerStore {graph : Vegas.EventGraph Player L}
    (who : Player) : {Γ : SourceCtx Player L} →
    (refs : ContextRefs graph.layout Γ) →
    (store : Vegas.EventGraph.Store graph.layout) →
    decodeObservation? who refs (graph.playerStore who store) =
      decodeObservation? who refs store
  | [], _, _ => rfl
  | (name, .publicData payload) :: Γ, refs, store => by
      rw [decodeObservation?, decodeObservation?]
      rw [(refs.get (HasVar.here :
        HasVar ((name, .publicData payload) :: Γ) name
          (.publicData payload))).get?_playerStore who store (by trivial)]
      rw [decodeObservation?_playerStore who refs.tail store]
  | (name, .publication payload) :: Γ, refs, store => by
      rw [decodeObservation?, decodeObservation?]
      rw [(refs.get (HasVar.here :
        HasVar ((name, .publication payload) :: Γ) name
          (.publication payload))).get?_playerStore who store (by trivial)]
      rw [decodeObservation?_playerStore who refs.tail store]
  | (name, .privateData owner payload) :: Γ, refs, store => by
      rw [decodeObservation?, decodeObservation?]
      by_cases same : owner = who
      · rw [dif_pos same, dif_pos same]
        rw [(refs.get (HasVar.here :
          HasVar ((name, .privateData owner payload) :: Γ) name
            (.privateData owner payload))).get?_playerStore who store (by
              change owner = who
              exact same)]
        rw [decodeObservation?_playerStore who refs.tail store]
      · rw [dif_neg same, dif_neg same]
        rw [decodeObservation?_playerStore who refs.tail store]

omit R in
/-- Typed context agreement makes the partial decoder exact. -/
theorem decodeObservation?_eq_some {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ) (who : Player)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agrees state store) :
    decodeObservation? who refs store = some (sourceObserve who state) := by
  induction Γ with
  | nil =>
      apply congrArg some
      apply congrArg SourceObservation.mk
      funext name cell source
      nomatch source
  | cons entry Γ ih =>
      obtain ⟨name, cell⟩ := entry
      have tail := ih refs.tail (fun _ _ source => state.get (.there source))
        fun source => refsAgree (.there source)
      have head := refsAgree (HasVar.here : HasVar ((name, cell) :: Γ) name cell)
      cases cell with
      | publicData payload =>
          rw [decodeObservation?, head, tail]
          apply congrArg some
          apply congrArg SourceObservation.mk
          funext readName readCell source
          cases source with
          | here => rfl
          | there source => cases readCell <;> rfl
      | publication payload =>
          rw [decodeObservation?, head, tail]
          apply congrArg some
          apply congrArg SourceObservation.mk
          funext readName readCell source
          cases source with
          | here => rfl
          | there source => cases readCell <;> rfl
      | privateData owner payload =>
          by_cases same : owner = who
          · rw [decodeObservation?, dif_pos same, head, tail]
            apply congrArg some
            apply congrArg SourceObservation.mk
            funext readName readCell source
            cases source with
            | here =>
                change some (state.get HasVar.here) =
                  if owner = who then some (state.get HasVar.here) else none
                simp [same]
            | there source => cases readCell <;> rfl
          · rw [decodeObservation?, dif_neg same, tail]
            apply congrArg some
            apply congrArg SourceObservation.mk
            funext readName readCell source
            cases source with
            | here =>
                change none = if owner = who then some (state.get HasVar.here) else none
                simp [same]
            | there source => cases readCell <;> rfl

/-- Agreement with the semantic store also makes decoding exact on the actual
masked player store. -/
theorem decodeObservation?_playerStore_eq_some {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs graph.layout Γ) (who : Player)
    (state : State L Γ) (store : Vegas.EventGraph.Store graph.layout)
    (refsAgree : refs.Agrees state store) :
    decodeObservation? who refs (graph.playerStore who store) =
      some (sourceObserve who state) := by
  rw [decodeObservation?_playerStore]
  exact decodeObservation?_eq_some refs who state store refsAgree

end Vegas.SourceProgram.EventLowering
