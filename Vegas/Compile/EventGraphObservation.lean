/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphEvaluation
import Vegas.EventGraph.Information
import Vegas.Foundation.PartialEnvironment

/-! # Source observations decoded from event-graph stores

The decoder is partial because an arbitrary graph observation need not contain
the fields required by a source decision point. It never manufactures a source
value: missing bindings, public cells, or publication fields produce `none`.
Foreign private cells remain intentionally hidden.
-/

noncomputable section

namespace Vegas

open SourceProgram

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
  | (name, .commitment owner payload) :: Γ, refs, store =>
      if _same : owner = who then do
        let binding ← (refs.get (HasVar.here :
          HasVar ((name, .commitment owner payload) :: Γ) name
            (.commitment owner payload))).get? store
        let tail ← decodeObservation? who refs.tail store
        pure ⟨Env.cons (some binding) tail.cells⟩
      else do
        let tail ← decodeObservation? who refs.tail store
        pure ⟨Env.cons none tail.cells⟩
  | (name, .privateInput owner payload) :: Γ, refs, store =>
      if _same : owner = who then do
        let binding ← (refs.get (HasVar.here :
          HasVar ((name, .privateInput owner payload) :: Γ) name
            (.privateInput owner payload))).get? store
        let tail ← decodeObservation? who refs.tail store
        pure ⟨Env.cons (some binding) tail.cells⟩
      else do
        let tail ← decodeObservation? who refs.tail store
        pure ⟨Env.cons none tail.cells⟩

/-- Source cells whose graph fields are visible to one player. -/
def cellVisibleTo (who : Player) : CellTy Player L → Prop
  | .publicData _ | .publication _ => True
  | .commitment owner _ | .privateInput owner _ => owner = who

instance (who : Player) (cell : CellTy Player L) : Decidable (cellVisibleTo who cell) := by
  cases cell <;> simp only [cellVisibleTo] <;> infer_instance

def readObservationCell? {Field : Type} {layout : Field → Vegas.EventGraph.EventField Player L}
    (who : Player) (store : Vegas.EventGraph.Store layout) :
    {cell : CellTy Player L} → Vegas.EventGraph.FieldRef layout (cellField cell) →
      Option (SourceObservationVal L cell)
  | .publicData _, ref => ref.get? store
  | .publication _, ref => ref.get? store
  | .commitment owner _, ref =>
      if owner = who then (ref.get? store).map some else some none
  | .privateInput owner _, ref =>
      if owner = who then (ref.get? store).map some else some none

def collectObservation? {Field : Type} {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (who : Player) (refs : ContextRefs layout Γ)
    (store : Vegas.EventGraph.Store layout) : Option (SourceObservation L who Γ) :=
  (PartialEnvironment.collect? (fun _ _ => True) Γ
    (fun source _ => readObservationCell? who store (refs.get source))).map
      (fun get => ⟨fun _ _ source => get source trivial⟩)

omit R in
theorem decodeObservation?_cons {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {name : VarId} {cell : CellTy Player L}
    (who : Player) (refs : ContextRefs layout ((name, cell) :: Γ))
    (store : Vegas.EventGraph.Store layout) :
    decodeObservation? who refs store =
      (readObservationCell? who store (refs.get HasVar.here)).bind fun head =>
        (decodeObservation? who refs.tail store).map fun tail =>
          ⟨Env.cons head tail.cells⟩ := by
  cases cell with
  | publicData payload | publication payload =>
      cases head : (refs.get HasVar.here).get? store <;>
        cases tail : decodeObservation? who refs.tail store <;>
          simp [decodeObservation?, readObservationCell?, head, tail, Option.map, Option.bind]
  | commitment owner payload | privateInput owner payload =>
      by_cases same : owner = who
      all_goals
        cases head : (refs.get HasVar.here).get? store <;>
          cases tail : decodeObservation? who refs.tail store <;>
            simp [decodeObservation?, readObservationCell?, same, head, tail,
              Option.map, Option.bind]

omit R in
/-- Decoding equals typed collection at every partial store, including missing
visible fields and intentionally hidden private cells. -/
theorem decodeObservation?_eq_collect {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    (who : Player) (refs : ContextRefs layout Γ) (store : Vegas.EventGraph.Store layout) :
    decodeObservation? who refs store = collectObservation? who refs store := by
  induction Γ with
  | nil =>
      apply congrArg some
      apply congrArg SourceObservation.mk
      funext name cell source
      nomatch source
  | cons entry Γ ih =>
      obtain ⟨name, cell⟩ := entry
      rw [decodeObservation?_cons, ih refs.tail]
      cases head : readObservationCell? who store (refs.get HasVar.here) <;>
        cases tail : PartialEnvironment.collect? (fun _ _ => True) Γ
            (fun source _ => readObservationCell? who store (refs.tail.get source)) <;>
          simp only [ContextRefs.tail] at tail <;>
          simp only [collectObservation?, PartialEnvironment.collect?, ContextRefs.tail, head, tail,
            Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind, ↓reduceDIte,
            Option.some.injEq, SourceObservation.mk.injEq]
      all_goals
        funext readName readCell source
        cases source <;> rfl

omit R in
theorem decodeObservation?_congr_of_visible {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    (who : Player) (refs : ContextRefs layout Γ) (left right : Vegas.EventGraph.Store layout)
    (agree : ∀ {name cell} (source : HasVar Γ name cell), cellVisibleTo who cell →
      (refs.get source).get? left = (refs.get source).get? right) :
    decodeObservation? who refs left = decodeObservation? who refs right := by
  rw [decodeObservation?_eq_collect, decodeObservation?_eq_collect]
  unfold collectObservation?
  congr 1
  apply PartialEnvironment.congr
  intro name cell source _
  cases cell with
  | publicData payload | publication payload => exact agree source trivial
  | commitment owner payload | privateInput owner payload =>
      by_cases same : owner = who
      · simp only [readObservationCell?, ite_eq_left same]
        rw [agree source same]
      · simp [readObservationCell?, same]

/-- Decoding depends only on public fields and `who`'s own inputs and bindings. It can
therefore consume an actual masked player observation without recovering any
foreign private value. -/
theorem decodeObservation?_playerStore {graph : Vegas.EventGraph Player L}
    (who : Player) : {Γ : SourceCtx Player L} →
    (refs : ContextRefs graph.layout Γ) →
    (store : Vegas.EventGraph.Store graph.layout) →
    decodeObservation? who refs (graph.playerStore who store) =
      decodeObservation? who refs store := by
  intro Γ refs store
  apply decodeObservation?_congr_of_visible
  intro name cell source visible
  apply (refs.get source).get?_playerStore
  cases cell with
  | publicData payload | publication payload => trivial
  | commitment owner payload | privateInput owner payload => exact visible

omit R in
/-- Agreement on the cells a player can see makes that player's decoder exact:
the decoder never reads a cell hidden from the player. -/
theorem decodeObservation?_eq_some_of_visible {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ) (who : Player)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : ∀ {name cell} (source : HasVar Γ name cell), cellVisibleTo who cell →
      (refs.get source).get? store = some (cellValue (state.get source))) :
    decodeObservation? who refs store = some (sourceObserve who state) := by
  let values : ∀ {name cell}, HasVar Γ name cell → True → SourceObservationVal L cell :=
    fun source _ => (sourceObserve who state).cells.get source
  have complete : ∀ {name cell} (source : HasVar Γ name cell) (read : True),
      readObservationCell? who store (refs.get source) = some (values source read) := by
    intro name cell source _
    cases cell with
    | publicData payload | publication payload => exact refsAgree source trivial
    | commitment owner payload | privateInput owner payload =>
        by_cases same : owner = who
        · simp [readObservationCell?, values, sourceObserve, Env.get, same, refsAgree source same,
            cellValue, Option.map]
        · simp [readObservationCell?, values, sourceObserve, Env.get, same]
  rw [decodeObservation?_eq_collect]
  unfold collectObservation?
  rw [PartialEnvironment.of_some _ Γ _ values complete]
  rfl

omit R in
/-- Typed context agreement makes the partial decoder exact. -/
theorem decodeObservation?_eq_some {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ) (who : Player)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agrees state store) :
    decodeObservation? who refs store = some (sourceObserve who state) := by
  exact decodeObservation?_eq_some_of_visible refs who state store
    (fun source _ => refsAgree source)

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

end Vegas
