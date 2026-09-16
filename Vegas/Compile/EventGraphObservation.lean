/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphEvaluation

/-! # Source observations decoded from event-graph stores

The decoder is partial because an arbitrary graph observation need not contain
the fields required by a source decision point. It never manufactures a source
value: missing bindings, public cells, or resolved-publication fields produce
`none`. Foreign private cells remain intentionally hidden.
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

namespace PublicationRefs

/-- Restrict retained private-publication references past one context head. -/
def tail {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {name : VarId} {cell : CellTy Player L} {Γ : SourceCtx Player L}
    (publications : PublicationRefs layout ((name, cell) :: Γ)) :
    PublicationRefs layout Γ :=
  fun source => publications (.there source)

end PublicationRefs

/-- Read the public resolution status represented by a retained publication
reference. Literal pending requires no graph field. -/
def publicationStatus? {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} {payload : L.Ty}
    (publication : PublicationRef layout payload)
    (store : Vegas.EventGraph.Store layout) :
    Option (Interaction.Publication (L.Val payload)) :=
  match publication with
  | .pending => some .pending
  | .publication ref => ref.get? store |>.map Vegas.EventGraph.publicationOfResult

/-- Decode exactly the source observation visible to `who` at one compiler
prefix. The outer option records malformed or unavailable graph views. -/
def decodeObservation? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L} (who : Player) :
    {Γ : SourceCtx Player L} → ContextRefs layout Γ → PublicationRefs layout Γ →
      Vegas.EventGraph.Store layout → Option (SourceObservation L who Γ)
  | [], _, _, _ => some ⟨Env.empty (SourceObservationVal L)⟩
  | (name, .publicData payload) :: Γ, refs, publications, store => do
      let head ← (refs.get (HasVar.here :
        HasVar ((name, .publicData payload) :: Γ) name (.publicData payload))).get? store
      let tail ← decodeObservation? who refs.tail publications.tail store
      pure ⟨Env.cons head tail.cells⟩
  | (name, .publication payload) :: Γ, refs, publications, store => do
      let head ← (refs.get (HasVar.here :
        HasVar ((name, .publication payload) :: Γ) name (.publication payload))).get? store
      let tail ← decodeObservation? who refs.tail publications.tail store
      pure ⟨Env.cons head tail.cells⟩
  | (name, .privateData owner payload) :: Γ, refs, publications, store =>
      if _same : owner = who then do
        let binding ← (refs.get (HasVar.here :
          HasVar ((name, .privateData owner payload) :: Γ) name
            (.privateData owner payload))).get? store
        let status ← publicationStatus? (publications
          (HasVar.here : HasVar ((name, .privateData owner payload) :: Γ) name
            (.privateData owner payload))) store
        let tail ← decodeObservation? who refs.tail publications.tail store
        pure ⟨Env.cons (some ((BoundValue.resultEquiv _).symm binding, status)) tail.cells⟩
      else do
        let tail ← decodeObservation? who refs.tail publications.tail store
        pure ⟨Env.cons none tail.cells⟩

omit [DecidableEq Player] R in
@[simp] theorem publicationStatus?_pending {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} {payload : L.Ty}
    (store : Vegas.EventGraph.Store layout) :
    publicationStatus? (PublicationRef.pending : PublicationRef layout payload) store =
      some .pending := rfl

/-- Publication-status references are either literal pending or public result
fields, so player masking never changes their decoded status. -/
theorem publicationStatus?_playerStore {graph : Vegas.EventGraph Player L}
    {payload : L.Ty} (publication : PublicationRef graph.layout payload)
    (who : Player) (store : Vegas.EventGraph.Store graph.layout) :
    publicationStatus? publication (graph.playerStore who store) =
      publicationStatus? publication store := by
  cases publication with
  | pending => rfl
  | publication ref =>
      simp only [publicationStatus?]
      rw [ref.get?_playerStore who store (by trivial)]

/-- Decoding depends only on public fields and `who`'s own bindings. It can
therefore consume an actual masked player observation without recovering any
foreign private value. -/
theorem decodeObservation?_playerStore {graph : Vegas.EventGraph Player L}
    (who : Player) : {Γ : SourceCtx Player L} →
    (refs : ContextRefs graph.layout Γ) →
    (publications : PublicationRefs graph.layout Γ) →
    (store : Vegas.EventGraph.Store graph.layout) →
    decodeObservation? who refs publications (graph.playerStore who store) =
      decodeObservation? who refs publications store
  | [], _, _, _ => rfl
  | (name, .publicData payload) :: Γ, refs, publications, store => by
      rw [decodeObservation?, decodeObservation?]
      rw [(refs.get (HasVar.here :
        HasVar ((name, .publicData payload) :: Γ) name
          (.publicData payload))).get?_playerStore who store (by trivial)]
      rw [decodeObservation?_playerStore who refs.tail
        (PublicationRefs.tail publications) store]
  | (name, .publication payload) :: Γ, refs, publications, store => by
      rw [decodeObservation?, decodeObservation?]
      rw [(refs.get (HasVar.here :
        HasVar ((name, .publication payload) :: Γ) name
          (.publication payload))).get?_playerStore who store (by trivial)]
      rw [decodeObservation?_playerStore who refs.tail
        (PublicationRefs.tail publications) store]
  | (name, .privateData owner payload) :: Γ, refs, publications, store => by
      rw [decodeObservation?, decodeObservation?]
      by_cases same : owner = who
      · rw [dif_pos same, dif_pos same]
        rw [(refs.get (HasVar.here :
          HasVar ((name, .privateData owner payload) :: Γ) name
            (.privateData owner payload))).get?_playerStore who store (by
              change owner = who
              exact same)]
        rw [publicationStatus?_playerStore (publications HasVar.here) who store]
        rw [decodeObservation?_playerStore who refs.tail
          (PublicationRefs.tail publications) store]
      · rw [dif_neg same, dif_neg same]
        rw [decodeObservation?_playerStore who refs.tail
          (PublicationRefs.tail publications) store]

omit R in
/-- Typed context and publication agreement make the partial decoder exact. -/
theorem decodeObservation?_eq_some {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (publications : PublicationRefs layout Γ) (who : Player)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agrees state store)
    (publicationsAgree : publications.Agree state store) :
    decodeObservation? who refs publications store = some (sourceObserve who state) := by
  induction Γ with
  | nil =>
      apply congrArg some
      apply congrArg SourceObservation.mk
      funext name cell source
      nomatch source
  | cons entry Γ ih =>
      obtain ⟨name, cell⟩ := entry
      cases cell with
      | publicData payload =>
          have head := refsAgree (HasVar.here :
            HasVar ((name, .publicData payload) :: Γ) name (.publicData payload))
          have tailRefs : refs.tail.Agrees
              (fun _ _ source => state.get (.there source)) store := by
            intro readName readCell source
            exact refsAgree (.there source)
          have tailPublications : PublicationRefs.Agree
              (PublicationRefs.tail publications)
              (fun _ _ source => state.get (.there source)) store := by
            intro readOwner readPayload readName source
            exact publicationsAgree (.there source)
          rw [decodeObservation?, head, ih refs.tail (PublicationRefs.tail publications)
            (fun _ _ source => state.get (.there source)) tailRefs tailPublications]
          simp only [cellValue]
          apply congrArg some
          apply congrArg SourceObservation.mk
          funext readName readCell source
          cases source with
          | here => rfl
          | there source => cases readCell <;> rfl
      | publication payload =>
          have head := refsAgree (HasVar.here :
            HasVar ((name, .publication payload) :: Γ) name (.publication payload))
          have tailRefs : refs.tail.Agrees
              (fun _ _ source => state.get (.there source)) store := by
            intro readName readCell source
            exact refsAgree (.there source)
          have tailPublications : PublicationRefs.Agree
              (PublicationRefs.tail publications)
              (fun _ _ source => state.get (.there source)) store := by
            intro readOwner readPayload readName source
            exact publicationsAgree (.there source)
          rw [decodeObservation?, head, ih refs.tail (PublicationRefs.tail publications)
            (fun _ _ source => state.get (.there source)) tailRefs tailPublications]
          simp only [cellValue]
          apply congrArg some
          apply congrArg SourceObservation.mk
          funext readName readCell source
          cases source with
          | here => rfl
          | there source => cases readCell <;> rfl
      | privateData owner payload =>
          have tailRefs : refs.tail.Agrees
              (fun _ _ source => state.get (.there source)) store := by
            intro readName readCell source
            exact refsAgree (.there source)
          have tailPublications : PublicationRefs.Agree
              (PublicationRefs.tail publications)
              (fun _ _ source => state.get (.there source)) store := by
            intro readOwner readPayload readName source
            exact publicationsAgree (.there source)
          by_cases same : owner = who
          · have bindingStored := refsAgree (HasVar.here :
              HasVar ((name, .privateData owner payload) :: Γ) name
                (.privateData owner payload))
            have statusStored := publicationsAgree (HasVar.here :
              HasVar ((name, .privateData owner payload) :: Γ) name
                (.privateData owner payload))
            rw [decodeObservation?, dif_pos same, bindingStored]
            change publicationStatus? (publications HasVar.here) store =
              some (state.get HasVar.here).2 at statusStored
            rw [statusStored, ih refs.tail (PublicationRefs.tail publications)
              (fun _ _ source => state.get (.there source)) tailRefs tailPublications]
            simp only [cellValue]
            apply congrArg some
            apply congrArg SourceObservation.mk
            funext readName readCell source
            cases source with
            | here =>
                rw [Equiv.symm_apply_apply]
                generalize valueEq : state.get (HasVar.here :
                  HasVar ((name, .privateData owner payload) :: Γ) name
                    (.privateData owner payload)) = value at *
                change BoundValue (L.Val payload) ×
                  Interaction.Publication (L.Val payload) at value
                rcases value with ⟨binding, status⟩
                change (Env.cons (some (binding, status))
                    (sourceObserve who
                      (fun _ _ source => state.get (.there source))).cells).get
                    (HasVar.here : HasVar
                      ((name, .privateData owner payload) :: Γ) name
                      (.privateData owner payload)) =
                  if owner = who then some (state.get HasVar.here) else none
                simp [SourceObservationVal, CellVal, sourceObserve,
                  same, valueEq]
            | there source => cases readCell <;> rfl
          · rw [decodeObservation?, dif_neg same,
              ih refs.tail (PublicationRefs.tail publications)
                (fun _ _ source => state.get (.there source)) tailRefs tailPublications]
            apply congrArg some
            apply congrArg SourceObservation.mk
            funext readName readCell source
            cases source with
            | here =>
                change none = if owner = who then
                  some (state.get (HasVar.here :
                    HasVar ((name, .privateData owner payload) :: Γ) name
                      (.privateData owner payload))) else none
                simp [same]
            | there source => cases readCell <;> rfl

/-- Agreement with the semantic store also makes decoding exact on the actual
masked player store. -/
theorem decodeObservation?_playerStore_eq_some {graph : Vegas.EventGraph Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs graph.layout Γ)
    (publications : PublicationRefs graph.layout Γ) (who : Player)
    (state : State L Γ) (store : Vegas.EventGraph.Store graph.layout)
    (refsAgree : refs.Agrees state store)
    (publicationsAgree : publications.Agree state store) :
    decodeObservation? who refs publications (graph.playerStore who store) =
      some (sourceObserve who state) := by
  rw [decodeObservation?_playerStore]
  exact decodeObservation?_eq_some refs publications who state store
    refsAgree publicationsAgree

end Vegas.SourceProgram.EventLowering
