/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphObservation
import Vegas.Compile.EventGraphSuffix
import Vegas.EventGraph.CanonicalStep

/-! # Constructive encoding of source observations

Source observations determine exactly the public fields and the observing
player's private bindings.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Source cells whose graph fields are visible to one player. -/
def cellVisibleTo (who : Player) : CellTy Player L → Prop
  | .publicData _ | .publication _ => True
  | .privateData owner _ => owner = who

instance (who : Player) (cell : CellTy Player L) : Decidable (cellVisibleTo who cell) := by
  cases cell <;> simp only [cellVisibleTo] <;> infer_instance

/-- Write one value through a typed graph-field reference. -/
private def writeField {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {kind : Vegas.EventGraph.EventField Player L}
    (ref : Vegas.EventGraph.FieldRef layout kind) (value : kind.Value)
    (store : Vegas.EventGraph.Store layout) : Vegas.EventGraph.Store layout :=
  Function.update store ref.field
    (some (cast (congrArg Vegas.EventGraph.EventField.Value ref.layout_eq.symm) value))

/-- Restrict an observation past its context head. -/
private def observationTail {name : VarId} {cell : CellTy Player L}
    {Γ : SourceCtx Player L} {who : Player}
    (observation : SourceObservation L who ((name, cell) :: Γ)) :
    SourceObservation L who Γ :=
  ⟨fun _ _ source => observation.cells.get (.there source)⟩

omit R in
private theorem observationTail_sourceObserve {name : VarId}
    {cell : CellTy Player L} {Γ : SourceCtx Player L} (who : Player)
    (state : State L ((name, cell) :: Γ)) :
    observationTail (sourceObserve who state) =
      sourceObserve who (fun _ _ source => state.get (.there source)) := by
  apply congrArg SourceObservation.mk
  funext readName readCell source
  cases readCell <;> rfl

/-- Construct the graph store represented by a source observation. Public
cells are written unconditionally, an own private binding is written exactly
when it is present, and a foreign private binding remains absent. -/
def encodeObservationStore {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L} (who : Player) :
    {Γ : SourceCtx Player L} → ContextRefs layout Γ → SourceObservation L who Γ →
      Vegas.EventGraph.Store layout
  | [], _, _ => fun _ => none
  | (name, .publicData payload) :: Γ, refs, observation =>
      writeField (refs.get (HasVar.here :
        HasVar ((name, .publicData payload) :: Γ) name (.publicData payload)))
        (observation.cells.get HasVar.here)
        (encodeObservationStore who refs.tail (observationTail observation))
  | (name, .publication payload) :: Γ, refs, observation =>
      writeField (refs.get (HasVar.here :
        HasVar ((name, .publication payload) :: Γ) name (.publication payload)))
        (observation.cells.get HasVar.here)
        (encodeObservationStore who refs.tail (observationTail observation))
  | (name, .privateData owner payload) :: Γ, refs, observation =>
      let tail := encodeObservationStore who refs.tail (observationTail observation)
      if _same : owner = who then
        match observation.cells.get (HasVar.here :
          HasVar ((name, .privateData owner payload) :: Γ) name
            (.privateData owner payload)) with
        | none => tail
        | some value => writeField (refs.get HasVar.here) value tail
      else tail

/-- A reference environment covers a visible graph field when some visible
source cell names that exact field. -/
def ContextRefs.CoversVisible {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (who : Player) (field : Field) : Prop :=
  ∃ name cell, ∃ source : HasVar Γ name cell,
    cellVisibleTo who cell ∧ (refs.get source).field = field

omit [DecidableEq Player] R in
private theorem writeField_of_ne {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {kind : Vegas.EventGraph.EventField Player L}
    (ref : Vegas.EventGraph.FieldRef layout kind) (value : kind.Value)
    (tail : Vegas.EventGraph.Store layout) (field : Field)
    (different : field ≠ ref.field) :
    writeField ref value tail field = tail field := by
  simp [writeField, Function.update, different]

omit [DecidableEq Player] R in
private theorem writeField_eq_of_get? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {kind : Vegas.EventGraph.EventField Player L}
    (ref : Vegas.EventGraph.FieldRef layout kind) (value : kind.Value)
    (tail store : Vegas.EventGraph.Store layout)
    (stored : ref.get? store = some value) :
    writeField ref value tail ref.field = store ref.field := by
  cases ref with
  | mk field layoutEq =>
      cases layoutEq
      simpa [Vegas.EventGraph.FieldRef.get?, writeField, Function.update] using stored.symm

/-- Pointwise form of observation-store correctness. Only the queried field
needs a coverage premise, which makes the structural induction exact. -/
private theorem encodeObservationStore_apply_eq_playerStore
    {graph : Vegas.EventGraph Player L} (who : Player) :
    {Γ : SourceCtx Player L} →
    (refs : ContextRefs graph.layout Γ) → (state : State L Γ) →
    (store : Vegas.EventGraph.Store graph.layout) →
    (field : graph.Field) → refs.Agrees state store →
    (¬ refs.CoversVisible who field → graph.playerStore who store field = none) →
    encodeObservationStore who refs (sourceObserve who state) field =
      graph.playerStore who store field
  | [], refs, state, store, field, _, coverage => by
      apply (coverage ?_).symm
      rintro ⟨name, cell, source, _, _⟩
      nomatch source
  | (name, .publicData payload) :: Γ, refs, state, store, field, agree,
      coverage => by
      let source : HasVar ((name, .publicData payload) :: Γ) name
          (.publicData payload) := .here
      let headRef := refs.get source
      let tailState : State L Γ := fun _ _ read => state.get (.there read)
      rw [encodeObservationStore, observationTail_sourceObserve]
      change writeField headRef (state.get source)
          (encodeObservationStore who refs.tail (sourceObserve who tailState)) field = _
      by_cases same : field = headRef.field
      · subst field
        have visible : graph.fieldVisibleTo who headRef.field := by
          change (graph.layout headRef.field).VisibleTo who
          rw [headRef.layout_eq]
          trivial
        rw [graph.playerStore_of_visible who store headRef.field visible]
        exact writeField_eq_of_get? headRef (state.get source) _ store (agree source)
      · rw [writeField_of_ne headRef (state.get source) _ field same]
        apply encodeObservationStore_apply_eq_playerStore who refs.tail tailState store
          field (fun read => agree (.there read))
        intro absent
        apply coverage
        rintro ⟨readName, cell, read, visible, found⟩
        cases read with
        | here => exact same found.symm
        | there read => exact absent ⟨readName, cell, read, visible, found⟩
  | (name, .publication payload) :: Γ, refs, state, store, field, agree,
      coverage => by
      let source : HasVar ((name, .publication payload) :: Γ) name
          (.publication payload) := .here
      let headRef := refs.get source
      let tailState : State L Γ := fun _ _ read => state.get (.there read)
      rw [encodeObservationStore, observationTail_sourceObserve]
      change writeField headRef (state.get source)
          (encodeObservationStore who refs.tail (sourceObserve who tailState)) field = _
      by_cases same : field = headRef.field
      · subst field
        have visible : graph.fieldVisibleTo who headRef.field := by
          change (graph.layout headRef.field).VisibleTo who
          rw [headRef.layout_eq]
          trivial
        rw [graph.playerStore_of_visible who store headRef.field visible]
        exact writeField_eq_of_get? headRef (state.get source) _ store (agree source)
      · rw [writeField_of_ne headRef (state.get source) _ field same]
        apply encodeObservationStore_apply_eq_playerStore who refs.tail tailState store
          field (fun read => agree (.there read))
        intro absent
        apply coverage
        rintro ⟨readName, cell, read, visible, found⟩
        cases read with
        | here => exact same found.symm
        | there read => exact absent ⟨readName, cell, read, visible, found⟩
  | (name, .privateData owner payload) :: Γ, refs, state, store, field, agree,
      coverage => by
      let source : HasVar ((name, .privateData owner payload) :: Γ) name
          (.privateData owner payload) := .here
      let headRef := refs.get source
      let tailState : State L Γ := fun _ _ read => state.get (.there read)
      rw [encodeObservationStore]
      by_cases ownerEq : owner = who
      · simp only [ownerEq, ↓reduceDIte]
        have headObserved : (sourceObserve who state).cells.get source =
            some (state.get source) := by
          change (if owner = who then some (state.get source) else none) = _
          simp [ownerEq]
        rw [headObserved, observationTail_sourceObserve]
        change writeField headRef (state.get source)
            (encodeObservationStore who refs.tail (sourceObserve who tailState)) field = _
        by_cases same : field = headRef.field
        · subst field
          have visible : graph.fieldVisibleTo who headRef.field := by
            change (graph.layout headRef.field).VisibleTo who
            rw [headRef.layout_eq]
            exact ownerEq
          rw [graph.playerStore_of_visible who store headRef.field visible]
          exact writeField_eq_of_get? headRef (state.get source) _ store (agree source)
        · rw [writeField_of_ne headRef (state.get source) _ field same]
          apply encodeObservationStore_apply_eq_playerStore who refs.tail tailState store
            field (fun read => agree (.there read))
          intro absent
          apply coverage
          rintro ⟨readName, cell, read, visible, found⟩
          cases read with
          | here => exact same found.symm
          | there read => exact absent ⟨readName, cell, read, visible, found⟩
      · simp only [ownerEq, ↓reduceDIte, observationTail_sourceObserve]
        apply encodeObservationStore_apply_eq_playerStore who refs.tail tailState store
          field (fun read => agree (.there read))
        intro absent
        apply coverage
        rintro ⟨readName, cell, read, visible, found⟩
        cases read with
        | here => exact ownerEq visible
        | there read => exact absent ⟨readName, cell, read, visible, found⟩

/-- Under semantic agreement, the constructive encoding equals the actual
masked store whenever the reference environment covers every available
visible field. -/
theorem encodeObservationStore_eq_playerStore
    {graph : Vegas.EventGraph Player L} (who : Player)
    {Γ : SourceCtx Player L} (refs : ContextRefs graph.layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store graph.layout)
    (agree : refs.Agrees state store)
    (coverage : ∀ field, ¬ refs.CoversVisible who field →
      graph.playerStore who store field = none) :
    encodeObservationStore who refs (sourceObserve who state) =
      graph.playerStore who store := by
  funext field
  exact encodeObservationStore_apply_eq_playerStore who refs state store field agree
    (coverage field)

omit R in
/-- Pure decoder/encoder inversion at one covered partial store. Unlike the
semantic agreement theorem above, this result needs no source state: every
written value comes directly from the successful decoder read. -/
private theorem encodeObservationStore_decode_apply
    {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L} (who : Player) :
    {Γ : SourceCtx Player L} →
    (refs : ContextRefs layout Γ) → (store : Vegas.EventGraph.Store layout) →
    (observation : SourceObservation L who Γ) →
    decodeObservation? who refs store = some observation →
    (field : Field) →
    (¬ refs.CoversVisible who field → store field = none) →
    encodeObservationStore who refs observation field = store field
  | [], refs, store, observation, decoded, field, coverage => by
      have observationEq : observation = ⟨Env.empty _⟩ := Option.some.inj decoded.symm
      subst observation
      exact (coverage (by
        rintro ⟨name, cell, source, _, _⟩
        nomatch source)).symm
  | (name, .publicData payload) :: Γ, refs, store, observation,
      decoded, field, coverage => by
      let source : HasVar ((name, .publicData payload) :: Γ) name
          (.publicData payload) := .here
      let headRef := refs.get source
      rw [decodeObservation?] at decoded
      cases headEq : headRef.get? store with
      | none =>
        change (refs.get HasVar.here).get? store = none at headEq
        rw [headEq] at decoded
        contradiction
      | some head =>
        change (refs.get HasVar.here).get? store = some head at headEq
        cases tailEq : decodeObservation? who refs.tail store with
        | none =>
          rw [headEq, tailEq] at decoded
          contradiction
        | some tail =>
          rw [headEq, tailEq] at decoded
          cases decoded
          change writeField headRef head (encodeObservationStore who refs.tail tail) field =
            store field
          by_cases same : field = headRef.field
          · subst field
            exact writeField_eq_of_get? headRef head _ store headEq
          · rw [writeField_of_ne headRef head _ field same]
            apply encodeObservationStore_decode_apply who refs.tail store tail tailEq field
            intro absent
            apply coverage
            rintro ⟨readName, cell, read, visible, found⟩
            cases read with
            | here => exact same found.symm
            | there read => exact absent ⟨readName, cell, read, visible, found⟩
  | (name, .publication payload) :: Γ, refs, store, observation,
      decoded, field, coverage => by
      let source : HasVar ((name, .publication payload) :: Γ) name
          (.publication payload) := .here
      let headRef := refs.get source
      rw [decodeObservation?] at decoded
      cases headEq : headRef.get? store with
      | none =>
        change (refs.get HasVar.here).get? store = none at headEq
        rw [headEq] at decoded
        contradiction
      | some head =>
        change (refs.get HasVar.here).get? store = some head at headEq
        cases tailEq : decodeObservation? who refs.tail store with
        | none =>
          rw [headEq, tailEq] at decoded
          contradiction
        | some tail =>
          rw [headEq, tailEq] at decoded
          cases decoded
          change writeField headRef head (encodeObservationStore who refs.tail tail) field =
            store field
          by_cases same : field = headRef.field
          · subst field
            exact writeField_eq_of_get? headRef head _ store headEq
          · rw [writeField_of_ne headRef head _ field same]
            apply encodeObservationStore_decode_apply who refs.tail store tail tailEq field
            intro absent
            apply coverage
            rintro ⟨readName, cell, read, visible, found⟩
            cases read with
            | here => exact same found.symm
            | there read => exact absent ⟨readName, cell, read, visible, found⟩
  | (name, .privateData owner payload) :: Γ, refs, store, observation,
      decoded, field, coverage => by
      let source : HasVar ((name, .privateData owner payload) :: Γ) name
          (.privateData owner payload) := .here
      let headRef := refs.get source
      rw [decodeObservation?] at decoded
      by_cases ownerEq : owner = who
      · simp only [ownerEq, ↓reduceDIte] at decoded
        cases bindingEq : headRef.get? store with
        | none =>
          change (refs.get HasVar.here).get? store = none at bindingEq
          rw [bindingEq] at decoded
          contradiction
        | some binding =>
          change (refs.get HasVar.here).get? store = some binding at bindingEq
          cases tailEq : decodeObservation? who refs.tail store with
          | none =>
            rw [bindingEq, tailEq] at decoded
            contradiction
          | some tail =>
            rw [bindingEq, tailEq] at decoded
            cases decoded
            rw [encodeObservationStore]
            simp only [ownerEq, ↓reduceDIte]
            change writeField headRef binding
                (encodeObservationStore who refs.tail tail) field = store field
            by_cases same : field = headRef.field
            · subst field
              exact writeField_eq_of_get? headRef binding _ store bindingEq
            · rw [writeField_of_ne headRef binding _ field same]
              apply encodeObservationStore_decode_apply who refs.tail store tail tailEq field
              intro absent
              apply coverage
              rintro ⟨readName, cell, read, visible, found⟩
              cases read with
              | here => exact same found.symm
              | there read => exact absent ⟨readName, cell, read, visible, found⟩
      · simp only [ownerEq, ↓reduceDIte] at decoded
        cases tailEq : decodeObservation? who refs.tail store with
        | none =>
          rw [tailEq] at decoded
          contradiction
        | some tail =>
          rw [tailEq] at decoded
          cases decoded
          rw [encodeObservationStore]
          simp only [ownerEq, ↓reduceDIte]
          apply encodeObservationStore_decode_apply who refs.tail store tail tailEq field
          intro absent
          apply coverage
          rintro ⟨readName, cell, read, visible, found⟩
          cases read with
          | here => exact ownerEq visible
          | there read => exact absent ⟨readName, cell, read, visible, found⟩

omit R in
/-- A successful observation decode is a right inverse of the constructive
encoder whenever all available fields are covered by visible source refs. -/
theorem encodeObservationStore_decodeObservation?_eq
    {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ) (who : Player)
    (store : Vegas.EventGraph.Store layout)
    (observation : SourceObservation L who Γ)
    (decoded : decodeObservation? who refs store = some observation)
    (coverage : ∀ field, ¬ refs.CoversVisible who field → store field = none) :
    encodeObservationStore who refs observation = store := by
  funext field
  exact encodeObservationStore_decode_apply who refs store observation decoded
    field (coverage field)

omit R in
/-- The observation decoder succeeds whenever every visible source reference
is available. -/
theorem exists_decodeObservation_of_available
    {Field : Type} {layout : Field → Vegas.EventGraph.EventField Player L} (who : Player) :
    {Γ : SourceCtx Player L} → (refs : ContextRefs layout Γ) →
    (store : Vegas.EventGraph.Store layout) →
    (∀ {name cell} (source : HasVar Γ name cell), cellVisibleTo who cell →
      ((refs.get source).get? store).isSome = true) →
    ∃ observation, decodeObservation? who refs store = some observation
  | [], refs, store, available => ⟨⟨Env.empty _⟩, rfl⟩
  | (name, .publicData payload) :: Γ, refs, store, available => by
      have headAvailable := available (HasVar.here :
        HasVar ((name, .publicData payload) :: Γ) name (.publicData payload)) trivial
      cases headEq : (refs.get (HasVar.here :
          HasVar ((name, .publicData payload) :: Γ) name
            (.publicData payload))).get? store with
      | none => simp [headEq] at headAvailable
      | some head =>
        obtain ⟨tail, tailEq⟩ := exists_decodeObservation_of_available who refs.tail store
          (fun source visible => available (.there source) visible)
        exact ⟨⟨Env.cons head tail.cells⟩, by simp [decodeObservation?, headEq, tailEq]⟩
  | (name, .publication payload) :: Γ, refs, store, available => by
      have headAvailable := available (HasVar.here :
        HasVar ((name, .publication payload) :: Γ) name (.publication payload)) trivial
      cases headEq : (refs.get (HasVar.here :
          HasVar ((name, .publication payload) :: Γ) name
            (.publication payload))).get? store with
      | none => simp [headEq] at headAvailable
      | some head =>
        obtain ⟨tail, tailEq⟩ := exists_decodeObservation_of_available who refs.tail store
          (fun source visible => available (.there source) visible)
        exact ⟨⟨Env.cons head tail.cells⟩, by simp [decodeObservation?, headEq, tailEq]⟩
  | (name, .privateData owner payload) :: Γ, refs, store, available => by
      obtain ⟨tail, tailEq⟩ := exists_decodeObservation_of_available who refs.tail store
        (fun source visible => available (.there source) visible)
      by_cases same : owner = who
      · have bindingAvailable := available (HasVar.here :
          HasVar ((name, .privateData owner payload) :: Γ) name
            (.privateData owner payload)) same
        cases bindingEq : (refs.get (HasVar.here :
            HasVar ((name, .privateData owner payload) :: Γ) name
              (.privateData owner payload))).get? store with
        | none => simp [bindingEq] at bindingAvailable
        | some binding =>
          exact ⟨⟨Env.cons (some binding) tail.cells⟩, by
            simp [decodeObservation?, same, bindingEq, tailEq]⟩
      · exact ⟨⟨Env.cons none tail.cells⟩, by
          simp [decodeObservation?, same, tailEq]⟩

/-- A field structurally preceding the next source-ranked event is present at
the corresponding completed graph prefix. -/
private theorem store_isSome_of_before
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (unique : (wholeΓ.map Prod.fst).Nodup)
    (config : (toEventGraph whole unique).Config) {offset : Nat}
    (ordered : config.cut.IsPrefix offset)
    (event : Fin (eventCount whole)) (rank : event.val = offset)
    (field : Vegas.EventGraph.FieldId wholeΓ.length (eventCount whole))
    (before : FieldBefore event field) :
    (config.store field).isSome = true := by
  cases field with
  | inl input => simp [Vegas.EventGraph.Config.store]
  | inr producer =>
      rw [Vegas.EventGraph.Config.store_output, config.output_available]
      exact (ordered.2 producer).mpr (rank ▸ before)

/-- At a canonical compiled prefix, the source observation decoder succeeds
on the actual masked player store. This is purely structural: references to
visible cells all precede the current event. -/
theorem exists_decodeObservation_of_prefix
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (unique : (wholeΓ.map Prod.fst).Nodup)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (refsBefore : ContextRefsBefore refs embedding)
    (index : Fin (eventCount program)) (offset : Nat)
    (config : (toEventGraph whole unique).Config)
    (ordered : config.cut.IsPrefix offset)
    (rank : (embedding.event index).val = offset) (who : Player) :
    ∃ observation, decodeObservation? who refs
        ((toEventGraph whole unique).playerStore who config.store) = some observation := by
  apply exists_decodeObservation_of_available who refs
  intro name cell source visible
  let ref := refs.get source
  have visibleKind : (cellField cell).VisibleTo who := by
    cases cell <;> exact visible
  rw [ref.get?_playerStore (graph := toEventGraph whole unique) who config.store
    visibleKind]
  exact ref.get?_isSome config.store
    (store_isSome_of_before whole unique config ordered (embedding.event index) rank
      ref.field (refsBefore source index))

omit [DecidableEq Player] R in
@[simp] theorem cellVisibleTo_iff_fieldVisibleTo (who : Player)
    (cell : CellTy Player L) :
    cellVisibleTo who cell ↔
      (cellField cell).VisibleTo who := by
  cases cell <;> rfl

/-- The references carried at a source suffix cover every graph input and
every event output preceding that suffix's source rank. -/
def ContextRefs.CoversPrefix
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (offset : Nat) : Prop :=
  (∀ input : Fin wholeΓ.length,
      ∃ name cell, ∃ source : HasVar Γ name cell,
        (refs.get source).field = .inl input) ∧
    (∀ event : Fin (eventCount whole), event.val < offset →
      ∃ name cell, ∃ source : HasVar Γ name cell,
        (refs.get source).field = .inr event)

omit [DecidableEq Player] R in
/-- Every initial input index is represented by its source-context member. -/
private theorem exists_source_inputId : (Γ : SourceCtx Player L) →
    ∀ input : Fin Γ.length,
      ∃ name cell, ∃ source : HasVar Γ name cell, inputId source = input
  | [], input => nomatch input
  | (name, cell) :: Γ, input => by
      refine Fin.cases ?_ (fun tail => ?_) input
      · exact ⟨name, cell, HasVar.here, rfl⟩
      · obtain ⟨readName, readCell, source, found⟩ :=
          exists_source_inputId Γ tail
        exact ⟨readName, readCell, .there source, congrArg Fin.succ found⟩

/-- Initial compiler references cover the rank-zero prefix. -/
theorem ContextRefs.initial_coversPrefix
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    (ContextRefs.initial Γ (outputLayout program)).CoversPrefix program 0 := by
  constructor
  · intro input
    obtain ⟨name, cell, source, found⟩ := exists_source_inputId Γ input
    exact ⟨name, cell, source, by
      simp only [ContextRefs.initial]
      exact congrArg Sum.inl found⟩
  · intro event earlier
    omega

/-- Adding the output at the current rank extends reference coverage by one. -/
theorem ContextRefs.CoversPrefix.cons
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    {Γ : SourceCtx Player L} {name : VarId} {cell : CellTy Player L}
    {refs : ContextRefs (graphLayout whole) Γ} {offset : Nat}
    (covered : refs.CoversPrefix whole offset)
    (head : Vegas.EventGraph.FieldRef (graphLayout whole) (cellField cell))
    (event : Fin (eventCount whole)) (headField : head.field = .inr event)
    (headRank : event.val = offset) :
    (refs.cons (name := name) head).CoversPrefix whole (offset + 1) := by
  constructor
  · intro input
    obtain ⟨readName, readCell, source, found⟩ := covered.1 input
    exact ⟨readName, readCell, .there source, found⟩
  · intro prior earlier
    by_cases before : prior.val < offset
    · obtain ⟨readName, readCell, source, found⟩ := covered.2 prior before
      exact ⟨readName, readCell, .there source, found⟩
    · have rankEq : prior.val = offset := by omega
      have eventEq : event = prior := Fin.ext (headRank.trans rankEq.symm)
      exact ⟨name, cell, HasVar.here, headField.trans (congrArg Sum.inr eventEq)⟩

/-- Prefix coverage implies that every available player-visible field is named
by a visible source cell. -/
theorem ContextRefs.CoversPrefix.available_visible
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (unique : (wholeΓ.map Prod.fst).Nodup)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (offset : Nat) (covered : refs.CoversPrefix whole offset)
    (config : (toEventGraph whole unique).Config)
    (ordered : config.cut.IsPrefix offset) (who : Player)
    (field : (toEventGraph whole unique).Field)
    (absent : ¬ refs.CoversVisible who field) :
    (toEventGraph whole unique).playerStore who config.store field = none := by
  let graph := toEventGraph whole unique
  by_cases visible : graph.fieldVisibleTo who field
  · rw [graph.playerStore_of_visible who config.store field visible]
    cases field with
    | inl input =>
        obtain ⟨name, cell, source, found⟩ := covered.1 input
        exfalso
        apply absent
        refine ⟨name, cell, source, ?_, found⟩
        rw [cellVisibleTo_iff_fieldVisibleTo]
        change ((graphLayout whole) (.inl input)).VisibleTo who at visible
        rw [← found, (refs.get source).layout_eq] at visible
        exact visible
    | inr event =>
        by_cases earlier : event.val < offset
        · obtain ⟨name, cell, source, found⟩ := covered.2 event earlier
          exfalso
          apply absent
          refine ⟨name, cell, source, ?_, found⟩
          rw [cellVisibleTo_iff_fieldVisibleTo]
          change ((graphLayout whole) (.inr event)).VisibleTo who at visible
          rw [← found, (refs.get source).layout_eq] at visible
          exact visible
        · rw [Vegas.EventGraph.Config.store_output]
          have unavailable : (config.outputs event).isSome = false := by
            rw [Bool.eq_false_iff]
            intro available
            have completed := (config.output_available event).mp available
            exact earlier ((ordered.2 event).mp completed)
          cases outputEq : config.outputs event with
          | none => rfl
          | some value => simp [outputEq] at unavailable
  · exact graph.playerStore_of_hidden who config.store field visible

/-- At a canonical source prefix, encoding the current source observation is
exactly the actual player-visible graph store. -/
theorem encodeObservationStore_eq_playerStore_of_prefix
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (unique : (wholeΓ.map Prod.fst).Nodup)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (offset : Nat) (covered : refs.CoversPrefix whole offset)
    (config : (toEventGraph whole unique).Config)
    (ordered : config.cut.IsPrefix offset) (state : State L Γ)
    (agree : refs.Agrees state config.store) (who : Player) :
    encodeObservationStore who refs (sourceObserve who state) =
      (toEventGraph whole unique).playerStore who config.store := by
  apply encodeObservationStore_eq_playerStore (graph := toEventGraph whole unique)
    who refs state config.store agree
  exact ContextRefs.CoversPrefix.available_visible whole unique refs offset covered
    config ordered who

/-- The constructive observation encoder is a decoder inverse at every
canonical reachable prefix represented by the compiler references. -/
theorem decodeObservation?_encodeObservationStore_of_prefix
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (unique : (wholeΓ.map Prod.fst).Nodup)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (offset : Nat) (covered : refs.CoversPrefix whole offset)
    (config : (toEventGraph whole unique).Config)
    (ordered : config.cut.IsPrefix offset) (state : State L Γ)
    (refsAgree : refs.Agrees state config.store) (who : Player) :
    decodeObservation? who refs
        (encodeObservationStore who refs (sourceObserve who state)) =
      some (sourceObserve who state) := by
  rw [encodeObservationStore_eq_playerStore_of_prefix whole unique refs offset covered
    config ordered state refsAgree who]
  exact decodeObservation?_playerStore_eq_some (graph := toEventGraph whole unique)
    refs who state config.store refsAgree

/-- Conversely, every observation decoded from the actual canonical player
store re-encodes to that exact masked store. This is the store component of
the canonical graph-policy decision-view inverse. -/
theorem encodeObservationStore_decodeObservation?_eq_playerStore_of_prefix
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (unique : (wholeΓ.map Prod.fst).Nodup)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (offset : Nat) (covered : refs.CoversPrefix whole offset)
    (config : (toEventGraph whole unique).Config)
    (ordered : config.cut.IsPrefix offset) (state : State L Γ)
    (refsAgree : refs.Agrees state config.store) (who : Player)
    (observation : SourceObservation L who Γ)
    (decoded : decodeObservation? who refs
      ((toEventGraph whole unique).playerStore who config.store) = some observation) :
    encodeObservationStore who refs observation =
      (toEventGraph whole unique).playerStore who config.store := by
  have exactObservation := decodeObservation?_playerStore_eq_some
    (graph := toEventGraph whole unique) refs who state config.store refsAgree
  rw [decoded] at exactObservation
  have observationEq : observation = sourceObserve who state :=
    Option.some.inj exactObservation
  subst observation
  exact encodeObservationStore_eq_playerStore_of_prefix whole unique refs offset covered
    config ordered state refsAgree who

end Vegas.SourceProgram.EventLowering
