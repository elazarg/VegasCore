/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourceView

/-! # Source observation and decoder alignment along compiler suffixes

A residual source-state lift follows the actual syntactic position of the
whole program. Its observation map is recorded independently of node kernels.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- The same syntactic suffix map embeds source observations and identifies
the whole compiler decoder at every residual event, retaining all own actions. -/
structure ProtocolViewSuffix {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (lift : ProtocolState program → ProtocolState whole) where
  actionEq : ∀ index (action : EventField.Action (outputLayout whole (embedding.event index))),
    decodeEventAction whole (embedding.event index) action = decodeEventAction program index
      (cast (congrArg EventField.Action (embedding.layout_eq index)) action)
  view : (who : Player) → ProtocolView who program ↪ ProtocolView who whole
  observe : ∀ who point, ProtocolState.observe who whole (lift point) =
    view who (ProtocolState.observe who program point)
  decode : ∀ who event store past,
    decodeEventView? whole (ContextRefs.initial wholeΓ (outputLayout whole))
        (outputEmbedding whole).ref who (embedding.event event) store past =
      (decodeEventView? program refs embedding.ref who event store past).map (view who)

namespace ProtocolViewSuffix

/-- The original program has the identity observation and decoder embedding. -/
def initial : ProtocolViewSuffix whole whole
    (ContextRefs.initial wholeΓ (outputLayout whole)) (outputEmbedding whole) id where
  actionEq _ _ := rfl
  view _ := Function.Embedding.refl _
  observe _ _ := rfl
  decode _ _ _ _ := by
    change _ = Option.map id _
    rw [Option.map_id]
    rfl

/-- Consuming one chance instruction follows its actual source sum constructor. -/
def sampleTail {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.sample name fresh law next))
    (lift : ProtocolState (.sample name fresh law next) → ProtocolState whole)
    (aligned : ProtocolViewSuffix whole (.sample name fresh law next) refs embedding lift) :
    let head : Fin (eventCount (.sample name fresh law next)) := ⟨0, by simp [eventCount]⟩
    let ref : FieldRef (graphLayout whole) (.publicData payload) := by
      simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.ref head
    ProtocolViewSuffix whole next (refs.cons ref)
      (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
      (fun point => lift (Sum.inr point)) := by
  intro head ref
  refine ⟨?_, (fun who => ⟨(fun view => aligned.view who (Sum.inr view)),
    fun _ _ same => Sum.inr.inj ((aligned.view who).injective same)⟩), ?_, ?_⟩
  · intro index action
    exact aligned.actionEq (Fin.succ index) action
  · intro who point
    exact aligned.observe who (Sum.inr point)
  · intro who event store past
    have actual := aligned.decode who (Fin.succ event) store past
    change _ = (decodeEventView? next (refs.cons ref) _ who event store past).map
      (fun view => aligned.view who (Sum.inr view))
    change decodeEventView? whole (ContextRefs.initial wholeΓ (outputLayout whole))
      (outputEmbedding whole).ref who (embedding.event (Fin.succ event)) store past = _
    rw [actual]
    change ((decodeEventView? next (refs.cons ref) _ who event store past).map Sum.inr).map
      (aligned.view who) = _
    rw [Option.map_map]
    rfl

/-- Consuming one commitment retains its complete original source view. -/
def commitTail {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard next))
    (lift : ProtocolState (.commit name owner fresh guard next) → ProtocolState whole)
    (aligned : ProtocolViewSuffix whole (.commit name owner fresh guard next) refs embedding lift) :
    let head : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let ref : FieldRef (graphLayout whole) (.binding owner payload) := by
      simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.ref head
    ProtocolViewSuffix whole next (refs.cons ref)
      (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
      (fun point => lift (Sum.inr point)) := by
  intro head ref
  refine ⟨?_, (fun who => ⟨(fun view => aligned.view who (Sum.inr view)),
    fun _ _ same => Sum.inr.inj ((aligned.view who).injective same)⟩), ?_, ?_⟩
  · intro index action
    exact aligned.actionEq (Fin.succ index) action
  · intro who point
    exact aligned.observe who (Sum.inr point)
  · intro who event store past
    have actual := aligned.decode who (Fin.succ event) store past
    change _ = (decodeEventView? next (refs.cons ref) _ who event store past).map
      (fun view => aligned.view who (Sum.inr view))
    change decodeEventView? whole (ContextRefs.initial wholeΓ (outputLayout whole))
      (outputEmbedding whole).ref who (embedding.event (Fin.succ event)) store past = _
    rw [actual]
    change ((decodeEventView? next (refs.cons ref) _ who event store past).map Sum.inr).map
      (aligned.view who) = _
    rw [Option.map_map]
    rfl

/-- Consuming one disclosure retains the actual publication context and source position. -/
def revealTail {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.reveal published owner name fresh selected unresolved next))
    (lift : ProtocolState (.reveal published owner name fresh selected unresolved next) →
      ProtocolState whole)
    (aligned : ProtocolViewSuffix whole
      (.reveal published owner name fresh selected unresolved next) refs embedding lift) :
    let head : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let ref : FieldRef (graphLayout whole) (.publication payload) := by
      simpa only [head, outputLayout, Fin.mk_zero, Fin.cases_zero] using embedding.ref head
    ProtocolViewSuffix whole next (refs.cons ref)
      (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
      (fun point => lift (Sum.inr point)) := by
  intro head ref
  refine ⟨?_, (fun who => ⟨(fun view => aligned.view who (Sum.inr view)),
    fun _ _ same => Sum.inr.inj ((aligned.view who).injective same)⟩), ?_, ?_⟩
  · intro index action
    exact aligned.actionEq (Fin.succ index) action
  · intro who point
    exact aligned.observe who (Sum.inr point)
  · intro who event store past
    have actual := aligned.decode who (Fin.succ event) store past
    change _ = (decodeEventView? next (refs.cons ref) _ who event store past).map
      (fun view => aligned.view who (Sum.inr view))
    change decodeEventView? whole (ContextRefs.initial wholeΓ (outputLayout whole))
      (outputEmbedding whole).ref who (embedding.event (Fin.succ event)) store past = _
    rw [actual]
    change ((decodeEventView? next (refs.cons ref) _ who event store past).map Sum.inr).map
      (aligned.view who) = _
    rw [Option.map_map]
    rfl

/-- Typed agreement and the saved effective own history identify the actual
whole-source observation at the residual entry, through the owner's masked store. -/
theorem decode_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (lift : ProtocolState program → ProtocolState whole)
    (aligned : ProtocolViewSuffix whole program refs embedding lift)
    (nonempty : 0 < eventCount program) (who : Player)
    (source : SourceProgram.Config Player L Γ) (store : Store (graphLayout whole))
    (agrees : refs.Agrees source.state store) :
    decodeEventView? whole (ContextRefs.initial wholeΓ (outputLayout whole))
        (outputEmbedding whole).ref who (embedding.event ⟨0, nonempty⟩)
        ((toEventGraph whole).playerStore who store) (source.history who) =
      some (ProtocolState.observe who whole (lift (ProtocolState.entry program source))) := by
  have observed : decodeObservation? who refs ((toEventGraph whole).playerStore who store) =
      some (sourceObserve who source.state) :=
    (decodeObservation?_playerStore (graph := toEventGraph whole) who refs store).trans
      (decodeObservation?_eq_some refs who source.state store agrees)
  rw [aligned.decode, aligned.observe]
  cases program with
  | ret => simp only [eventCount] at nonempty; omega
  | sample name fresh law next =>
      change ((decodeObservation? who refs ((toEventGraph whole).playerStore who store)).map
        (fun observation => Sum.inl (observation, source.history who))).map (aligned.view who) = _
      rw [observed]
      rfl
  | commit name owner fresh guard next =>
      change ((decodeObservation? who refs ((toEventGraph whole).playerStore who store)).map
        (fun observation => Sum.inl (observation, source.history who))).map (aligned.view who) = _
      rw [observed]
      rfl
  | reveal published owner name fresh selected unresolved next =>
      change ((decodeObservation? who refs ((toEventGraph whole).playerStore who store)).map
        (fun observation => Sum.inl (observation, source.history who))).map (aligned.view who) = _
      rw [observed]
      rfl

end ProtocolViewSuffix
end Vegas
