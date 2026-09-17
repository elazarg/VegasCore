/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphHistory
import Vegas.Compile.EventGraphSuffix

/-! # Policy alignment along compiled source suffixes

The whole graph keeps one behavioral profile, while the canonical source-order
proof recursively advances through source-policy tails. This module records
only the dependent lookup equality connecting those two views.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- A source suffix's policy table is the corresponding slice of the one
behavioral profile compiled for the whole program. -/
structure CompiledPolicySuffix
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeProfile : BehavioralProfile whole)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (refsBefore : ContextRefsBefore refs embedding)
    (offset : Nat) : Prop where
  graphSuffix : CompiledSuffix whole program refs revelations registry
    embedding refsBefore offset
  actorEq : ∀ index,
    (toEventGraph whole).actor? (embedding.event index) =
      eventOwner? program index
  policyEq : ∀ (who : Player) (index : Fin (eventCount program))
      (actor : (toEventGraph whole).actor? (embedding.event index) = some who)
      (observation : (toEventGraph whole).PlayerObservation who),
    cast (congrArg FinDist
      (congrArg Vegas.EventGraph.EventField.Action (embedding.layout_eq index)))
      ((compileEventProfile whole wholeProfile) who
        (embedding.event index) actor observation) =
    compilePolicyTable program refs embedding.ref who
      (profile who) index observation.store
      (decodeCompletions whole observation.ownActions)
  actionEq : ∀ (index : Fin (eventCount program))
      (action : Vegas.EventGraph.EventField.Action
        (outputLayout whole (embedding.event index))),
    decodeEventAction whole (embedding.event index) action =
      decodeEventAction program index
        (cast (congrArg Vegas.EventGraph.EventField.Action
          (embedding.layout_eq index)) action)

/-- The initial whole-program profile is aligned with its own policy table. -/
theorem CompiledPolicySuffix.whole
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program) :
    CompiledPolicySuffix program profile program profile
      (ContextRefs.initial Γ (outputLayout program)) (Revelations.initial Γ) []
      (outputEmbedding program) (initialRefsBefore program) 0 := by
  constructor
  · exact CompiledSuffix.whole program
  · intro index
    exact (eventOwner?_eq_actor program index).symm
  · intro who index actor observation
    rfl
  · intro index action
    rfl

/-- Policy alignment advances across a source sampling node with the same
typed suffix state as node lowering. -/
theorem CompiledPolicySuffix.sampleTail
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeProfile : BehavioralProfile whole)
    {Γ : SourceCtx Player L} {_openNames nextOpen : Finset VarId}
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) nextOpen)
    (profile : BehavioralProfile (.sample name fresh law next))
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.sample name fresh law next))
    (refsBefore : ContextRefsBefore refs embedding)
    (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile
      (.sample name fresh law next) profile refs revelations registry
      embedding refsBefore offset) :
    let headIndex : Fin (eventCount (.sample name fresh law next)) :=
      ⟨0, by simp [eventCount]⟩
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons (embedding.ref headIndex)
    let tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
      intro readName cell source remaining
      cases source with
      | here =>
          change (embedding.event headIndex).val <
            (embedding.event (Fin.succ remaining)).val
          apply embedding.strictMono
          exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
      | there source => exact refsBefore source (Fin.succ remaining)
    CompiledPolicySuffix whole wholeProfile next
      (afterSample profile) tailRefs revelations.weaken
      registry.weaken tailEmbedding tailRefsBefore (offset + 1) := by
  dsimp only
  constructor
  · exact aligned.graphSuffix.sampleTail (whole := whole)
      (_openNames := _openNames) fresh law next refs revelations registry
      embedding refsBefore offset
  · intro index
    simpa [OutputEmbedding.tail, eventOwner?, eventCount, Fin.cases_succ] using
      aligned.actorEq (Fin.succ index)
  · intro who index actor observation
    have current := aligned.policyEq who (Fin.succ index) actor observation
    change _ = compilePolicyTable next
      (refs.cons (embedding.ref ⟨0, by simp [eventCount]⟩))
      (fun tail => embedding.ref (Fin.succ tail)) who (profile who) index
      observation.store (decodeCompletions whole observation.ownActions) at current
    have outputsEq : (fun tail => embedding.ref (Fin.succ tail)) =
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl)).ref := by
      funext tail
      rfl
    rw [outputsEq] at current
    simpa [OutputEmbedding.tail, OutputEmbedding.ref, afterSample, eventCount,
      outputLayout] using current
  · intro index action
    have current := aligned.actionEq (Fin.succ index) action
    change _ = decodeEventAction next index _ at current
    simpa [OutputEmbedding.tail, eventCount, outputLayout] using current

/-- Policy alignment advances across a source commitment. -/
theorem CompiledPolicySuffix.commitTail
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeProfile : BehavioralProfile whole)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .privateData owner payload) :: Γ)
      (insert name openNames))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding)
    (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile
      (.commit name owner fresh guard next) profile refs revelations registry
      embedding refsBefore offset) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let obligation : Obligation _ :=
      { owner := owner, subject := name, payload := payload, source := .here,
        guard := guard.weaken }
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons (embedding.ref headIndex)
    let tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
      intro readName cell source remaining
      cases source with
      | here =>
          change (embedding.event headIndex).val <
            (embedding.event (Fin.succ remaining)).val
          apply embedding.strictMono
          exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
      | there source => exact refsBefore source (Fin.succ remaining)
    CompiledPolicySuffix whole wholeProfile next
      (afterCommit profile) tailRefs revelations.weaken
      (obligation :: registry.weaken) tailEmbedding tailRefsBefore (offset + 1) := by
  dsimp only
  constructor
  · exact aligned.graphSuffix.commitTail (whole := whole)
      fresh guard next refs revelations registry embedding refsBefore offset
  · intro index
    simpa [OutputEmbedding.tail, eventOwner?, eventCount, Fin.cases_succ] using
      aligned.actorEq (Fin.succ index)
  · intro who index actor observation
    have current := aligned.policyEq who (Fin.succ index) actor observation
    change _ = compilePolicyTable next
      (refs.cons (embedding.ref ⟨0, by simp [eventCount]⟩))
      (fun tail => embedding.ref (Fin.succ tail)) who ((profile who).2) index
      observation.store (decodeCompletions whole observation.ownActions) at current
    have outputsEq : (fun tail => embedding.ref (Fin.succ tail)) =
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl)).ref := by
      funext tail
      rfl
    rw [outputsEq] at current
    simpa [OutputEmbedding.tail, OutputEmbedding.ref, afterCommit, eventCount,
      outputLayout] using current
  · intro index action
    have current := aligned.actionEq (Fin.succ index) action
    change _ = decodeEventAction next index _ at current
    simpa [OutputEmbedding.tail, eventCount, outputLayout] using current

/-- Policy alignment advances across a source resolution. -/
theorem CompiledPolicySuffix.revealTail
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeProfile : BehavioralProfile whole)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.privateData owner payload))
    (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile
      (.reveal published owner name fresh selected unresolved next))
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.reveal published owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding)
    (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile
      (.reveal published owner name fresh selected unresolved next) profile refs
      revelations registry embedding refsBefore offset) :
    let headIndex : Fin (eventCount
        (.reveal published owner name fresh selected unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let resultRef : Vegas.EventGraph.FieldRef (graphLayout whole)
        (.publication payload) := by
      simpa [headIndex, outputLayout, eventCount] using embedding.ref headIndex
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons resultRef
    let tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
      intro readName cell source remaining
      cases source with
      | here =>
          change (embedding.event headIndex).val <
            (embedding.event (Fin.succ remaining)).val
          apply embedding.strictMono
          exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
      | there source => exact refsBefore source (Fin.succ remaining)
    CompiledPolicySuffix whole wholeProfile next
      (afterReveal profile) tailRefs
      (revelations.reveal (published := published) selected) registry.weaken tailEmbedding
      tailRefsBefore (offset + 1) := by
  dsimp only
  constructor
  · exact aligned.graphSuffix.revealTail (whole := whole)
      fresh selected unresolved next refs revelations registry embedding
      refsBefore offset
  · intro index
    simpa [OutputEmbedding.tail, eventOwner?, eventCount, Fin.cases_succ] using
      aligned.actorEq (Fin.succ index)
  · intro who index actor observation
    let resultRef : Vegas.EventGraph.FieldRef (graphLayout whole)
        (.publication payload) := by
      simpa [outputLayout, eventCount] using
        embedding.ref ⟨0, by simp [eventCount]⟩
    have current := aligned.policyEq who (Fin.succ index) actor observation
    change _ = compilePolicyTable next
      (refs.cons resultRef)
      (fun tail => embedding.ref (Fin.succ tail)) who ((profile who).2) index
      observation.store (decodeCompletions whole observation.ownActions) at current
    have outputsEq : (fun tail => embedding.ref (Fin.succ tail)) =
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl)).ref := by
      funext tail
      rfl
    rw [outputsEq] at current
    change _ = compilePolicyTable next
      (refs.cons resultRef)
      (embedding.tail next (by simp [eventCount]) (fun _ => rfl)).ref who
      ((profile who).2) index observation.store
      (decodeCompletions whole observation.ownActions)
    exact current
  · intro index action
    have current := aligned.actionEq (Fin.succ index) action
    change _ = decodeEventAction next index _ at current
    simpa [OutputEmbedding.tail, eventCount, outputLayout] using current

/-- Decoded own completions in an actual player observation are exactly that
player's component of the decoded whole source history. -/
@[simp] theorem decodeCompletions_playerObserve
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (config : (toEventGraph program).Config) (who : Player) :
    decodeCompletions program
        ((toEventGraph program).playerObserve who config).ownActions =
      decodeHistory program config.history who := by
  rfl

end Vegas.SourceProgram.EventLowering
