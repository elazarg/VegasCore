/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphCanonical
import Vegas.Compile.EventGraphIndependence
import Vegas.Compile.EventGraphPolicyBacktranslation
import Vegas.EventGraph.CanonicalNormalization
import Vegas.EventGraph.PolicyCongruence

/-! # Canonical policy backtranslation law

Recompiling the source policy obtained from one arbitrary graph policy agrees
with that graph policy at every reachable canonical decision.  Consequently a
canonical unilateral graph deviation has exactly the source execution law of
its setup-uniform backtranslation.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Source profile replacement commutes exactly with policy compilation. -/
theorem compileEventProfile_update
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (profile : BehavioralProfile program)
    (who : Player) (replacement : BehavioralPolicy who program) :
    compileEventProfile program
        (Profile.update (sig := SourceProgram.gameSignature program)
          profile who replacement) =
      Profile.update (sig := (toEventGraph program).gameSignature)
        (compileEventProfile program profile) who
        (compileEventPolicy program who replacement) := by
  funext owner
  by_cases same : owner = who
  · subst owner
    simp [compileEventProfile, Profile.update_same]
  · simp [compileEventProfile, Profile.update_of_ne _ _ same]

private theorem cast_finDist_eq_map {A B : Type} (same : A = B)
    (law : FinDist A) :
    cast (congrArg FinDist same) law = law.map (cast same) := by
  cases same
  exact (FinDist.map_id law).symm

/-- At a reachable canonical decision, recompiling an arbitrary graph
policy's source backtranslation yields its rank-normalized graph kernel. -/
private theorem compilePolicyTable_backtranslate_eq_normalized
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (who : Player)
    (replacement : (toEventGraph whole).BehavioralPolicy who) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graphLayout whole) Γ)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
      (_refsBefore : ContextRefsBefore refs embedding)
      (suffixOffset : Nat),
      (actorEq : ∀ index,
        (toEventGraph whole).actor? (embedding.event index) =
          eventOwner? program index) →
      (rankEq : ∀ index, (embedding.event index).val = suffixOffset + index.val) →
      refs.CoversPrefix whole suffixOffset →
      ∀ (inputs : (toEventGraph whole).Inputs)
        (config : (toEventGraph whole).Config),
      config.Reachable inputs →
      ∀ (selectedOffset : Nat), config.cut.IsPrefix selectedOffset →
      ∀ (index : Fin (eventCount program)),
      (rank : (embedding.event index).val = selectedOffset) →
      (ready : config.cut.Ready (embedding.event index)) →
      (actor : (toEventGraph whole).actor?
        (embedding.event index) = some who) →
      compilePolicyTable program refs embedding.ref who
          (backtranslatePolicyTable whole who replacement program refs
            embedding actorEq)
          index ((toEventGraph whole).playerObserve who config).store
          (decodeCompletions whole
            ((toEventGraph whole).playerObserve who config).ownActions) =
        cast (congrArg FinDist
          (congrArg Vegas.EventGraph.EventField.Action (embedding.layout_eq index)))
          ((toEventGraph whole).normalizePolicy who replacement
            (embedding.event index) actor
            ((toEventGraph whole).playerObserve who config)) := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro refs embedding refsBefore
        suffixOffset actorEq rankEq covered inputs config reachable selectedOffset ordered index
      exact nomatch index
  | sample name fresh law next ih =>
      intro refs embedding refsBefore
        suffixOffset actorEq rankEq covered inputs config reachable selectedOffset ordered index
      refine Fin.cases ?_ (fun tail => ?_) index <;> intro rank ready actor
      · let headIndex : Fin (eventCount (.sample name fresh law next)) :=
          ⟨0, by simp [eventCount]⟩
        have ownerless : (toEventGraph whole).actor?
            (embedding.event headIndex) = none := by
          simpa [headIndex, eventOwner?] using actorEq headIndex
        have strategic : (toEventGraph whole).actor?
            (embedding.event headIndex) = some who := by
          simpa [headIndex] using actor
        rw [strategic] at ownerless
        contradiction
      · let headIndex : Fin (eventCount (.sample name fresh law next)) :=
          ⟨0, by simp [eventCount]⟩
        let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
        let tailRefs := refs.cons (name := name) (cell := .publicData _)
          (embedding.ref headIndex)
        have tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
          intro readName cell source remaining
          cases source with
          | here =>
              change (embedding.event headIndex).val <
                (embedding.event (Fin.succ remaining)).val
              exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
          | there source => exact refsBefore source (Fin.succ remaining)
        have tailActorEq : ∀ current,
            (toEventGraph whole).actor? (tailEmbedding.event current) =
              eventOwner? next current := by
          intro current
          simpa [tailEmbedding, OutputEmbedding.tail, eventOwner?, eventCount,
            Fin.cases_succ] using actorEq (Fin.succ current)
        have tailRankEq : ∀ current,
            (tailEmbedding.event current).val = suffixOffset + 1 + current.val := by
          intro current
          have indexEq : Fin.cast (by simp) (Fin.succ current) =
              Fin.succ current := Fin.ext rfl
          simpa [tailEmbedding, OutputEmbedding.tail, indexEq, Nat.add_assoc,
            Nat.add_comm 1 current.val] using rankEq (Fin.succ current)
        have headRank : (embedding.event headIndex).val = suffixOffset := by
          simpa [headIndex] using rankEq headIndex
        have tailCovered : tailRefs.CoversPrefix whole (suffixOffset + 1) :=
          covered.cons whole (tailRefs.get HasVar.here) (embedding.event headIndex)
            rfl headRank
        have current :=
          ih tailRefs tailEmbedding tailRefsBefore (suffixOffset + 1)
            tailActorEq tailRankEq tailCovered inputs config reachable selectedOffset
            ordered tail rank ready actor
        have outputsEq : (fun remaining => embedding.ref (Fin.succ remaining)) =
            tailEmbedding.ref := by
          funext remaining
          rfl
        rw [← outputsEq] at current
        simpa [headIndex, tailEmbedding, tailRefs, OutputEmbedding.tail,
          OutputEmbedding.ref,
          eventCount, Fin.cases_succ, compilePolicyTable, backtranslatePolicyTable,
          outputLayout] using current
  | commit name owner fresh guard next ih =>
      intro refs embedding refsBefore
        suffixOffset actorEq rankEq covered inputs config reachable selectedOffset ordered index
      refine Fin.cases ?_ (fun tail => ?_) index <;> intro rank ready actor
      · let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
          ⟨0, by simp [eventCount]⟩
        have headActor : (toEventGraph whole).actor?
            (embedding.event headIndex) = some who := by
          simpa [headIndex] using actor
        have ownerEq : owner = who := by
          have this : eventOwner? (.commit name owner fresh guard next) headIndex =
              some who := actorEq headIndex ▸ headActor
          simpa [headIndex, eventOwner?] using this
        have headRank : (embedding.event headIndex).val = suffixOffset := by
          simpa [headIndex] using rankEq headIndex
        have selectedRank : (embedding.event headIndex).val = selectedOffset := by
          simpa [headIndex] using rank
        have offsetEq : selectedOffset = suffixOffset := by omega
        rw [offsetEq] at ordered
        have headReady : config.cut.Ready (embedding.event headIndex) := by
          simpa [headIndex] using ready
        obtain ⟨sourceObservation, decodedStore⟩ :=
          exists_decodeObservation_of_prefix whole refs embedding
            refsBefore headIndex suffixOffset config ordered headRank who
        let view :=
          (sourceObservation, decodeCompletions whole
            ((toEventGraph whole).playerObserve who config).ownActions)
        have encoded := encodeDecisionView?_decodeActual_eq_normalizeObservation
          whole refs suffixOffset covered inputs config reachable
          ordered (embedding.event headIndex) headReady who headActor sourceObservation decodedStore
        have kernel := backtranslatePolicyTable_commit_kernel whole who replacement
          refs embedding actorEq
          ownerEq view _ encoded
        change compilePolicyTable (.commit name owner fresh guard next) refs
            embedding.ref who
            (backtranslatePolicyTable whole who replacement
              (.commit name owner fresh guard next) refs embedding actorEq)
            headIndex ((toEventGraph whole).playerStore who config.store)
            (decodeCompletions whole
              ((toEventGraph whole).ownCompletions who config.history)) =
          cast (congrArg FinDist (congrArg Vegas.EventGraph.EventField.Action
            (embedding.layout_eq headIndex)))
            (replacement (embedding.event headIndex) headActor
              ((toEventGraph whole).normalizeObservation
                (embedding.event headIndex) who
                ((toEventGraph whole).playerObserve who config)))
        rw [compilePolicyTable_commit_of_decode refs embedding.ref
          (backtranslatePolicyTable whole who replacement
            (.commit name owner fresh guard next) refs embedding actorEq)
          ownerEq _ _ sourceObservation decodedStore]
        rw [cast_finDist_eq_map]
        change _ = (replacement (embedding.event headIndex) headActor
          ((toEventGraph whole).normalizeObservation
            (embedding.event headIndex) who
            ((toEventGraph whole).playerObserve who config))).map
              embedding.commitHeadAction
        simpa [headIndex, view] using kernel
      · let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
          ⟨0, by simp [eventCount]⟩
        let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
        let tailRefs := refs.cons (name := name) (cell := .commitment owner _)
          (embedding.ref headIndex)
        have tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
          intro readName cell source remaining
          cases source with
          | here =>
              change (embedding.event headIndex).val <
                (embedding.event (Fin.succ remaining)).val
              exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
          | there source => exact refsBefore source (Fin.succ remaining)
        have tailActorEq : ∀ current,
            (toEventGraph whole).actor? (tailEmbedding.event current) =
              eventOwner? next current := by
          intro current
          simpa [tailEmbedding, OutputEmbedding.tail, eventOwner?, eventCount,
            Fin.cases_succ] using actorEq (Fin.succ current)
        have tailRankEq : ∀ current,
            (tailEmbedding.event current).val = suffixOffset + 1 + current.val := by
          intro current
          have indexEq : Fin.cast (by simp) (Fin.succ current) =
              Fin.succ current := Fin.ext rfl
          simpa [tailEmbedding, OutputEmbedding.tail, indexEq, Nat.add_assoc,
            Nat.add_comm 1 current.val] using rankEq (Fin.succ current)
        have headRank : (embedding.event headIndex).val = suffixOffset := by
          simpa [headIndex] using rankEq headIndex
        have tailCovered : tailRefs.CoversPrefix whole (suffixOffset + 1) :=
          covered.cons whole (tailRefs.get HasVar.here) (embedding.event headIndex)
            rfl headRank
        have current :=
          ih tailRefs tailEmbedding tailRefsBefore (suffixOffset + 1)
            tailActorEq tailRankEq tailCovered inputs config reachable selectedOffset
            ordered tail rank ready actor
        have outputsEq : (fun remaining => embedding.ref (Fin.succ remaining)) =
            tailEmbedding.ref := by
          funext remaining
          rfl
        rw [← outputsEq] at current
        simpa [headIndex, tailEmbedding, tailRefs,
          OutputEmbedding.tail, OutputEmbedding.ref, eventCount, Fin.cases_succ, compilePolicyTable,
          backtranslatePolicyTable, outputLayout] using current
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs embedding refsBefore
        suffixOffset actorEq rankEq covered inputs config reachable selectedOffset ordered index
      refine Fin.cases ?_ (fun tail => ?_) index <;> intro rank ready actor
      · let headIndex : Fin (eventCount
            (.reveal published owner name fresh selected unresolved next)) :=
          ⟨0, by simp [eventCount]⟩
        have headActor : (toEventGraph whole).actor?
            (embedding.event headIndex) = some who := by
          simpa [headIndex] using actor
        have ownerEq : owner = who := by
          have : eventOwner?
              (.reveal published owner name fresh selected unresolved next) headIndex =
                some who := actorEq headIndex ▸ headActor
          simpa [headIndex, eventOwner?] using this
        have headRank : (embedding.event headIndex).val = suffixOffset := by
          simpa [headIndex] using rankEq headIndex
        have selectedRank : (embedding.event headIndex).val = selectedOffset := by
          simpa [headIndex] using rank
        have offsetEq : selectedOffset = suffixOffset := by omega
        rw [offsetEq] at ordered
        have headReady : config.cut.Ready (embedding.event headIndex) := by
          simpa [headIndex] using ready
        obtain ⟨sourceObservation, decodedStore⟩ :=
          exists_decodeObservation_of_prefix whole refs embedding
            refsBefore headIndex suffixOffset config ordered headRank who
        let view :=
          (sourceObservation, decodeCompletions whole
            ((toEventGraph whole).playerObserve who config).ownActions)
        have encoded := encodeDecisionView?_decodeActual_eq_normalizeObservation
          whole refs suffixOffset covered inputs config reachable
          ordered (embedding.event headIndex) headReady who headActor sourceObservation decodedStore
        have kernel := backtranslatePolicyTable_reveal_kernel whole who replacement
          refs embedding actorEq
          ownerEq view _ encoded
        change compilePolicyTable
            (.reveal published owner name fresh selected unresolved next) refs
            embedding.ref who
            (backtranslatePolicyTable whole who replacement
              (.reveal published owner name fresh selected unresolved next) refs
                embedding actorEq)
            headIndex ((toEventGraph whole).playerStore who config.store)
            (decodeCompletions whole
              ((toEventGraph whole).ownCompletions who config.history)) =
          cast (congrArg FinDist (congrArg Vegas.EventGraph.EventField.Action
            (embedding.layout_eq headIndex)))
            (replacement (embedding.event headIndex) headActor
              ((toEventGraph whole).normalizeObservation
                (embedding.event headIndex) who
                ((toEventGraph whole).playerObserve who config)))
        rw [compilePolicyTable_reveal_of_decode refs embedding.ref
          (backtranslatePolicyTable whole who replacement
            (.reveal published owner name fresh selected unresolved next) refs
              embedding actorEq)
          ownerEq _ _ sourceObservation decodedStore]
        rw [cast_finDist_eq_map]
        change _ = (replacement (embedding.event headIndex) headActor
          ((toEventGraph whole).normalizeObservation
            (embedding.event headIndex) who
            ((toEventGraph whole).playerObserve who config))).map
              embedding.revealHeadAction
        simpa [headIndex, view] using kernel
      · let headIndex : Fin (eventCount
            (.reveal published owner name fresh selected unresolved next)) :=
          ⟨0, by simp [eventCount]⟩
        let resultRef : Vegas.EventGraph.FieldRef (graphLayout whole)
            (.publication _) := by
          simpa [headIndex, outputLayout, eventCount] using embedding.ref headIndex
        let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
        let tailRefs := refs.cons (name := published) (cell := .publication _) resultRef
        have tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
          intro readName cell source remaining
          cases source with
          | here =>
              change (embedding.event headIndex).val <
                (embedding.event (Fin.succ remaining)).val
              exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
          | there source => exact refsBefore source (Fin.succ remaining)
        have tailActorEq : ∀ current,
            (toEventGraph whole).actor? (tailEmbedding.event current) =
              eventOwner? next current := by
          intro current
          simpa [tailEmbedding, OutputEmbedding.tail, eventOwner?, eventCount,
            Fin.cases_succ] using actorEq (Fin.succ current)
        have tailRankEq : ∀ current,
            (tailEmbedding.event current).val = suffixOffset + 1 + current.val := by
          intro current
          have indexEq : Fin.cast (by simp) (Fin.succ current) =
              Fin.succ current := Fin.ext rfl
          simpa [tailEmbedding, OutputEmbedding.tail, indexEq, Nat.add_assoc,
            Nat.add_comm 1 current.val] using rankEq (Fin.succ current)
        have headRank : (embedding.event headIndex).val = suffixOffset := by
          simpa [headIndex] using rankEq headIndex
        have tailCovered : tailRefs.CoversPrefix whole (suffixOffset + 1) :=
          covered.cons whole (tailRefs.get HasVar.here) (embedding.event headIndex)
            rfl headRank
        have current :=
          ih tailRefs tailEmbedding
            tailRefsBefore (suffixOffset + 1) tailActorEq tailRankEq
            tailCovered inputs config reachable selectedOffset ordered tail rank ready actor
        have outputsEq : (fun remaining => embedding.ref (Fin.succ remaining)) =
            tailEmbedding.ref := by
          funext remaining
          rfl
        rw [← outputsEq] at current
        simpa [headIndex, tailEmbedding, tailRefs, resultRef,
          OutputEmbedding.tail, OutputEmbedding.ref, eventCount, Fin.cases_succ, compilePolicyTable,
          backtranslatePolicyTable, outputLayout] using current

/-- Recompiling an arbitrary graph policy's setup-uniform source
backtranslation agrees with its rank-normalized graph kernel at every
reachable canonical decision. -/
theorem compileEventPolicy_backtranslate_at_prefix
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (who : Player)
    (replacement : (toEventGraph program).BehavioralPolicy who)
    (inputs : (toEventGraph program).Inputs)
    (config : (toEventGraph program).Config)
    (reachable : config.Reachable inputs)
    (offset : Nat) (ordered : config.cut.IsPrefix offset)
    (event : Fin (eventCount program)) (ready : config.cut.Ready event)
    (rank : event.val = offset)
    (actor : (toEventGraph program).actor? event = some who) :
    compileEventPolicy program who
        (backtranslateEventPolicy program who replacement)
        event actor ((toEventGraph program).playerObserve who config) =
      (toEventGraph program).normalizePolicy who replacement
        event actor ((toEventGraph program).playerObserve who config) := by
  have aligned := compilePolicyTable_backtranslate_eq_normalized
    program who replacement program
    (ContextRefs.initial Γ (outputLayout program))
    (outputEmbedding program) (initialRefsBefore program) 0
    (fun current => (eventOwner?_eq_actor program current).symm)
    (fun current => by simp [outputEmbedding])
    (ContextRefs.initial_coversPrefix program) inputs config reachable offset ordered
    event rank ready actor
  have refsEq : (outputEmbedding program).ref = outputRef program := by
    funext current
    exact outputEmbedding_ref program current
  rw [refsEq] at aligned
  simpa [compileEventPolicy, backtranslateEventPolicy, outputEmbedding,
    outputEmbedding_ref, toEventGraph] using aligned

end Vegas.SourceProgram.EventLowering
