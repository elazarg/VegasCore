/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefix
import Vegas.Game.SourceStateKernel
import Vegas.Compile.EventGraphPolicyLaw
import Vegas.Source.DisclosureNormalization

/-! # One source decoder slice shared by every native store

The source syntax and rank fix the typed tail, policy slice, references,
registry and publication bookkeeping. They also fix the state lift, its whole
observation map, and partial view recovery. The witnesses do not depend on a
native store, history, private draw or scheduler.

The decoder identity holds for every additional count, including counts past
the terminal instruction. It is a symbolic compiler identity; identifying an
initialized native likelihood with a source assessment remains separate.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeNames : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeNames) (wholeProfile : BehavioralProfile whole)

/-- A static source prefix has one decoder slice for all stores and histories.
Its actual behavioral tail profile commutes with the same source-state lift.
No source strategy admission, native support or observation law is assumed. -/
theorem exists_decoder_slice {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout whole) Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile program profile refs revelations registry
      embedding refsBefore offset)
    (rank : Nat) (within : rank ≤ eventCount program) :
    ∃ (Δ : SourceCtx Player L) (tailNames : Finset VarId)
      (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
      (tailRefs : ContextRefs (graphLayout whole) Δ) (tailRegistry : Registry Δ)
      (tailRevelations : Revelations Δ)
      (tailEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) tail)
      (tailBefore : ContextRefsBefore tailRefs tailEmbedding)
      (lift : ProtocolState tail → ProtocolState program)
      (liftView : ∀ who, ProtocolView who tail → ProtocolView who program)
      (recover : ∀ who, ProtocolView who program → Option (ProtocolView who tail)),
      rank + eventCount tail = eventCount program ∧
      CompiledPolicySuffix whole wholeProfile tail tailProfile tailRefs tailRevelations tailRegistry
        tailEmbedding tailBefore (offset + rank) ∧
      ((∀ who, (profile who).EffectiveDisclosures program registry revelations) →
        ∀ who, (tailProfile who).EffectiveDisclosures tail tailRegistry tailRevelations) ∧
      Function.Injective lift ∧
      (∀ who state, ProtocolState.observe who program (lift state) =
        liftView who (ProtocolState.observe who tail state)) ∧
      (∀ who state, recover who (ProtocolState.observe who program (lift state)) =
        some (ProtocolState.observe who tail state)) ∧
      (∀ [Fintype Player] state, ProtocolState.behavioralStateStep program profile (lift state) =
        (ProtocolState.behavioralStateStep tail tailProfile state).map lift) ∧
      ∀ more store history,
        decodeSourcePrefix? program refs registry revelations embedding.ref (rank + more)
            store history =
          (decodeSourcePrefix? tail tailRefs tailRegistry tailRevelations tailEmbedding.ref
            more store history).map lift := by
  induction rank generalizing Γ names offset with
  | zero =>
      refine ⟨Γ, names, program, profile, refs, registry, revelations, embedding, refsBefore, id,
        (fun _ => id), (fun _ => some), by omega, by simpa only [Nat.add_zero] using aligned,
        (fun effective => effective), Function.injective_id,
        (fun _ _ => rfl), (fun _ _ => rfl), ?_, ?_⟩
      · intro _inst state
        simp only [id_eq, PMF.map_id]
      · intro more store history
        simp only [Nat.zero_add, Option.map_id_fun, id_eq]
  | succ rank ih =>
      cases program with
      | ret payoffs =>
          simp only [eventCount] at within
          omega
      | @sample Γ names name payload fresh distribution next =>
          let headIndex : Fin (eventCount (.sample name fresh distribution next)) :=
            ⟨0, by simp [eventCount]⟩
          let headRef : EventGraph.FieldRef (graphLayout whole) (.publicData payload) :=
            embedding.ref headIndex
          let nextEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let nextRefs : ContextRefs (graphLayout whole) ((name, .publicData payload) :: Γ) :=
            refs.cons headRef
          have nextBefore : ContextRefsBefore nextRefs nextEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event headIndex).val < (embedding.event remaining.succ).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref remaining.succ
          have nextAligned : CompiledPolicySuffix whole wholeProfile next (afterSample profile)
              nextRefs revelations.weaken registry.weaken nextEmbedding nextBefore (offset + 1) :=
            aligned.sampleTail whole wholeProfile (_openNames := names) fresh distribution next
              profile refs revelations registry embedding refsBefore offset
          have tailBound : rank ≤ eventCount next := by
            simp only [eventCount] at within
            omega
          obtain ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailEmbedding, tailBefore, lift, liftView, recover, counted, tailAligned, tailEffective,
            injective,
            viewed, recovered,
            commutes, transport⟩ :=
            ih next (afterSample profile) nextRefs registry.weaken revelations.weaken nextEmbedding
              nextBefore (offset + 1) nextAligned tailBound
          refine ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailEmbedding, tailBefore, Sum.inr ∘ lift, (fun who => Sum.inr ∘ liftView who),
            (fun who view => view.getRight?.bind (recover who)), ?_, ?_, ?_,
            Sum.inr_injective.comp injective, ?_, ?_, ?_, ?_⟩
          · simp only [eventCount]
            omega
          · simpa only [Nat.add_assoc, Nat.add_comm 1 rank] using tailAligned
          · intro effective
            exact tailEffective (fun who => effective who)
          · intro who state
            exact congrArg Sum.inr (viewed who state)
          · intro who state
            exact recovered who state
          · intro _inst state
            rw [Function.comp_apply, ProtocolState.behavioralStateStep_sample_tail,
              commutes, PMF.map_comp]
          · intro more store history
            rw [show rank + 1 + more = (rank + more) + 1 by omega, decodeSourcePrefix?_sample]
            have outputsEq : nextEmbedding.ref =
                fun event : Fin (eventCount next) => embedding.ref event.succ := by
              funext event
              rfl
            have shifted := transport more store history
            rw [outputsEq] at shifted
            simpa only [nextRefs, headRef, headIndex, Option.map_map] using
              congrArg (Option.map Sum.inr) shifted
      | @commit Γ names name owner payload fresh guard next =>
          let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
            ⟨0, by simp [eventCount]⟩
          let headRef : EventGraph.FieldRef (graphLayout whole) (.binding owner payload) :=
            embedding.ref headIndex
          let nextEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let nextRefs : ContextRefs (graphLayout whole) ((name, .commitment owner payload) :: Γ) :=
            refs.cons headRef
          let nextRegistry : Registry ((name, .commitment owner payload) :: Γ) :=
            { owner := owner, subject := name, payload := payload, source := HasVar.here,
              guard := guard.weaken } :: registry.weaken
          have nextBefore : ContextRefsBefore nextRefs nextEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event headIndex).val < (embedding.event remaining.succ).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref remaining.succ
          have nextAligned : CompiledPolicySuffix whole wholeProfile next (afterCommit profile)
              nextRefs revelations.weaken nextRegistry nextEmbedding nextBefore (offset + 1) :=
            aligned.commitTail whole wholeProfile fresh guard next profile refs revelations registry
              embedding refsBefore offset
          have tailBound : rank ≤ eventCount next := by
            simp only [eventCount] at within
            omega
          obtain ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailEmbedding, tailBefore, lift, liftView, recover, counted, tailAligned, tailEffective,
            injective,
            viewed, recovered,
            commutes, transport⟩ :=
            ih next (afterCommit profile) nextRefs nextRegistry revelations.weaken nextEmbedding
              nextBefore (offset + 1) nextAligned tailBound
          refine ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailEmbedding, tailBefore, Sum.inr ∘ lift, (fun who => Sum.inr ∘ liftView who),
            (fun who view => view.getRight?.bind (recover who)), ?_, ?_, ?_,
            Sum.inr_injective.comp injective, ?_, ?_, ?_, ?_⟩
          · simp only [eventCount]
            omega
          · simpa only [Nat.add_assoc, Nat.add_comm 1 rank] using tailAligned
          · intro effective
            exact tailEffective (fun who => effective who)
          · intro who state
            exact congrArg Sum.inr (viewed who state)
          · intro who state
            exact recovered who state
          · intro _inst state
            rw [Function.comp_apply, ProtocolState.behavioralStateStep_commit_tail,
              commutes, PMF.map_comp]
          · intro more store history
            rw [show rank + 1 + more = (rank + more) + 1 by omega, decodeSourcePrefix?_commit]
            have outputsEq : nextEmbedding.ref =
                fun event : Fin (eventCount next) => embedding.ref event.succ := by
              funext event
              rfl
            have shifted := transport more store history
            rw [outputsEq] at shifted
            simpa only [nextRefs, headRef, headIndex, nextRegistry, Option.map_map] using
              congrArg (Option.map Sum.inr) shifted
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          let headIndex : Fin (eventCount (.reveal published owner name fresh selected
              unresolved next)) := ⟨0, by simp [eventCount]⟩
          let headRef : EventGraph.FieldRef (graphLayout whole) (.publication payload) :=
            embedding.ref headIndex
          let nextEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let nextRefs : ContextRefs (graphLayout whole) ((published, .publication payload) :: Γ) :=
            refs.cons headRef
          have nextBefore : ContextRefsBefore nextRefs nextEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event headIndex).val < (embedding.event remaining.succ).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref remaining.succ
          have nextAligned : CompiledPolicySuffix whole wholeProfile next (afterReveal profile)
              nextRefs (revelations.reveal selected) registry.weaken nextEmbedding nextBefore
                (offset + 1) :=
            aligned.revealTail whole wholeProfile fresh selected unresolved next profile refs
              revelations registry embedding refsBefore offset
          have tailBound : rank ≤ eventCount next := by
            simp only [eventCount] at within
            omega
          obtain ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailEmbedding, tailBefore, lift, liftView, recover, counted, tailAligned, tailEffective,
            injective,
            viewed, recovered,
            commutes, transport⟩ :=
            ih next (afterReveal profile) nextRefs registry.weaken (revelations.reveal selected)
              nextEmbedding nextBefore (offset + 1) nextAligned tailBound
          refine ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailEmbedding, tailBefore, Sum.inr ∘ lift, (fun who => Sum.inr ∘ liftView who),
            (fun who view => view.getRight?.bind (recover who)), ?_, ?_, ?_,
            Sum.inr_injective.comp injective, ?_, ?_, ?_, ?_⟩
          · simp only [eventCount]
            omega
          · simpa only [Nat.add_assoc, Nat.add_comm 1 rank] using tailAligned
          · intro effective
            exact tailEffective (fun who => (effective who).2)
          · intro who state
            exact congrArg Sum.inr (viewed who state)
          · intro who state
            exact recovered who state
          · intro _inst state
            rw [Function.comp_apply, ProtocolState.behavioralStateStep_reveal_tail,
              commutes, PMF.map_comp]
          · intro more store history
            rw [show rank + 1 + more = (rank + more) + 1 by omega, decodeSourcePrefix?_reveal]
            have outputsEq : nextEmbedding.ref =
                fun event : Fin (eventCount next) => embedding.ref event.succ := by
              funext event
              rfl
            have shifted := transport more store history
            rw [outputsEq] at shifted
            simpa only [nextRefs, headRef, headIndex, Option.map_map] using
              congrArg (Option.map Sum.inr) shifted

end Vegas.SourceProgram
