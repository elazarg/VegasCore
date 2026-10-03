/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefix
import Vegas.Game.SourceStateKernel

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
  {Field : Type} [DecidableEq Field]
  {layout : Field → EventGraph.EventField Player L}

/-- A static source prefix has one decoder slice for all stores and histories.
Its actual behavioral tail profile commutes with the same source-state lift.
No source strategy admission, native support or observation law is assumed. -/
theorem exists_decoder_slice {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (rank : Nat) (within : rank ≤ eventCount program) :
    ∃ (Δ : SourceCtx Player L) (tailNames : Finset VarId)
      (tail : SourceProgram Player L Δ tailNames) (tailProfile : BehavioralProfile tail)
      (tailRefs : ContextRefs layout Δ) (tailRegistry : Registry Δ)
      (tailRevelations : Revelations Δ)
      (tailOutputs : ∀ event, EventGraph.FieldRef layout (outputLayout tail event))
      (lift : ProtocolState tail → ProtocolState program)
      (liftView : ∀ who, ProtocolView who tail → ProtocolView who program)
      (recover : ∀ who, ProtocolView who program → Option (ProtocolView who tail)),
      rank + eventCount tail = eventCount program ∧
      Function.Injective lift ∧
      (∀ who state, ProtocolState.observe who program (lift state) =
        liftView who (ProtocolState.observe who tail state)) ∧
      (∀ who state, recover who (ProtocolState.observe who program (lift state)) =
        some (ProtocolState.observe who tail state)) ∧
      (∀ [Fintype Player] state, ProtocolState.behavioralStateStep program profile (lift state) =
        (ProtocolState.behavioralStateStep tail tailProfile state).map lift) ∧
      ∀ more store history,
        decodeSourcePrefix? program refs registry revelations outputs (rank + more) store history =
          (decodeSourcePrefix? tail tailRefs tailRegistry tailRevelations tailOutputs
            more store history).map lift := by
  induction rank generalizing Γ names with
  | zero =>
      refine ⟨Γ, names, program, profile, refs, registry, revelations, outputs, id,
        (fun _ => id), (fun _ => some), by omega, Function.injective_id,
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
          let headRef : EventGraph.FieldRef layout (.publicData payload) := by
            simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
          have tailBound : rank ≤ eventCount next := by
            simp only [eventCount] at within
            omega
          obtain ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailOutputs, lift, liftView, recover, counted, injective, viewed, recovered,
            commutes, transport⟩ :=
            ih next (afterSample profile) (refs.cons headRef) (registry.weaken) (revelations.weaken)
              (fun event => outputs event.succ) tailBound
          refine ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailOutputs, Sum.inr ∘ lift, (fun who => Sum.inr ∘ liftView who),
            (fun who view => view.getRight?.bind (recover who)), ?_,
            Sum.inr_injective.comp injective, ?_, ?_, ?_, ?_⟩
          · simp only [eventCount]
            omega
          · intro who state
            exact congrArg Sum.inr (viewed who state)
          · intro who state
            exact recovered who state
          · intro _inst state
            rw [Function.comp_apply, ProtocolState.behavioralStateStep_sample_tail,
              commutes, PMF.map_comp]
          · intro more store history
            rw [show rank + 1 + more = (rank + more) + 1 by omega,
              decodeSourcePrefix?_sample, transport, Option.map_map]
      | @commit Γ names name owner payload fresh guard next =>
          let headRef : EventGraph.FieldRef layout (.binding owner payload) := by
            simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
          let nextRegistry : Registry ((name, .commitment owner payload) :: Γ) :=
            { owner := owner, subject := name, payload := payload, source := HasVar.here,
              guard := guard.weaken } :: registry.weaken
          have tailBound : rank ≤ eventCount next := by
            simp only [eventCount] at within
            omega
          obtain ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailOutputs, lift, liftView, recover, counted, injective, viewed, recovered,
            commutes, transport⟩ :=
            ih next (afterCommit profile) (refs.cons headRef) (nextRegistry) (revelations.weaken)
              (fun event => outputs event.succ) tailBound
          refine ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailOutputs, Sum.inr ∘ lift, (fun who => Sum.inr ∘ liftView who),
            (fun who view => view.getRight?.bind (recover who)), ?_,
            Sum.inr_injective.comp injective, ?_, ?_, ?_, ?_⟩
          · simp only [eventCount]
            omega
          · intro who state
            exact congrArg Sum.inr (viewed who state)
          · intro who state
            exact recovered who state
          · intro _inst state
            rw [Function.comp_apply, ProtocolState.behavioralStateStep_commit_tail,
              commutes, PMF.map_comp]
          · intro more store history
            rw [show rank + 1 + more = (rank + more) + 1 by omega,
              decodeSourcePrefix?_commit, transport, Option.map_map]
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          let headRef : EventGraph.FieldRef layout (.publication payload) := by
            simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
          have tailBound : rank ≤ eventCount next := by
            simp only [eventCount] at within
            omega
          obtain ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailOutputs, lift, liftView, recover, counted, injective, viewed, recovered,
            commutes, transport⟩ :=
            ih next (afterReveal profile) (refs.cons headRef) registry.weaken
              (revelations.reveal selected) (fun event => outputs event.succ) tailBound
          refine ⟨Δ, tailNames, tail, tailProfile, tailRefs, tailRegistry, tailRevelations,
            tailOutputs, Sum.inr ∘ lift, (fun who => Sum.inr ∘ liftView who),
            (fun who view => view.getRight?.bind (recover who)), ?_,
            Sum.inr_injective.comp injective, ?_, ?_, ?_, ?_⟩
          · simp only [eventCount]
            omega
          · intro who state
            exact congrArg Sum.inr (viewed who state)
          · intro who state
            exact recovered who state
          · intro _inst state
            rw [Function.comp_apply, ProtocolState.behavioralStateStep_reveal_tail,
              commutes, PMF.map_comp]
          · intro more store history
            rw [show rank + 1 + more = (rank + more) + 1 by omega,
              decodeSourcePrefix?_reveal, transport, Option.map_map]

end Vegas.SourceProgram
