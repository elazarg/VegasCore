/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosurePosterior
import Vegas.Source.ProtocolBehavioralPolicy

/-! # Lifting a continuation across private history prefixes

A continuation can replace a fixed initial own-history prefix by the history
of its compressed information site. Every subsequent action is retained. This
defines one behavioral policy from local information and preserves its entire
typed terminal law against arbitrary unchanged opponents.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {who : Player}

/-- Read the chosen continuation using a fixed replacement of the initial
own-history prefix. Subsequent choices remain in the player's observation. -/
def BehavioralPolicy.rebaseHistory {who : Player} (count : Nat)
    (replacement : List (OwnAction Player L)) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    BehavioralPolicy who program → BehavioralPolicy who program
  | _, _, .ret _, _ => PUnit.unit
  | _, _, .sample _ _ _ next, policy => rebaseHistory count replacement next policy
  | _, _, .commit _ _ _ _ next, policy =>
      (fun owned view => policy.1 owned (view.1, replacement ++ view.2.drop count),
        rebaseHistory count replacement next policy.2)
  | _, _, .reveal _ _ _ _ _ _ next, policy =>
      (fun owned view => policy.1 owned (view.1, replacement ++ view.2.drop count),
        rebaseHistory count replacement next policy.2)

omit [IExpr.ResultTypes L] in
private theorem rebase_update (count : Nat) (replacement : List (OwnAction Player L))
    (source target : History Player L)
    (others : ∀ other, other ≠ who → source other = target other)
    (focal : target who = replacement ++ (source who).drop count)
    (longEnough : count ≤ (source who).length) (actor : Player) (action : OwnAction Player L) :
    let source' := Function.update source actor (source actor ++ [action])
    let target' := Function.update target actor (target actor ++ [action])
    (∀ other, other ≠ who → source' other = target' other) ∧
      target' who = replacement ++ (source' who).drop count ∧
      count ≤ (source' who).length := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro other different
    by_cases same : other = actor
    · subst other
      simp only [Function.update_self, others actor different]
    · simp only [Function.update_of_ne same, others other different]
  · by_cases same : who = actor
    · subst actor
      rw [Function.update_self, Function.update_self,
        List.drop_append_of_le_length longEnough, ← List.append_assoc, ← focal]
    · simpa only [Function.update_of_ne same] using focal
  · by_cases same : who = actor
    · subst actor
      simp only [Function.update_self, List.length_append, List.length_singleton]
      omega
    · simpa only [Function.update_of_ne same] using longEnough

private def RebaseRealizes {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : Prop :=
  ∀ (count : Nat) (replacement : List (OwnAction Player L))
    (profile : BehavioralProfile program) (policy : BehavioralPolicy who program)
    (state : State L Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (source target : History Player L),
    (∀ other, other ≠ who → source other = target other) →
    target who = replacement ++ (source who).drop count →
    count ≤ (source who).length →
    runWith program (Function.update profile who (policy.rebaseHistory count replacement program))
        state registry revelations source =
      runWith program (Function.update profile who policy) state registry revelations target

private theorem rebaseRealizes_commit {Γ : SourceCtx Player L} {O : Finset VarId}
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (ih : RebaseRealizes (who := who) next) :
    RebaseRealizes (who := who) (.commit name owner fresh guard next) := by
  intro count replacement profile policy state registry revelations source target
    others focal longEnough
  have kernels : commitKernel
      (Function.update profile who (policy.rebaseHistory count replacement
        (.commit name owner fresh guard next))) (sourceObserve owner state, source owner) =
      commitKernel (Function.update profile who policy)
        (sourceObserve owner state, target owner) := by
    by_cases own : owner = who
    · subst who
      simp only [commitKernel, Function.update_self, BehavioralPolicy.rebaseHistory, focal]
    · simp only [commitKernel, Function.update_of_ne own, others owner own]
  simp only [runWith, kernels, afterCommit_update]
  apply FinDist.bind_congr
  intro binding _
  obtain ⟨otherStep, focalStep, lengthStep⟩ := rebase_update count replacement source target
    others focal longEnough owner (.commit owner name payload binding)
  exact ih count replacement (afterCommit profile) policy.2 _ _ _ _ _
    otherStep focalStep lengthStep

private theorem rebaseRealizes_reveal {Γ : SourceCtx Player L} {O : Finset VarId}
    (published : VarId) (owner : Player) (name : VarId) {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (ih : RebaseRealizes (who := who) next) :
    RebaseRealizes (who := who)
      (.reveal published owner name fresh selected unresolved next) := by
  intro count replacement profile policy state registry revelations source target
    others focal longEnough
  have kernels : revealKernel
      (Function.update profile who (policy.rebaseHistory count replacement
        (.reveal published owner name fresh selected unresolved next)))
        (sourceObserve owner state, source owner) =
      revealKernel (Function.update profile who policy)
        (sourceObserve owner state, target owner) := by
    by_cases own : owner = who
    · subst who
      simp only [revealKernel, Function.update_self, BehavioralPolicy.rebaseHistory, focal]
    · simp only [revealKernel, Function.update_of_ne own, others owner own]
  simp only [runWith, kernels, afterReveal_update]
  apply FinDist.bind_congr
  intro disclose _
  obtain ⟨otherStep, focalStep, lengthStep⟩ := rebase_update count replacement source target
    others focal longEnough owner (.reveal owner name disclose)
  exact ih count replacement (afterReveal profile) policy.2 _ _ _ _ _
    otherStep focalStep lengthStep

/-- Replacing the initial private history prefix commutes with every actual
continuation step. Hidden state, opponents, chance and deferred guards remain
arbitrary throughout this whole-continuation law. -/
theorem rebaseHistory_runWith {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (count : Nat) → (replacement : List (OwnAction Player L)) →
    (profile : BehavioralProfile program) → (policy : BehavioralPolicy who program) →
    (state : State L Γ) → (registry : Registry Γ) → (revelations : Revelations Γ) →
    (source target : History Player L) →
    (∀ other, other ≠ who → source other = target other) →
    target who = replacement ++ (source who).drop count →
    count ≤ (source who).length →
    runWith program (Function.update profile who (policy.rebaseHistory count replacement program))
        state registry revelations source =
      runWith program (Function.update profile who policy) state registry revelations target
  | _, _, .ret _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, count, replacement, profile, policy, state, registry,
      revelations, source, target, others, focal, longEnough => by
      simp only [runWith, afterSample_update]
      exact FinDist.bind_congr fun _ _ => rebaseHistory_runWith next count replacement
        (afterSample profile) policy _ _ _ source target others focal longEnough
  | _, _, .commit name owner fresh guard next, count, replacement, profile, policy, state,
      registry, revelations, source, target, others, focal, longEnough =>
      rebaseRealizes_commit name owner fresh guard next (rebaseHistory_runWith next)
        count replacement profile policy state registry revelations source target
        others focal longEnough
  | _, _, .reveal published owner name fresh selected unresolved next, count, replacement,
      profile, policy, state, registry, revelations, source, target, others, focal, longEnough =>
      rebaseRealizes_reveal published owner name fresh selected unresolved next
        (rebaseHistory_runWith next) count replacement profile policy state registry revelations
        source target others focal longEnough

/-- One policy lifts the compressed continuation at every hidden state in an
original information fiber. The remembered prefix is fixed by that fiber. -/
theorem rebaseHistory_runFrom {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy : BehavioralPolicy who program) (original replacement : List (OwnAction Player L))
    (config : Config Player L Γ) (past : config.history who = original) :
    runFrom program (Function.update profile who
        (policy.rebaseHistory original.length replacement program)) config =
      runFrom program (Function.update profile who policy)
        (config.withOwnHistory who replacement) := by
  apply rebaseHistory_runWith program original.length replacement profile policy
  · intro other different
    simp only [Config.withOwnHistory, Function.update_of_ne different]
  · simp only [Config.withOwnHistory, Function.update_self, past, List.drop_length,
      List.append_nil]
  · exact past.symm ▸ Nat.le_refl _

/-- Rebasing changes the observation at which a law is consulted, while
retaining its admitted support. It therefore lifts actual legal deviations. -/
theorem BehavioralPolicy.rebaseHistory_admitted {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : BehavioralPolicy who program) → policy.Admitted program admission →
    (count : Nat) → (replacement : List (OwnAction Player L)) →
    (policy.rebaseHistory count replacement program).Admitted program admission
  | _, _, .ret _, _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy, permitted, count, replacement =>
      policy.rebaseHistory_admitted next admission permitted count replacement
  | _, _, .commit _ _ _ _ next, admission, policy, permitted, count, replacement => by
      refine ⟨?_, policy.2.rebaseHistory_admitted next
        (fun site => admission (some site)) permitted.2 count replacement⟩
      intro own view choice supported
      exact permitted.1 own (view.1, replacement ++ view.2.drop count) choice supported
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy, permitted, count, replacement =>
      policy.2.rebaseHistory_admitted next admission permitted count replacement

/-- The deviation lift preserves correlated hidden parameters jointly with
the complete terminal state, with a single policy over the entire fiber. -/
theorem rebaseHistory_joint_law {Γ : SourceCtx Player L} {O : Finset VarId}
    {Parameter : Type} (program : SourceProgram Player L Γ O)
    (profile : BehavioralProfile program) (policy : BehavioralPolicy who program)
    (original replacement : List (OwnAction Player L)) (belief : FinDist (Config Player L Γ))
    (past : ∀ config ∈ belief.support, config.history who = original)
    (parameter : Config Player L Γ → Parameter) :
    (belief.bind fun config =>
      (runFrom program (Function.update profile who
        (policy.rebaseHistory original.length replacement program)) config).map
          (fun result => (parameter config, result))) =
      belief.bind fun config =>
        (runFrom program (Function.update profile who policy)
          (config.withOwnHistory who replacement)).map
            (fun result => (parameter config, result)) := by
  apply FinDist.bind_congr
  intro config supported
  rw [rebaseHistory_runFrom program profile policy original replacement config
    (past config supported)]

end Vegas.SourceProgram
