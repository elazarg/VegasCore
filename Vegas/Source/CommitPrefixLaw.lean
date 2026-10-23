/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBlockLift
import GameTheory.Math.Probability.Conditioning

/-! # Behavioral laws of typed commitment prefixes

The existing source commitment kernels are composed at their successive full
configurations. Each repeated owner's later decision sees its earlier sampled
actions. Conditioning is performed on the resulting joint law, rather than
fixing later observed values before sampling an earlier hidden choice.
-/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- The original structural profile after consuming the commitment segment. -/
def tailProfile : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : CommitPrefix Γ O Δ P) → (suffix : SourceProgram Player L Δ P) →
    BehavioralProfile (block.prepend suffix) → BehavioralProfile suffix
  | _, _, _, _, .nil, _, profile => profile
  | _, _, _, _, .commit _ _ _ _ rest, suffix, profile =>
      tailProfile rest suffix (afterCommit profile)

/-- Draw the source prefix using its original commitment kernels at the
updated semantic state and complete own-action history. -/
def prefixLaw : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    (block : CommitPrefix Γ O Δ P) → (suffix : SourceProgram Player L Δ P) →
    BehavioralProfile (block.prepend suffix) → Config Player L Γ → PMF (Config Player L Δ)
  | _, _, _, _, .nil, _, _, entry => PMF.pure entry
  | _, _, _, _, .commit name owner _ guard rest, suffix, profile, entry =>
      (commitKernel profile (entry.view owner)).bind fun result =>
        prefixLaw rest suffix (afterCommit profile) (commitSuccessor name guard entry result)

/-- Every supported draw is an actual typed source attempt. No physical
omission or new exclusion is fabricated by sampling a hidden failed result. -/
theorem prefixLaw_attempt (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (final : Config Player L Δ)
    (supported : final ∈ (block.prefixLaw suffix profile entry).support) :
    Nonempty (block.Attempt entry ∅ final ∅) := by
  induction block with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨.nil entry ∅⟩
  | commit name owner fresh guard rest ih =>
      obtain ⟨result, _drawn, later⟩ := (PMF.mem_support_bind_iff ..).mp supported
      obtain ⟨attempt⟩ := ih suffix (afterCommit profile)
        (commitSuccessor name guard entry result) final later
      exact ⟨.active (Finset.notMem_empty owner) result false
        (by intro impossible; cases impossible) attempt⟩

end Vegas.SourceProgram.CommitPrefix
