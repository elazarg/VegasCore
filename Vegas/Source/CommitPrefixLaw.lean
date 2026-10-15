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

/-- Prefix sampling factors the actual source continuation law exactly. The
continuation is evaluated in the original program, so no terminal cast is hidden. -/
theorem prefixLaw_continuation (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) :
    (block.prefixLaw suffix profile entry).bind (fun final =>
      ProtocolState.continuationLaw (block.prepend suffix) profile
        (block.liftPoint suffix (ProtocolState.entry suffix final))) =
      runFrom (block.prepend suffix) profile entry := by
  induction block with
  | nil => simp only [prefixLaw, liftPoint, prepend, PMF.pure_bind,
      ProtocolState.continuationLaw_entry]
  | commit name owner fresh guard rest ih =>
      simp only [prefixLaw, prepend, PMF.bind_bind, runFrom_commit]
      apply congrArg (PMF.bind (commitKernel profile (entry.view owner)))
      funext result
      exact ih suffix (afterCommit profile) (commitSuccessor name guard entry result)

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

/-- Finite branching of the original source profile gives a finite joint
prefix law without treating different occurrences of one owner independently. -/
theorem prefixLaw_support_finite (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (finite : BehavioralProfile.FiniteSupport (block.prepend suffix) profile)
    (entry : Config Player L Γ) : (block.prefixLaw suffix profile entry).support.Finite := by
  induction block with
  | nil =>
      rw [prefixLaw, PMF.support_pure]
      exact Set.finite_singleton _
  | commit name owner fresh guard rest ih =>
      rw [prefixLaw, PMF.support_bind]
      exact (finite.1 _).biUnion fun result _ =>
        ih suffix (afterCommit profile) finite.2 (commitSuccessor name guard entry result)

/-- Complete the latent source choices conditional on this player's actual
semantic cells and full effective own-action word. Zero-mass fibers use the
existing total conditional-law convention. -/
def prefixPosterior (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (who : Player) (observed : DecisionView who Δ) :
    PMF (Config Player L Δ) :=
  fiberPosterior (block.prefixLaw suffix profile entry) (Config.view who) observed

/-- A positive-mass current view yields genuine supported source attempts
with exactly the same semantic observation and the whole own-action word. -/
theorem prefixPosterior_supported (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (who : Player) (observed : DecisionView who Δ)
    (present : observed ∈ ((block.prefixLaw suffix profile entry).map (Config.view who)).support)
    (final : Config Player L Δ)
    (supported : final ∈ (block.prefixPosterior suffix profile entry who observed).support) :
    final.view who = observed ∧ Nonempty (block.Attempt entry ∅ final ∅) := by
  obtain ⟨same, drawn⟩ := mem_support_fiberPosterior present supported
  exact ⟨same, block.prefixLaw_attempt suffix profile entry final drawn⟩

/-- Sampling the visible prefix and then its latent conditional completion
recovers the original joint prefix distribution, including repeated-owner dependence. -/
theorem prefixPosterior_reconstruct (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (who : Player) :
    ((block.prefixLaw suffix profile entry).map (Config.view who)).bind
      (block.prefixPosterior suffix profile entry who) = block.prefixLaw suffix profile entry :=
  fiberPosterior_reconstruct _ _

/-- Conditioning and resampling the latent prefix before the actual remaining
source continuation preserves its complete terminal distribution. -/
theorem prefixPosterior_continuation (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (profile : BehavioralProfile (block.prepend suffix))
    (entry : Config Player L Γ) (who : Player) :
    (((block.prefixLaw suffix profile entry).map (Config.view who)).bind
      (block.prefixPosterior suffix profile entry who)).bind (fun final =>
        ProtocolState.continuationLaw (block.prepend suffix) profile
          (block.liftPoint suffix (ProtocolState.entry suffix final))) =
      runFrom (block.prepend suffix) profile entry := by
  rw [prefixPosterior_reconstruct]
  exact block.prefixLaw_continuation suffix profile entry

end Vegas.SourceProgram.CommitPrefix
