/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup

/-! # Finitely branching source runs

Chance laws are exact finite tables and disclosures are Boolean, so a run
branches finitely exactly when every commitment kernel it consults does. That
holds for every profile when fresh binding types are finite; over an infinite
binding alphabet it is a property of the profile.
-/

noncomputable section
namespace Vegas.SourceProgram

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every commitment kernel of the profile has finite support at every view. -/
def BehavioralProfile.FiniteSupport : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralProfile p → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ k, profile => BehavioralProfile.FiniteSupport k (afterSample profile)
  | _, _, .commit _ _ _ _ k, profile =>
      (∀ view, (commitKernel profile view).support.Finite) ∧
        BehavioralProfile.FiniteSupport k (afterCommit profile)
  | _, _, .reveal _ _ _ _ _ _ k, profile =>
      BehavioralProfile.FiniteSupport k (afterReveal profile)

/-- Finite fresh-binding alphabets make every profile finitely branching. -/
theorem FiniteBindingTypes.profileFiniteSupport :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    p.FiniteBindingTypes → (profile : BehavioralProfile p) →
    BehavioralProfile.FiniteSupport p profile
  | _, _, .ret _, _, _ => trivial
  | _, _, .sample _ _ _ k, finite, profile =>
      profileFiniteSupport k finite (afterSample profile)
  | _, _, .commit _ _ _ _ k, finite, profile =>
      have := finite.1
      ⟨fun _ => Set.toFinite _, profileFiniteSupport k finite.2 (afterCommit profile)⟩
  | _, _, .reveal _ _ _ _ _ _ k, finite, profile =>
      profileFiniteSupport k finite (afterReveal profile)

/-- A finitely branching profile has a finitely supported run from every
configuration. -/
theorem runFrom_support_finite : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → (profile : BehavioralProfile p) →
    BehavioralProfile.FiniteSupport p profile → (config : Config Player L Γ) →
    (runFrom p profile config).support.Finite
  | _, _, .ret _, _, _, config => by
      change (PMF.pure config.state).support.Finite
      rw [PMF.support_pure]
      exact Set.finite_singleton _
  | _, _, .sample _ _ _ k, profile, finite, config => by
      rw [runFrom_sample, PMF.support_bind]
      exact (L.evalDist_support_finite _ _).biUnion fun _ _ =>
        runFrom_support_finite k _ finite _
  | _, _, .commit _ _ _ _ k, profile, finite, config => by
      rw [runFrom_commit, PMF.support_bind]
      exact (finite.1 _).biUnion fun _ _ => runFrom_support_finite k _ finite.2 _
  | _, _, .reveal _ _ _ _ _ _ k, profile, finite, config => by
      rw [runFrom_reveal, PMF.support_bind]
      exact (Set.toFinite _).biUnion fun _ _ => runFrom_support_finite k _ finite _

/-- A finitely supported initial law and a finitely branching profile give a
finitely supported setup run. -/
theorem Setup.run_support_finite (setup : Setup (Player := Player) (L := L))
    (initialFinite : setup.initialLaw.support.Finite) (profile : BehavioralProfile setup.program)
    (finite : BehavioralProfile.FiniteSupport setup.program profile) :
    (setup.run profile).support.Finite := by
  rw [Setup.run, PMF.support_bind]
  exact initialFinite.biUnion fun initial _ => runFrom_support_finite _ _ finite
    ⟨initial, [], Revelations.initial setup.context, fun _ => []⟩

end Vegas.SourceProgram
