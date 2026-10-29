/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Semantics

/-! # Syntax-determined source metadata

Registry and revelation metadata follow the remaining syntax independently of
player decisions. The evaluator retains precisely these fields, allowing a
compiler readout to reconstruct them without another execution semantics.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The revelations after following the remaining source syntax. -/
def finalRevelations : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Revelations Γ →
      Revelations (terminalCtx program)
  | _, _, .ret _, revelations => revelations
  | _, _, .sample _ _ _ next, revelations => finalRevelations next revelations.weaken
  | _, _, .commit _ _ _ _ next, revelations => finalRevelations next revelations.weaken
  | _, _, .reveal published _ _ _ source _ next, revelations =>
      finalRevelations next (revelations.reveal (published := published) source)

/-- The guard registry obtained after following the remaining source syntax.
It retains every original typed guard and its subject provenance. -/
def finalRegistry : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ →
      Registry (terminalCtx program)
  | _, _, .ret _, registry => registry
  | _, _, .sample _ _ _ next, registry => finalRegistry next registry.weaken
  | _, _, .commit name owner _ guard next, registry =>
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      finalRegistry next (obligation :: registry.weaken)
  | _, _, .reveal _ _ _ _ _ _ next, registry => finalRegistry next registry.weaken

/-- Every supported terminal configuration retains the syntax-determined
registry and revelations, independently of all decisions and prior defaults. -/
theorem runFrom_metadata : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile program) → (config : Config Player L Γ) →
    (final : Config Player L program.terminalCtx) →
    final ∈ (runFrom program profile config).support →
      final.registry = finalRegistry program config.registry ∧
        @Eq (Revelations program.terminalCtx) final.revelations
          (finalRevelations program config.revelations)
  | _, _, .ret _, _, config, final, reached => by
      have same : final = config := by simpa [runFrom] using reached
      subst final
      exact ⟨rfl, rfl⟩
  | _, _, .sample name _ law next, profile, config, final, reached => by
      simp only [runFrom, PMF.support_bind, Set.mem_iUnion] at reached
      obtain ⟨value, _, reached⟩ := reached
      simpa only [finalRegistry, finalRevelations, sampleSuccessor] using
        runFrom_metadata next (afterSample profile)
          (sampleSuccessor name config value) final reached
  | _, _, .commit name _ _ guard next, profile, config, final, reached => by
      simp only [runFrom, PMF.support_bind, Set.mem_iUnion] at reached
      obtain ⟨choice, _, reached⟩ := reached
      simpa only [finalRegistry, finalRevelations, commitSuccessor] using
        runFrom_metadata next (afterCommit profile)
          (commitSuccessor name guard config choice) final reached
  | _, _, .reveal published _ _ _ source _ next, profile, config, final, reached => by
      simp only [runFrom, PMF.support_bind, Set.mem_iUnion] at reached
      obtain ⟨disclose, _, reached⟩ := reached
      simpa only [finalRegistry, finalRevelations, revealSuccessor] using
        runFrom_metadata next (afterReveal profile)
          (revealSuccessor published source config disclose) final reached

end Vegas.SourceProgram
