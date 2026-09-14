/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.Strategy
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Exact point masses of written-source execution

The terminal environment retains every source binding. It therefore identifies
each earlier draw, even when the queried terminal environment has probability
zero. Its mass factors into the actual conditional source-kernel probabilities
and the final environment-consistency check. No independence of draws is assumed.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Forget bindings introduced by a source continuation. This projects an
existing terminal environment; it does not execute a program. -/
def sourceInitialProjection : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    VEnv L (sourceTerminalCtx prog) → VEnv L Γ
  | _, .ret _, final => final
  | _, .sample _ _ tail, final => (sourceInitialProjection tail final).tail
  | _, .commit _ _ _ tail, final => (sourceInitialProjection tail final).tail
  | _, .reveal _ _ _ _ tail, final => (sourceInitialProjection tail final).tail

/-- Project the bindings retained immediately after a source decision from
the terminal environment. This reads recorded source values; it supplies no
additional information to a policy and does not execute a continuation. -/
def SourceDecisionSite.recorded {who : P} {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {Δ : VCtx P L} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool} :
    SourceDecisionSite who prog Δ name ty guard → VEnv L (sourceTerminalCtx prog) →
      VEnv L ((name, .sealed who ty) :: Δ)
  | .here _ tail, final => sourceInitialProjection tail final
  | .sample site, final => site.recorded final
  | .commit site, final => site.recorded final
  | .reveal site, final => site.recorded final

/-- The terminal record contains `value` at a commitment belonging to `who`.
This describes recorded source choices, not the observations available to a
policy. Legality of the complete record is a separate execution property. -/
def VegasCore.Chooses {Γ : VCtx P L} (prog : VegasCore P L Γ) (who : P)
    {ty : L.Ty} (value : L.Val ty) (final : VEnv L (sourceTerminalCtx prog)) : Prop :=
  ∃ Δ name guard, ∃ site : SourceDecisionSite who prog Δ name ty guard,
    (site.recorded final).get .here = value

/-- Source execution preserves its initial bindings in the terminal result. -/
theorem denoteSource_initialProjection : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (profile : SourceBehavioralProfile prog) → (env : VEnv L Γ) →
    (final : VEnv L (sourceTerminalCtx prog)) →
    final ∈ (denoteSource prog profile env).support → sourceInitialProjection prog final = env
  | _, .ret _, _, _, _, hfinal => FinDist.mem_support_pure.mp hfinal
  | _, .sample _ _ tail, profile, env, final, hfinal => by
      simp only [denoteSource, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨value, _, htail⟩ := hfinal
      change (sourceInitialProjection tail final).tail = env
      rw [denoteSource_initialProjection tail profile.afterSample (env.cons value) final htail,
        VEnv.tail_cons]
  | _, .commit _ _ _ tail, profile, env, final, hfinal => by
      simp only [denoteSource, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨choice, _, htail⟩ := hfinal
      change (sourceInitialProjection tail final).tail = env
      rw [denoteSource_initialProjection tail profile.afterCommit (env.cons choice.1) final htail,
        VEnv.tail_cons]
  | _, .reveal _ _ _ _ tail, profile, env, final, hfinal => by
      change (sourceInitialProjection tail final).tail = env
      rw [denoteSource_initialProjection tail profile.afterReveal _ final hfinal, VEnv.tail_cons]

/-- An outcome of a source continuation identifies the value supplied at its
head binding, so a preceding draw contributes exactly one conditional factor. -/
theorem denoteSource_bind_cons_prob {Γ : VCtx P L} {name : VarId} {binding : BindTy P L}
    (tail : VegasCore P L ((name, binding) :: Γ)) (profile : SourceBehavioralProfile tail)
    (env : VEnv L Γ) (law : FinDist (L.Val binding.base))
    (final : VEnv L (sourceTerminalCtx tail)) :
    (law.bind fun value => denoteSource tail profile (env.cons value)).prob final =
      law.prob ((sourceInitialProjection tail final).get .here) *
        (denoteSource tail profile
          (env.cons ((sourceInitialProjection tail final).get .here))).prob final := by
  apply FinDist.prob_bind_of_unique_branch
  intro value _ hfinal
  rw [denoteSource_initialProjection tail profile (env.cons value) final hfinal,
    VEnv.cons_get_here]

/-- A source commitment contributes the mass of its retained value. -/
theorem denoteSource_prob_commit {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (profile : SourceBehavioralProfile (.commit name who guard tail)) (env : VEnv L Γ)
    (final : VEnv L (sourceTerminalCtx tail)) :
    (denoteSource (.commit name who guard tail) profile env).prob final =
      ((profile who (.here guard tail) (env.toView who).eraseEnv).map Subtype.val).prob
          ((sourceInitialProjection tail final).get .here) *
        (denoteSource tail profile.afterCommit
          (env.cons ((sourceInitialProjection tail final).get .here))).prob final := by
  have hbind := FinDist.bind_map Subtype.val
    (profile who (.here guard tail) (env.toView who).eraseEnv)
    (fun value => denoteSource tail profile.afterCommit (env.cons value))
  exact (congrArg (fun law => law.prob final) hbind.symm).trans
    (denoteSource_bind_cons_prob tail profile.afterCommit env _ final)

/-- The exact point-mass factors of existing source execution. A sample or
commitment contributes its conditional draw probability at the value retained
by the queried final environment; reveals use their ordinary deterministic
semantics. The last factor checks equality at `ret`. -/
def sourcePointFactors : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    SourceBehavioralProfile prog → VEnv L Γ →
    VEnv L (sourceTerminalCtx prog) → List ℝ
  | _, .ret _, _, env, final => [(FinDist.pure env).prob final]
  | _, .sample _ dist tail, profile, env, final =>
      let value := (sourceInitialProjection tail final).get .here
      (L.evalDist dist env.eraseSampleEnv).prob value ::
        sourcePointFactors tail profile.afterSample (env.cons value) final
  | _, .commit _ who guard tail, profile, env, final =>
      let value := (sourceInitialProjection tail final).get .here
      ((profile who (.here guard tail) (env.toView who).eraseEnv).map Subtype.val).prob value ::
        sourcePointFactors tail profile.afterCommit (env.cons value) final
  | _, .reveal _ who name source tail, profile, env, final =>
      sourcePointFactors tail profile.afterReveal
        (env.cons (@VEnv.get P L _ name (.sealed who _) env source)) final

/-- Whole-program source probabilities are products of their conditional
factors. This holds for every queried terminal environment, not only supported
ones, and includes samples, nontrivial guards, and dependent honest choices. -/
theorem denoteSource_prob_eq_prod : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (profile : SourceBehavioralProfile prog) → (env : VEnv L Γ) →
    (final : VEnv L (sourceTerminalCtx prog)) →
    (denoteSource prog profile env).prob final = (sourcePointFactors prog profile env final).prod
  | _, .ret _, _, _, _ => by simp only [denoteSource, sourcePointFactors, List.prod_singleton]
  | _, .sample _ dist tail, profile, env, final => by
      change ((L.evalDist dist env.eraseSampleEnv).bind fun value =>
        denoteSource tail profile.afterSample (env.cons value)).prob final = _
      exact (denoteSource_bind_cons_prob tail profile.afterSample env _ final).trans
        (congrArg ((L.evalDist dist env.eraseSampleEnv).prob
          ((sourceInitialProjection tail final).get .here) * ·)
          (denoteSource_prob_eq_prod tail profile.afterSample _ final))
  | _, .commit _ who guard tail, profile, env, final => by
      exact (denoteSource_prob_commit guard tail profile env final).trans
        (congrArg (((profile who (.here guard tail) (env.toView who).eraseEnv).map
          Subtype.val).prob ((sourceInitialProjection tail final).get .here) * ·)
          (denoteSource_prob_eq_prod tail profile.afterCommit _ final))
  | _, .reveal _ _ _ _ tail, profile, env, final => by
      exact denoteSource_prob_eq_prod tail profile.afterReveal _ final

end Vegas

/-- info: 'Vegas.denoteSource_prob_eq_prod' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.denoteSource_prob_eq_prod
