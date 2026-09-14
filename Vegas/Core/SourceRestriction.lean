/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.SourceLikelihood

/-! # Probabilities of constraints on source choices

A restriction supplies a legal forced value at selected source inputs and
leaves every other kernel unchanged. Its application is an ordinary source
profile, evaluated by `denoteSource`. Weighting this normalized execution by
the original probabilities of forced choices computes the probability that
the original execution satisfies the restriction. The identity is valid for
dependent choices and zero-probability events; it uses no conditioning.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Optional legal choices, selected using exactly the source policy input.
`none` retains the original kernel; `some` fixes a choice for this analysis.
A forced nullable quit is `some` of a legal `none` value. -/
def SourceChoiceRestriction {Γ : VCtx P L} (prog : VegasCore P L Γ) :=
  ∀ who {Δ x b guard}, SourceDecisionSite who prog Δ x b guard →
    (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      Option {value : L.Val b // evalGuard guard value visible = true}

namespace SourceChoiceRestriction

def apply {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (restriction : SourceChoiceRestriction prog) (profile : SourceBehavioralProfile prog) :
    SourceBehavioralProfile prog :=
  fun who _ _ _ _ site visible =>
    match restriction who site visible with
    | none => profile who site visible
    | some value => FinDist.pure value

def afterSample {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) b} {tail : VegasCore P L ((x, .pub b) :: Γ)}
    (restriction : SourceChoiceRestriction (.sample x dist tail)) :
    SourceChoiceRestriction tail :=
  fun who _ _ _ _ site => restriction who (.sample (Γ := Γ) site)

def afterCommit {Γ : VCtx P L} {x : VarId} {actor : P} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx actor Γ)) L.bool}
    {tail : VegasCore P L ((x, .sealed actor b) :: Γ)}
    (restriction : SourceChoiceRestriction (.commit x actor guard tail)) :
    SourceChoiceRestriction tail :=
  fun who _ _ _ _ site => restriction who (.commit (Γ := Γ) site)

def afterReveal {Γ : VCtx P L} {y : VarId} {actor : P} {x : VarId} {b : L.Ty}
    {source : VHasVar Γ x (.sealed actor b)} {tail : VegasCore P L ((y, .pub b) :: Γ)}
    (restriction : SourceChoiceRestriction (.reveal y actor x source tail)) :
    SourceChoiceRestriction tail :=
  fun who _ _ _ _ site => restriction who (.reveal (Γ := Γ) site)

/-- Check the retained choices against the restriction, using the ordinary
source views along the queried terminal environment. -/
def Allows : {Γ : VCtx P L} → {prog : VegasCore P L Γ} → SourceChoiceRestriction prog →
    VEnv L Γ → VEnv L (sourceTerminalCtx prog) → Prop
  | _, .ret _, _, _, _ => True
  | _, .sample _ _ tail, restriction, env, final =>
      restriction.afterSample.Allows
        (env.cons ((sourceInitialProjection tail final).get .here)) final
  | _, .commit _ who guard tail, restriction, env, final =>
      let value := (sourceInitialProjection tail final).get .here
      (match restriction who (.here guard tail) (env.toView who).eraseEnv with
        | none => True
        | some fixed => value = fixed.1) ∧
      restriction.afterCommit.Allows (env.cons value) final
  | _, .reveal _ who name source _, restriction, env, final =>
      restriction.afterReveal.Allows
        (env.cons (@VEnv.get P L _ name (.sealed who _) env source)) final

/-- Product of the original conditional probabilities of forced choices.
Unrestricted samples and decisions are still drawn by the reference execution,
so they contribute no likelihood correction. -/
def weight : {Γ : VCtx P L} → {prog : VegasCore P L Γ} → SourceChoiceRestriction prog →
    SourceBehavioralProfile prog → VEnv L Γ → VEnv L (sourceTerminalCtx prog) → ℝ
  | _, .ret _, _, _, _, _ => 1
  | _, .sample _ _ tail, restriction, profile, env, final =>
      restriction.afterSample.weight profile.afterSample
        (env.cons ((sourceInitialProjection tail final).get .here)) final
  | _, .commit _ who guard tail, restriction, profile, env, final =>
      (match restriction who (.here guard tail) (env.toView who).eraseEnv with
        | none => 1
        | some fixed =>
            ((profile who (.here guard tail) (env.toView who).eraseEnv).map Subtype.val).prob
              fixed.1) *
      restriction.afterCommit.weight profile.afterCommit
        (env.cons ((sourceInitialProjection tail final).get .here)) final
  | _, .reveal _ who name source _, restriction, profile, env, final =>
      restriction.afterReveal.weight profile.afterReveal
        (env.cons (@VEnv.get P L _ name (.sealed who _) env source)) final

end SourceChoiceRestriction

/-- Owners and instruction positions of source commitments, in written order.
Samples and reveals advance the instruction position without adding a decision. -/
def VegasCore.decisionPositions : {Γ : VCtx P L} → VegasCore P L Γ → List (P × Nat)
  | _, .ret _ => []
  | _, .sample _ _ tail => tail.decisionPositions.map fun slot => (slot.1, slot.2 + 1)
  | _, .commit _ who _ tail =>
      (who, 0) :: tail.decisionPositions.map fun slot => (slot.1, slot.2 + 1)
  | _, .reveal _ _ _ _ tail => tail.decisionPositions.map fun slot => (slot.1, slot.2 + 1)

/-- The restriction likelihood is a product indexed by source decisions.
Factors may be specified in another execution order: only their value at each
recorded source input matters. The reference profile need not be the profile
whose probabilities supply the factors. -/
theorem SourceChoiceRestriction.weight_eq_decision_product : {Γ : VCtx P L} →
    (prog : VegasCore P L Γ) → (profile reference : SourceBehavioralProfile prog) →
    (restriction : SourceChoiceRestriction prog) → (env : VEnv L Γ) →
    (final : VEnv L (sourceTerminalCtx prog)) →
    final ∈ (denoteSource prog reference env).support → (factor : P → Nat → ℝ) →
    (∀ who {Δ name ty guard} (site : SourceDecisionSite who prog Δ name ty guard),
      let visible := ((site.recorded final).tail.toView who).eraseEnv
      (restriction who site visible = none → factor who site.depth = 1) ∧
      (∀ fixed, restriction who site visible = some fixed →
        factor who site.depth = ((profile who site visible).map Subtype.val).prob fixed.1)) →
    restriction.weight profile env final =
      (prog.decisionPositions.map fun slot => factor slot.1 slot.2).prod
  | _, .ret _, _, _, _, _, _, _, _, _ => rfl
  | _, .sample _ _ tail, profile, reference, restriction, env, final, hfinal, factor, hfactor => by
      change VEnv L (sourceTerminalCtx tail) at final
      simp only [denoteSource, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨value, _, htail⟩ := hfinal
      change restriction.afterSample.weight profile.afterSample
        (env.cons ((sourceInitialProjection tail final).get .here)) final = _
      rw [denoteSource_initialProjection tail _ (env.cons value) final htail, VEnv.cons_get_here]
      simp only [VegasCore.decisionPositions, List.map_map, Function.comp_def]
      apply SourceChoiceRestriction.weight_eq_decision_product tail profile.afterSample
        reference.afterSample restriction.afterSample (env.cons value) final htail
        (fun who depth => factor who (depth + 1))
      intro who Δ name ty guard site
      exact hfactor who (.sample site)
  | _, .commit _ actor sourceGuard tail, profile, reference, restriction, env, final,
      hfinal, factor, hfactor => by
      change VEnv L (sourceTerminalCtx tail) at final
      simp only [denoteSource, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨choice, _, htail⟩ := hfinal
      have hprojection := denoteSource_initialProjection tail _ (env.cons choice.1) final htail
      change (match restriction actor (.here sourceGuard tail) (env.toView actor).eraseEnv with
        | none => 1
        | some fixed =>
            ((profile actor (.here sourceGuard tail) (env.toView actor).eraseEnv).map
              Subtype.val).prob fixed.1) *
        restriction.afterCommit.weight profile.afterCommit
          (env.cons ((sourceInitialProjection tail final).get .here)) final = _
      rw [hprojection, VEnv.cons_get_here]
      have hhead := hfactor actor (.here sourceGuard tail)
      simp only [SourceDecisionSite.recorded] at hhead
      erw [hprojection] at hhead
      have htailFactors := SourceChoiceRestriction.weight_eq_decision_product tail
        profile.afterCommit reference.afterCommit restriction.afterCommit (env.cons choice.1)
        final htail (fun who depth => factor who (depth + 1))
        (fun who _ _ _ _ site => hfactor who (.commit site))
      rw [htailFactors]
      simp only [VegasCore.decisionPositions, List.map_cons, List.map_map, Function.comp_def,
        List.prod_cons]
      congr 1
      cases hfixed : restriction actor (.here sourceGuard tail) (env.toView actor).eraseEnv with
      | none => exact (hhead.1 hfixed).symm
      | some fixed => exact (hhead.2 fixed hfixed).symm
  | _, .reveal _ actor name source tail, profile, reference, restriction, env, final,
      hfinal, factor, hfactor => by
      simp only [VegasCore.decisionPositions, List.map_map, Function.comp_def]
      apply SourceChoiceRestriction.weight_eq_decision_product tail profile.afterReveal
        reference.afterReveal restriction.afterReveal
        (env.cons (@VEnv.get P L _ name (.sealed actor _) env source)) final hfinal
        (fun who depth => factor who (depth + 1))
      intro who Δ name ty guard site
      exact hfactor who (.reveal site)

/-- On an actual source outcome, restriction acceptance is exactly agreement
at every selected decision occurrence. Its inputs and chosen values are read
from that same terminal source environment. -/
theorem SourceChoiceRestriction.allows_iff_recorded : {Γ : VCtx P L} →
    (prog : VegasCore P L Γ) → (profile : SourceBehavioralProfile prog) →
    (restriction : SourceChoiceRestriction prog) → (env : VEnv L Γ) →
    (final : VEnv L (sourceTerminalCtx prog)) →
    final ∈ (denoteSource prog profile env).support →
    (restriction.Allows env final ↔ ∀ who {Δ name ty guard}
      (site : SourceDecisionSite who prog Δ name ty guard) fixed,
      restriction who site ((site.recorded final).tail.toView who).eraseEnv = some fixed →
        (site.recorded final).get .here = fixed.1)
  | _, .ret _, _, _, _, _, _ => by
      constructor
      · intro _ who Δ name ty guard site
        cases site
      · intro _
        trivial
  | _, .sample _ _ tail, profile, restriction, env, final, hfinal => by
      change VEnv L (sourceTerminalCtx tail) at final
      simp only [denoteSource, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨value, _, htail⟩ := hfinal
      change restriction.afterSample.Allows
        (env.cons ((sourceInitialProjection tail final).get .here)) final ↔ _
      rw [denoteSource_initialProjection tail _ (env.cons value) final htail, VEnv.cons_get_here]
      have ih := SourceChoiceRestriction.allows_iff_recorded tail profile.afterSample
        restriction.afterSample (env.cons value) final htail
      constructor
      · intro h who Δ name ty guard site
        cases site with
        | sample site =>
            simpa only [SourceChoiceRestriction.afterSample, SourceDecisionSite.recorded]
              using ih.mp h who site
      · intro h
        apply ih.mpr
        intro who Δ name ty guard site
        simpa only [SourceChoiceRestriction.afterSample, SourceDecisionSite.recorded]
          using h who (.sample site)
  | _, .commit _ actor sourceGuard tail, profile, restriction, env, final, hfinal => by
      change VEnv L (sourceTerminalCtx tail) at final
      simp only [denoteSource, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨choice, _, htail⟩ := hfinal
      have hprojection := denoteSource_initialProjection tail _ (env.cons choice.1) final htail
      change (match restriction actor (.here sourceGuard tail) (env.toView actor).eraseEnv with
        | none => True
        | some fixed => (sourceInitialProjection tail final).get .here = fixed.1) ∧
          restriction.afterCommit.Allows
            (env.cons ((sourceInitialProjection tail final).get .here)) final ↔ _
      rw [hprojection, VEnv.cons_get_here]
      have hhead :
          (match restriction actor (.here sourceGuard tail) (env.toView actor).eraseEnv with
          | none => True
          | some fixed => choice.1 = fixed.1) ↔
          ∀ fixed, restriction actor (.here sourceGuard tail) (env.toView actor).eraseEnv =
            some fixed → choice.1 = fixed.1 := by
        cases restriction actor (.here sourceGuard tail) (env.toView actor).eraseEnv <;> simp
      rw [hhead]
      have ih := SourceChoiceRestriction.allows_iff_recorded tail profile.afterCommit
        restriction.afterCommit (env.cons choice.1) final htail
      constructor
      · intro h who Δ name ty guard site
        cases site with
        | here =>
            simp only [SourceDecisionSite.recorded]
            erw [hprojection]
            exact h.1
        | commit site =>
            simpa only [SourceChoiceRestriction.afterCommit, SourceDecisionSite.recorded]
              using ih.mp h.2 who site
      · intro h
        constructor
        · have hcurrent := h actor (.here sourceGuard tail)
          simp only [SourceDecisionSite.recorded] at hcurrent
          erw [hprojection] at hcurrent
          exact hcurrent
        · apply ih.mpr
          intro who Δ name ty guard site
          simpa only [SourceChoiceRestriction.afterCommit, SourceDecisionSite.recorded]
            using h who (.commit site)
  | _, .reveal _ actor name source tail, profile, restriction, env, final, hfinal => by
      have ih := SourceChoiceRestriction.allows_iff_recorded tail profile.afterReveal
        restriction.afterReveal
        (env.cons (@VEnv.get P L _ name (.sealed actor _) env source)) final hfinal
      constructor
      · intro h who Δ name ty guard site
        cases site with
        | reveal site =>
            simpa only [SourceChoiceRestriction.afterReveal, SourceDecisionSite.recorded]
              using ih.mp h who site
      · intro h
        apply ih.mpr
        intro who Δ name ty guard site
        simpa only [SourceChoiceRestriction.afterReveal, SourceDecisionSite.recorded]
          using h who (.reveal site)

/-- Every run of the restricted profile satisfies the selected choices,
irrespective of whether those choices have positive mass in the original profile. -/
theorem denoteSource_restriction_support : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (profile : SourceBehavioralProfile prog) → (restriction : SourceChoiceRestriction prog) →
    (env : VEnv L Γ) → (final : VEnv L (sourceTerminalCtx prog)) →
    final ∈ (denoteSource prog (restriction.apply profile) env).support →
      restriction.Allows env final
  | _, .ret _, _, _, _, _, _ => trivial
  | _, .sample _ _ tail, profile, restriction, env, final, hfinal => by
      simp only [denoteSource, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨value, _, htail⟩ := hfinal
      change restriction.afterSample.Allows
        (env.cons ((sourceInitialProjection tail final).get .here)) final
      rw [denoteSource_initialProjection tail _ (env.cons value) final htail, VEnv.cons_get_here]
      exact denoteSource_restriction_support tail profile.afterSample restriction.afterSample
        (env.cons value) final htail
  | _, .commit _ who guard tail, profile, restriction, env, final, hfinal => by
      simp only [denoteSource, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨choice, hchoice, htail⟩ := hfinal
      change (match restriction who (.here guard tail) (env.toView who).eraseEnv with
        | none => True
        | some fixed => (sourceInitialProjection tail final).get .here = fixed.1) ∧ _
      rw [denoteSource_initialProjection tail _ (env.cons choice.1) final htail,
        VEnv.cons_get_here]
      constructor
      · cases hfixed : restriction who (.here guard tail) (env.toView who).eraseEnv with
        | none => trivial
        | some fixed =>
            change choice ∈ (restriction.apply profile who (.here guard tail)
              (env.toView who).eraseEnv).support at hchoice
            simp only [SourceChoiceRestriction.apply, hfixed, FinDist.mem_support_pure] at hchoice
            exact congrArg Subtype.val hchoice
      · exact denoteSource_restriction_support tail profile.afterCommit restriction.afterCommit
          (env.cons choice.1) final htail
  | _, .reveal _ _ _ _ tail, profile, restriction, env, final, hfinal =>
      denoteSource_restriction_support tail profile.afterReveal restriction.afterReveal
        _ final hfinal

open Classical in
/-- Pointwise change of source law under legal forced choices. The identity
includes terminal environments outside either law's support. -/
theorem denoteSource_restriction_density : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (profile : SourceBehavioralProfile prog) → (restriction : SourceChoiceRestriction prog) →
    (env : VEnv L Γ) → (final : VEnv L (sourceTerminalCtx prog)) →
    (if restriction.Allows env final then (denoteSource prog profile env).prob final else 0) =
      restriction.weight profile env final *
        (denoteSource prog (restriction.apply profile) env).prob final
  | _, .ret _, _, _, _, _ => by simp only [SourceChoiceRestriction.Allows,
      SourceChoiceRestriction.weight, ↓reduceIte, denoteSource, one_mul]
  | _, .sample _ dist tail, profile, restriction, env, final => by
      classical
      let value := (sourceInitialProjection tail final).get .here
      have ih := denoteSource_restriction_density tail profile.afterSample
        restriction.afterSample (env.cons value) final
      have horiginal := denoteSource_bind_cons_prob tail profile.afterSample env
        (L.evalDist dist env.eraseSampleEnv) final
      have hrestricted := denoteSource_bind_cons_prob tail
        (restriction.afterSample.apply profile.afterSample) env
        (L.evalDist dist env.eraseSampleEnv) final
      change (if restriction.afterSample.Allows (env.cons value) final then
        ((L.evalDist dist env.eraseSampleEnv).bind fun v =>
          denoteSource tail profile.afterSample (env.cons v)).prob final else 0) =
        restriction.afterSample.weight profile.afterSample (env.cons value) final *
          ((L.evalDist dist env.eraseSampleEnv).bind fun v =>
            denoteSource tail (restriction.afterSample.apply profile.afterSample)
              (env.cons v)).prob final
      rw [horiginal, hrestricted]
      by_cases hallow : restriction.afterSample.Allows (env.cons value) final
      · rw [if_pos hallow] at ih ⊢
        rw [ih]
        ring
      · rw [if_neg hallow] at ih ⊢
        rw [mul_left_comm, ← ih, mul_zero]
  | _, .commit _ who guard tail, profile, restriction, env, final => by
      classical
      change VEnv L (sourceTerminalCtx tail) at final
      let value := (sourceInitialProjection tail final).get .here
      have ih := denoteSource_restriction_density tail profile.afterCommit
        restriction.afterCommit (env.cons value) final
      cases hfixed : restriction who (.here guard tail) (env.toView who).eraseEnv with
      | none =>
          rw [denoteSource_prob_commit, denoteSource_prob_commit]
          simp only [SourceChoiceRestriction.Allows, hfixed, true_and,
            SourceChoiceRestriction.weight, SourceChoiceRestriction.apply, one_mul]
          by_cases hallow : restriction.afterCommit.Allows (env.cons value) final
          · rw [if_pos hallow] at ih ⊢
            erw [ih]
            exact mul_left_comm _ _ _
          · rw [if_neg hallow] at ih ⊢
            erw [mul_left_comm, ← ih, mul_zero]
      | some fixed =>
          rw [denoteSource_prob_commit, denoteSource_prob_commit]
          simp only [SourceChoiceRestriction.Allows, hfixed,
            SourceChoiceRestriction.weight, SourceChoiceRestriction.apply,
            FinDist.map_pure]
          dsimp only [value] at ih
          by_cases heq : (sourceInitialProjection tail final).get .here = fixed.1
          · erw [heq, FinDist.prob_pure_self, one_mul]
            simp only [heq] at ih
            simp only [true_and]
            by_cases hallow : restriction.afterCommit.Allows (env.cons fixed.1) final
            · rw [if_pos hallow] at ih ⊢
              erw [ih]
              exact (mul_assoc _ _ _).symm
            · rw [if_neg hallow] at ih ⊢
              erw [mul_assoc, ← ih, mul_zero]
          · rw [if_neg (fun h => heq h.1),
              FinDist.prob_eq_zero_iff.mpr (fun h => heq (FinDist.mem_support_pure.mp h)),
              zero_mul, mul_zero]
  | _, .reveal _ _ _ _ tail, profile, restriction, env, final => by
      exact denoteSource_restriction_density tail profile.afterReveal
        restriction.afterReveal _ final

/-- Summing all unconstrained source choices uses the normalized restricted
source execution. No independence assumption is made about those choices. -/
theorem denoteSource_restriction_probability {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (profile : SourceBehavioralProfile prog) (restriction : SourceChoiceRestriction prog)
    (env : VEnv L Γ) :
    (denoteSource prog profile env).probOf {final | restriction.Allows env final} =
      (denoteSource prog (restriction.apply profile) env).expect
        (restriction.weight profile env) := by
  classical
  exact FinDist.probOf_eq_expect_of_weighting _ _ _ _
    (denoteSource_restriction_density prog profile restriction env)

/-- If the forced-choice likelihood is constant on restricted source runs,
that constant is exactly the event probability, including when it is zero. -/
theorem denoteSource_restriction_probability_of_constant {Γ : VCtx P L}
    (prog : VegasCore P L Γ) (profile : SourceBehavioralProfile prog)
    (restriction : SourceChoiceRestriction prog) (env : VEnv L Γ) (mass : ℝ)
    (hconstant : ∀ final ∈ (denoteSource prog (restriction.apply profile) env).support,
      restriction.weight profile env final = mass) :
    (denoteSource prog profile env).probOf {final | restriction.Allows env final} = mass := by
  rw [denoteSource_restriction_probability]
  exact (FinDist.expect_congr hconstant).trans (FinDist.expect_const _ mass)

end Vegas

/-- info: 'Vegas.denoteSource_restriction_support' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.denoteSource_restriction_support

/-- info: 'Vegas.denoteSource_restriction_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.denoteSource_restriction_probability

/-- info: 'Vegas.denoteSource_restriction_probability_of_constant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.denoteSource_restriction_probability_of_constant
