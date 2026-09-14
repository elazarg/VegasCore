/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.SourceRestriction
import VegasTests.SourceGraph

/-! # Source cylinder probabilities with dependent continuation choices -/

noncomputable section

namespace VegasTests.SourceRestriction

open Vegas GameTheory.Math.Probability
open PendingStages SourceGraph

def firstChoice (value : Value) : SourceChoiceRestriction core := by
  intro who Δ name ty guard site visible
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  unfold core at site
  cases site with
  | here => exact some ⟨value, by cases value <;> rfl⟩
  | commit _ => exact none

/-- Forcing the first choice leaves the later observation-dependent copy
policy unchanged; both source reveals still execute normally. -/
theorem restricted_repeat_law (law : FinDist Value) (value : Value) :
    denoteSource core ((firstChoice value).apply (repeatPolicy law)) (VEnv.empty simpleExpr) =
      FinDist.pure (repeatedOutcome value) := by
  simp only [core, denoteSource, SourceChoiceRestriction.apply, firstChoice,
    VegasCore.commit.noConfusion, VegasCore.reveal.noConfusion, VegasCore.noConfusion, id_eq,
    SourceBehavioralProfile.afterCommit, SourceBehavioralProfile.afterReveal,
    repeatPolicy, FinDist.pure_bind]
  cases value <;> rfl

theorem repeat_weight (law : FinDist Value) (value : Value) :
    (firstChoice value).weight (repeatPolicy law) (VEnv.empty simpleExpr)
      (repeatedOutcome value) = law.prob value := by
  simp only [core, SourceChoiceRestriction.weight, firstChoice, repeatPolicy,
    VegasCore.commit.noConfusion, VegasCore.noConfusion, id_eq,
    SourceChoiceRestriction.afterCommit, SourceChoiceRestriction.afterReveal,
    FinDist.map_comp, Function.comp_def, mul_one]
  change (law.map id).prob value = law.prob value
  rw [FinDist.map_id]

/-- The cylinder sum is the first draw's mass, not a product of two independent
draws. No positivity premise is required. -/
theorem first_choice_cylinder (law : FinDist Value) (value : Value) :
    (denoteSource core (repeatPolicy law) (VEnv.empty simpleExpr)).probOf
      {final | (firstChoice value).Allows (VEnv.empty simpleExpr) final} = law.prob value := by
  apply denoteSource_restriction_probability_of_constant
  intro final hfinal
  rw [restricted_repeat_law, FinDist.mem_support_pure] at hfinal
  subst final
  exact repeat_weight law value

/-- The forced reference run exists even when its cylinder has zero mass in
the original source law. Such a reference is not a conditional distribution. -/
theorem zero_probability_cylinder :
    (denoteSource core (repeatPolicy (FinDist.pure (some true))) (VEnv.empty simpleExpr)).probOf
      {final | (firstChoice none).Allows (VEnv.empty simpleExpr) final} = 0 := by
  rw [first_choice_cylinder]
  exact FinDist.prob_eq_zero_iff.mpr (by simp only [FinDist.mem_support_pure,
    reduceCtorEq, not_false_eq_true])

def secondChoice (value : Value) : SourceChoiceRestriction core := by
  intro who Δ name ty guard site visible
  have hwho : who = 0 := Subsingleton.elim _ _
  subst who
  unfold core at site
  cases site with
  | here => exact none
  | commit site =>
      cases site with
      | reveal site =>
          cases site with
          | here => exact some ⟨value, by cases value <;> rfl⟩
          | commit site => cases site with | reveal site => cases site

def pairOutcome (first second : Value) : VEnv simpleExpr (sourceTerminalCtx core) :=
  (((VEnv.empty simpleExpr).cons first).cons first).cons second |>.cons second

theorem restricted_second_law (law : FinDist Value) (value : Value) :
    denoteSource core ((secondChoice value).apply (repeatPolicy law)) (VEnv.empty simpleExpr) =
      law.map (fun first => pairOutcome first value) := by
  simp only [core, denoteSource, SourceChoiceRestriction.apply, secondChoice,
    VegasCore.commit.noConfusion, VegasCore.reveal.noConfusion, VegasCore.noConfusion, id_eq,
    SourceBehavioralProfile.afterCommit, SourceBehavioralProfile.afterReveal,
    repeatPolicy, FinDist.bind_map, FinDist.pure_bind]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro first _
  cases first <;> cases value <;> rfl

/-- When only the second choice is forced, its original likelihood depends
on the first choice. It must remain inside the expectation. -/
theorem second_weight (law : FinDist Value) (first second : Value) :
    (secondChoice second).weight (repeatPolicy law) (VEnv.empty simpleExpr)
      (pairOutcome first second) = (FinDist.pure first).prob second := by
  simp only [core, SourceChoiceRestriction.weight, secondChoice, repeatPolicy,
    VegasCore.commit.noConfusion, VegasCore.reveal.noConfusion, VegasCore.noConfusion, id_eq,
    SourceChoiceRestriction.afterCommit, SourceChoiceRestriction.afterReveal,
    SourceBehavioralProfile.afterCommit, SourceBehavioralProfile.afterReveal,
    FinDist.map_pure, one_mul, mul_one]
  rfl

theorem second_choice_cylinder (law : FinDist Value) (value : Value) :
    (denoteSource core (repeatPolicy law) (VEnv.empty simpleExpr)).probOf
      {final | (secondChoice value).Allows (VEnv.empty simpleExpr) final} = law.prob value := by
  classical
  rw [denoteSource_restriction_probability, restricted_second_law, FinDist.expect_map]
  calc
    _ = law.expect (fun first => (FinDist.pure first).prob value) :=
      FinDist.expect_congr (fun first _ => second_weight law first value)
    _ = law.prob value := by
      simp only [FinDist.prob_pure_eq_ite]
      rw [FinDist.expect_ite_eq, mul_one]

end VegasTests.SourceRestriction
