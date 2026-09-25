/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.AmbientEnforcementEquilibrium

/-! # Sharp collateral thresholds for preserving the guessing-game outcomes

After disclosure Bob must guess correctly. Alice can therefore secure `1 - D`
at either private bit by disclosing. With nonnegative collateral, her utility
is bounded by ordinary correctness. Matching a source joint bit/guess law
consequently requires `1 - D` to be no larger than its correctness probability
at either bit. The retained law forgets whether disclosure occurred.

The bound covers every sequentially rational target assessment; no restriction
to the proposed compiler, prescribed beliefs, or silent strategies is imposed.
Combined with the silent compiler, it exactly characterizes implementation of
each source law. Fair guessing requires a deposit of at least one half;
implementing all source equilibrium laws requires a deposit of at least one.
-/

noncomputable section

namespace GameTheoryExtensionsTests.AmbientEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

theorem rational_disclosed_reward_lower (deposit : ℝ)
    (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => payoff deposit history.state who) 3) (bit : Bool) :
    1 ≤ (resultLaw assessment.strategy bit true).expect (payoff deposit · true) := by
  have best := rational true (bobDisclosedSite bit) (choose true true bit) (Set.mem_univ _)
  rw [disclosed_context assessment bit (payoff deposit · true) (choose true true bit),
    disclosed_context assessment bit (payoff deposit · true) (assessment.strategy true),
    Profile.update_eq_self] at best
  rw [value_bob (ambient := true) _ _ _ (payoff deposit · true),
    value_bob (ambient := true) _ _ _ (payoff deposit · true)] at best
  simp only [Bool.true_and] at best
  have correct : (resultLaw
      (Profile.update (sig := (model true).behavioralSignature) assessment.strategy true
        (choose true true bit)) bit true).expect (payoff deposit · true) = 1 := by
    simp [resultLaw, choiceLaw, Profile.update, choose, decisionInfo, payoff]
  rwa [correct] at best

theorem disclosed_payoff_difference (deposit : ℝ)
    (profile : Profile (model true).behavioralSignature) (bit : Bool) :
    (resultLaw profile bit true).expect (payoff deposit · false) =
      (resultLaw profile bit true).expect (payoff deposit · true) - deposit := by
  simp only [resultLaw, FinDist.expect_map, payoff, Bool.not_false, Bool.not_true,
    Bool.true_and, Bool.false_and, ite_true, Bool.false_eq_true, ite_false, sub_zero]
  rw [FinDist.expect_sub, FinDist.expect_const]

theorem rational_alice_reward_lower (deposit : ℝ)
    (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => payoff deposit history.state who) 3) (bit : Bool) :
    1 - deposit ≤
      ((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
        (aliceHistory true bit)).expect (fun history => payoff deposit history.state false) := by
  have best := rational false (aliceSite bit) (choose true false true) (Set.mem_univ _)
  rw [alice_context assessment bit (payoff deposit · false) (choose true false true),
    alice_context assessment bit (payoff deposit · false) (assessment.strategy false),
    Profile.update_eq_self,
    value_alice (ambient := true) _ bit (payoff deposit · false)] at best
  have discloses : choiceLaw
      (Profile.update (sig := (model true).behavioralSignature) assessment.strategy false
        (choose true false true)) false (some (some bit)) = FinDist.pure true := by
    simp [choiceLaw, Profile.update, choose, decisionInfo]
  rw [discloses, FinDist.expect_pure] at best
  have unchanged : resultLaw
      (Profile.update (sig := (model true).behavioralSignature) assessment.strategy false
        (choose true false true)) bit true = resultLaw assessment.strategy bit true := by
    simp [resultLaw, choiceLaw, Profile.update]
  simp only [Bool.true_and] at best
  rw [unchanged, disclosed_payoff_difference] at best
  have correct := rational_disclosed_reward_lower deposit assessment rational bit
  linarith

theorem alice_payoff_le_correctness {deposit : ℝ} (nonnegative : 0 ≤ deposit) (state : State) :
    payoff deposit state false ≤ payoff deposit state true := by
  cases state with
  | initial => simp [payoff]
  | alice bit => simp [payoff]
  | bob bit disclosed => simp [payoff]
  | done bit disclosed guess => cases disclosed <;> simp [payoff, nonnegative]

theorem rational_correctness_lower {deposit : ℝ} (nonnegative : 0 ≤ deposit)
    (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => payoff deposit history.state who) 3) (bit : Bool) :
    1 - deposit ≤
      ((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
        (aliceHistory true bit)).expect (fun history => payoff deposit history.state true) := by
  exact (rational_alice_reward_lower deposit assessment rational bit).trans
    (FinDist.expect_mono fun history _ => alice_payoff_le_correctness nonnegative history.state)

def retainedBitScore (bit : Bool) : Option (Bool × Bool) → ℝ
  | some (actual, guess) => if actual = bit then (if guess = bit then 1 else 0) else 0
  | none => 0

/-- Weighting the retained joint law by one bit recovers that type's ordinary
correctness, multiplied by its initial probability one half. -/
theorem initialized_bit_score (deposit : ℝ)
    (profile : Profile (model true).behavioralSignature) (bit : Bool) :
    ((((model true).runSingleMoverBehavioralFrom (single true) profile 3
      (arena true).initHistory).map History.state).map retained).expect (retainedBitScore bit) =
      (1 / 2) * ((model true).runSingleMoverBehavioralFrom (single true) profile 3
        (aliceHistory true bit)).expect (fun history => payoff deposit history.state true) := by
  rw [run_initial, FinDist.expect_map, FinDist.expect_bind,
    value_alice (ambient := true) _ bit (payoff deposit · true)]
  simp only [FinDist.expect_bind, resultLaw, FinDist.expect_map]
  rw [FinDist.expect_eq_sum, Fintype.sum_bool]
  cases bit <;>
    simp [FinDist.prob_uniformOfFintype, Fintype.card_bool, retainedBitScore, retained, payoff]

theorem source_bit_score (guesses : FinDist Bool) (bit : Bool) :
    ((FinDist.product (FinDist.uniformOfFintype (α := Bool)) guesses).map some).expect
        (retainedBitScore bit) =
      (1 / 2) * guesses.expect (fun guess => if guess = bit then (1 : ℝ) else 0) := by
  rw [FinDist.expect_map, FinDist.expect_product, FinDist.expect_eq_sum, Fintype.sum_bool]
  cases bit <;>
    simp [FinDist.prob_uniformOfFintype, Fintype.card_bool, retainedBitScore]

/-- Necessary collateral for matching any source guessing law, even when the
target strategies and beliefs are chosen freely and disclosure is not retained. -/
theorem retained_law_requires_deterrence {deposit : ℝ} (nonnegative : 0 ≤ deposit)
    (guesses : FinDist Bool) (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => payoff deposit history.state who) 3)
    (matching :
      (((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
        (arena true).initHistory).map History.state).map retained =
      (FinDist.product (FinDist.uniformOfFintype (α := Bool)) guesses).map some) :
    ∀ bit, 1 - deposit ≤ guesses.expect (fun guess => if guess = bit then (1 : ℝ) else 0) := by
  intro bit
  have same := congrArg (fun law => law.expect (retainedBitScore bit)) matching
  rw [initialized_bit_score deposit, source_bit_score] at same
  have lower := rational_correctness_lower nonnegative assessment rational bit
  linarith

/-- Exact existence criterion for a target SE matching the source joint law.
The necessity permits arbitrary target strategies and beliefs; sufficiency
uses the fixed playerwise compiler's silent extension. -/
theorem retained_law_implementable_iff {deposit : ℝ} (nonnegative : 0 ≤ deposit)
    (guesses : FinDist Bool) :
    (∃ assessment : (model true).BehavioralAssessment,
      isEquilibrium deposit assessment ∧
        (((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
          (arena true).initHistory).map History.state).map retained =
        (FinDist.product (FinDist.uniformOfFintype (α := Bool)) guesses).map some) ↔
      ∀ bit, 1 - deposit ≤ guesses.expect (correct bit) := by
  constructor
  · rintro ⟨assessment, equilibrium, matching⟩
    exact retained_law_requires_deterrence nonnegative guesses assessment equilibrium.1 matching
  · intro deterrence
    refine ⟨targetAssessment (silentProfile guesses),
      target_sequential_equilibrium guesses deposit deterrence, ?_⟩
    change (((model true).runSingleMoverBehavioralFrom (single true) (silentProfile guesses) 3
      (arena true).initHistory).map History.state).map retained = _
    rw [target_initialized_law]
    simp [FinDist.product, FinDist.map_eq_bind]

theorem fair_law_implementable_iff {deposit : ℝ} (nonnegative : 0 ≤ deposit) :
    (∃ assessment : (model true).BehavioralAssessment,
      isEquilibrium deposit assessment ∧
        (((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
          (arena true).initHistory).map History.state).map retained =
        (FinDist.product (FinDist.uniformOfFintype (α := Bool))
          (FinDist.uniformOfFintype (α := Bool))).map some) ↔
      1 / 2 ≤ deposit := by
  rw [retained_law_implementable_iff nonnegative]
  constructor
  · intro deterrence
    have bound := deterrence false
    rw [fair_correct] at bound
    linarith
  · intro enforced bit
    rw [fair_correct]
    linarith

/-- A single deposit implements every source equilibrium law exactly when it
is at least one. Every source guess law is an SE by `source_sequential_equilibrium`. -/
theorem all_source_laws_implementable_iff {deposit : ℝ} (nonnegative : 0 ≤ deposit) :
    (∀ guesses : FinDist Bool, ∃ assessment : (model true).BehavioralAssessment,
      isEquilibrium deposit assessment ∧
        (((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
          (arena true).initHistory).map History.state).map retained =
        (FinDist.product (FinDist.uniformOfFintype (α := Bool)) guesses).map some) ↔
      1 ≤ deposit := by
  constructor
  · intro implements
    have deterrence := (retained_law_implementable_iff nonnegative (FinDist.pure false)).mp
      (implements (FinDist.pure false))
    have bound := deterrence true
    norm_num [correct] at bound
    linarith
  · intro enforced guesses
    apply (retained_law_implementable_iff nonnegative guesses).mpr
    intro bit
    have nonnegativeReward := correct_nonnegative guesses bit
    linarith

/-- Without a penalty, restoring optional disclosure destroys even the fair
source equilibrium's joint bit/guess law, regardless of target strategy choice. -/
theorem no_unpenalized_fair_law :
    ¬ ∃ assessment : (model true).BehavioralAssessment,
      isEquilibrium 0 assessment ∧
        (((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
          (arena true).initHistory).map History.state).map retained =
        (FinDist.product (FinDist.uniformOfFintype (α := Bool))
          (FinDist.uniformOfFintype (α := Bool))).map some := by
  rw [fair_law_implementable_iff (by norm_num)]
  norm_num

end GameTheoryExtensionsTests.AmbientEnforcement
