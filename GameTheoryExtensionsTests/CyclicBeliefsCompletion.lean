/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensionsTests.CyclicBeliefs
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # A common equal-rate completion preserves the pure-main profile

Positive common trembles toward the uniform profile make all rare sender
choices equiprobable. Finite compactness selects one common Bayes subsequence;
its limit keeps the entire main profile and the equal pair-belief rates.
-/

noncomputable section

namespace GameTheoryExtensionsTests.CyclicBeliefs

open GameTheory GameTheory.Protocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability Filter

private local instance : Finite arena.History :=
  (model.bayesAssessment_isFullyMixed uniformStrategy uniform_full antichain).finite_history
    bounded (fun _ _ => Set.toFinite _) (fun _ => Set.toFinite _)

def trembleWeight (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)

theorem trembleWeight_pos (n : Nat) : 0 < trembleWeight n := by
  unfold trembleWeight
  positivity

theorem trembleWeight_le_one (n : Nat) : trembleWeight n ≤ 1 := by
  apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem trembleWeight_vanishes : Tendsto trembleWeight atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def trembled (n : Nat) : model.BehavioralAssessment :=
  uniformAssessment.perturb mainStrategy (trembleWeight n) (trembleWeight_pos n).le
    (trembleWeight_le_one n)

theorem trembled_mixed (n : Nat) : (trembled n).IsFullyMixed :=
  uniformAssessment.perturb_fullyMixed
    (model.bayesAssessment_isFullyMixed uniformStrategy uniform_full antichain) mainStrategy
    (trembleWeight n) (trembleWeight_pos n).le (trembleWeight_le_one n) (trembleWeight_pos n)

abbrev equalRateSequence (n : Nat) : model.BehavioralAssessment :=
  model.bayesAssessment (trembled n).strategy (trembled_mixed n) antichain

theorem trembled_choose_shared (n : Nat) (who : Bool) :
    (trembled n).strategy who .choose = (trembled n).strategy false .choose := by
  cases who <;> rfl

theorem trembled_pair_shared (n : Nat) (who : Bool) (excluded : Fin 3) :
    (trembled n).strategy who (.pair excluded) = (trembled n).strategy false .choose := by
  cases who <;> rfl

theorem trembled_idle (n : Nat) (who : Bool) :
    (trembled n).strategy who .idle = PMF.pure ⟨none, rfl⟩ := by
  let : Subsingleton (model.Choice who .idle) :=
    ⟨fun first second => Subtype.ext (first.2.trans second.2.symm)⟩
  exact eq_pure_of_subsingleton _ _

theorem trembled_rare_equal (n : Nat) (first second : Fin 3) :
    (trembled n).strategy false .choose (rootChoice first.succ) =
      (trembled n).strategy false .choose (rootChoice second.succ) := by
  change mix (trembleWeight n) (trembleWeight_pos n).le (trembleWeight_le_one n)
      (uniformStrategy false .choose) (mainStrategy false .choose) (rootChoice first.succ) =
    mix (trembleWeight n) (trembleWeight_pos n).le (trembleWeight_le_one n)
      (uniformStrategy false .choose) (mainStrategy false .choose) (rootChoice second.succ)
  simp only [mix_apply, main_rare_zero, uniformStrategy, PMF.uniformOfFintype_apply]

theorem equalRateSequence_pair (n : Nat) (excluded : Fin 3) :
    ((equalRateSequence n).belief true (pairSite excluded) (favoredMember excluded)).toReal =
      ((equalRateSequence n).belief true (pairSite excluded) (opposedMember excluded)).toReal := by
  have bayes := model.bayesAssessment_isBayesConsistent (trembled n).strategy
    (trembled_mixed n) antichain
  have positive := model.informationMass_pos_of_fullSupport (trembled n).strategy
    (trembled_mixed n) true (pairSite excluded)
  have left := congrArg ENNReal.toReal (bayes true (pairSite excluded) positive
    (favoredMember excluded))
  have right := congrArg ENNReal.toReal (bayes true (pairSite excluded) positive
    (opposedMember excluded))
  rw [ENNReal.toReal_div] at left right
  calc
    _ = (model.historyReachWeight (trembled n).strategy (favoredMember excluded).1).toReal /
        (model.informationMass (trembled n).strategy true (pairSite excluded)).toReal := left
    _ = (model.historyReachWeight (trembled n).strategy (opposedMember excluded).1).toReal /
        (model.informationMass (trembled n).strategy true (pairSite excluded)).toReal := by
      simp only [favoredMember, opposedMember, pairMember, pair_weight]
      rw [trembled_rare_equal n (excluded + 1) (excluded + 2)]
    _ = _ := right.symm

def rootChoiceEquiv : Fin 4 ≃ model.Choice false .choose where
  toFun := rootChoice
  invFun choice := Classical.choose choice.2
  left_inv action := by
    have same := Classical.choose_spec (rootChoice action).2
    exact Option.some.inj same.symm
  right_inv choice := Subtype.ext (Classical.choose_spec choice.2).symm

theorem root_choice_card : Fintype.card (model.Choice false .choose) = 4 := by
  simpa using (Fintype.card_congr rootChoiceEquiv).symm

theorem uniform_root (action : Fin 4) :
    (uniformStrategy false .choose (rootChoice action)).toReal = 1 / 4 := by
  change ((PMF.uniformOfFintype (model.Choice false .choose)) (rootChoice action)).toReal = _
  rw [PMF.uniformOfFintype_apply, root_choice_card]
  norm_num

theorem trembled_rare_power (n : Nat) (actual : Fin 3) :
    ((trembled n).strategy false .choose (rootChoice actual.succ)).toReal =
      trembleWeight n / 4 := by
  change (mix _ (trembleWeight_pos n).le (trembleWeight_le_one n)
    (uniformStrategy false .choose) (mainStrategy false .choose)
      (rootChoice actual.succ)).toReal = _
  rw [mix_apply_toReal, main_rare_zero, uniform_root, ENNReal.toReal_zero,
    mul_zero, add_zero]
  ring

theorem trembled_main_power (n : Nat) :
    ((trembled n).strategy false .choose (rootChoice 0)).toReal = 1 - 3 * trembleWeight n / 4 := by
  change (mix _ (trembleWeight_pos n).le (trembleWeight_le_one n)
    (uniformStrategy false .choose) (mainStrategy false .choose) (rootChoice 0)).toReal = _
  rw [mix_apply_toReal]
  change _ + _ * ((PMF.pure (rootChoice 0)) (rootChoice 0)).toReal = _
  rw [PMF.pure_apply_self, ENNReal.toReal_one]
  rw [uniform_root]
  ring

/-- Normalized powers with coefficients one and exponents zero or one. -/
def powerBase (n : Nat) : ℝ := trembleWeight n / (4 - 3 * trembleWeight n)

theorem powerBase_denominator_pos (n : Nat) : 0 < 4 - 3 * trembleWeight n := by
  have := trembleWeight_le_one n
  linarith

theorem powerBase_pos (n : Nat) : 0 < powerBase n :=
  div_pos (trembleWeight_pos n) (powerBase_denominator_pos n)

theorem powerBase_vanishes : Tendsto powerBase atTop (nhds 0) := by
  have denominator : Tendsto (fun n => 4 - 3 * trembleWeight n) atTop
      (nhds (4 - 3 * (0 : ℝ))) :=
    tendsto_const_nhds.sub (trembleWeight_vanishes.const_mul 3)
  change Tendsto (fun n => trembleWeight n / (4 - 3 * trembleWeight n)) atTop (nhds 0)
  simpa only [Pi.div_def, mul_zero, sub_zero, zero_div] using
    trembleWeight_vanishes.div denominator (by norm_num)

theorem trembled_normalized_powers (n : Nat) :
    ((trembled n).strategy false .choose (rootChoice 0)).toReal = 1 / (1 + 3 * powerBase n) ∧
      ∀ actual : Fin 3,
        ((trembled n).strategy false .choose (rootChoice actual.succ)).toReal =
          powerBase n / (1 + 3 * powerBase n) := by
  have denominator := (powerBase_denominator_pos n).ne'
  have total : 1 + 3 * powerBase n = 4 / (4 - 3 * trembleWeight n) := by
    unfold powerBase
    field_simp [denominator]
    ring
  constructor
  · rw [trembled_main_power, total, one_div_div]
    ring
  · intro actual
    rw [trembled_rare_power, total]
    unfold powerBase
    exact (div_div_div_cancel_right₀ denominator (trembleWeight n) 4).symm

/-- A preserving equilibrium exists for the exact same complete prescribed profile.
Only the analyst's impossible cyclic beliefs must change. -/
theorem exists_main_sequential_equilibrium :
    ∃ assessment : model.BehavioralAssessment,
      assessment.strategy = mainStrategy ∧
      assessment.IsSequentialEquilibrium antichain bounded.wellFoundedHistories
        (fun _ _ => 0) ∧
      ∀ excluded,
        (assessment.belief true (pairSite excluded) (favoredMember excluded)).toReal =
          (assessment.belief true (pairSite excluded) (opposedMember excluded)).toReal := by
  obtain ⟨assessment, prescribed, index, increasing, converges, consistent⟩ :=
    BehavioralAssessment.exists_consistent_completion_subsequence antichain mainStrategy
      equalRateSequence
      (fun n => model.bayesAssessment_isFullyMixed _ (trembled_mixed n) antichain)
      (fun n => model.bayesAssessment_isBayesConsistent _ (trembled_mixed n) antichain)
      (fun _ _ => uniformlyTight_of_finite _)
      (fun who site => uniformAssessment.perturb_strategy_converges mainStrategy trembleWeight
        (fun n => (trembleWeight_pos n).le) trembleWeight_le_one trembleWeight_vanishes who site.1)
  refine ⟨assessment, prescribed, ⟨assessment.isSequentiallyRational_zero _, consistent⟩,
    fun excluded => ?_⟩
  have left := (converges.belief true (pairSite excluded)).toReal (favoredMember excluded)
  have right := (converges.belief true (pairSite excluded)).toReal (opposedMember excluded)
  apply tendsto_nhds_unique left
  apply right.congr'
  filter_upwards [] with n
  exact (equalRateSequence_pair (index n) excluded).symm

end GameTheoryExtensionsTests.CyclicBeliefs
