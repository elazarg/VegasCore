/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheory.Analysis.Protocol.BeliefTransport
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Finite and divergent log ratios from actual consistent Bayes play

Bayes normalization cancels inside one genuine information fiber. The actual
common consistency sequence therefore supplies finite log-ratio limits on
positive target histories and divergent negative logs on zero target histories.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)

/-- The actual Bayes odds in one information fiber are its actual reach odds. -/
theorem bayes_reach_ratio {assessment : M.BehavioralAssessment}
    (antichain : M.DecisionInformationAntichain) (mixed : assessment.IsFullyMixed)
    (bayes : BehavioralAssessment.IsBayesConsistent M assessment antichain)
    (who : ι) (site : M.InformationSite who)
    (history reference : M.InformationHistory who site.1) :
    (assessment.belief who site history).toReal /
        (assessment.belief who site reference).toReal =
      (M.historyReachWeight assessment.strategy history.1).toReal /
        (M.historyReachWeight assessment.strategy reference.1).toReal := by
  have positive := M.informationMass_pos_of_fullSupport assessment.strategy mixed who site
  have finite := ne_top_of_le_ne_top ENNReal.one_ne_top
    (M.informationMass_le_one assessment.strategy who site (antichain who site))
  rw [bayes who site positive history, bayes who site positive reference,
    ENNReal.toReal_div, ENNReal.toReal_div]
  exact div_div_div_cancel_right₀ (ENNReal.toReal_pos positive.ne' finite).ne' _ _

/-- Positive target belief ratios have their actual finite logarithmic limits. -/
theorem reach_log_ratio_tendsto {sequence : Nat → M.BehavioralAssessment}
    {assessment : M.BehavioralAssessment} (antichain : M.DecisionInformationAntichain)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : ι) (site : M.InformationSite who)
    (history reference : M.InformationHistory who site.1)
    (historyNonzero : (assessment.belief who site history).toReal ≠ 0)
    (referenceNonzero : (assessment.belief who site reference).toReal ≠ 0) :
    Tendsto (fun n => Real.log
      ((M.historyReachWeight (sequence n).strategy history.1).toReal /
        (M.historyReachWeight (sequence n).strategy reference.1).toReal)) atTop
      (nhds (Real.log ((assessment.belief who site history).toReal /
        (assessment.belief who site reference).toReal))) := by
  have ratio := (converges.belief who site |>.toReal history).div
    (converges.belief who site |>.toReal reference) referenceNonzero
  have limit := (Real.continuousAt_log (div_ne_zero historyNonzero referenceNonzero)).tendsto.comp
    ratio
  apply limit.congr'
  filter_upwards [] with n
  exact congrArg Real.log (M.bayes_reach_ratio antichain (mixed n) (bayes n)
    who site history reference)

/-- A zero target history against a positive reference forces divergent
negative log odds along the actual fully mixed Bayes sequence. -/
theorem reach_neg_log_ratio_tendsto {sequence : Nat → M.BehavioralAssessment}
    {assessment : M.BehavioralAssessment} (antichain : M.DecisionInformationAntichain)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (who : ι) (site : M.InformationSite who)
    (history reference : M.InformationHistory who site.1)
    (historyZero : (assessment.belief who site history).toReal = 0)
    (referenceNonzero : (assessment.belief who site reference).toReal ≠ 0) :
    Tendsto (fun n => -Real.log
      ((M.historyReachWeight (sequence n).strategy history.1).toReal /
        (M.historyReachWeight (sequence n).strategy reference.1).toReal)) atTop atTop := by
  have ratio := (converges.belief who site |>.toReal history).div
    (converges.belief who site |>.toReal reference) referenceNonzero
  rw [historyZero, zero_div] at ratio
  have reachRatio : Tendsto (fun n =>
      (M.historyReachWeight (sequence n).strategy history.1).toReal /
        (M.historyReachWeight (sequence n).strategy reference.1).toReal) atTop (nhds 0) := by
    apply ratio.congr'
    filter_upwards [] with n
    exact M.bayes_reach_ratio antichain (mixed n) (bayes n) who site history reference
  have positive (n : Nat) (member : M.InformationHistory who site.1) :
      0 < (M.historyReachWeight (sequence n).strategy member.1).toReal :=
    ENNReal.toReal_pos
      (M.historyReachWeight_pos_of_fullSupport (sequence n).strategy (mixed n) member.1).ne'
      (PMF.apply_ne_top _ _)
  have within := tendsto_nhdsWithin_iff.mpr ⟨reachRatio,
    Eventually.of_forall fun n => div_pos (positive n history) (positive n reference)⟩
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp within)

end GameTheory.Protocol.InformationModel
