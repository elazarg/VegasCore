/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.LogRateCertificate
import GameTheoryExtensions.Analysis.Protocol.PowerCertificate

/-! # Completeness of power certificates for finite games

Actual common Bayes consistency supplies one shared integral log certificate.
Exponentiating its intercept and taking its nonnegative integer direction
produces positive coefficients and natural orders for the SAME complete
assessment, with every positive and zero belief history checked.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)

/-- In a game with finitely many global behavioral coordinates and legal
histories, consistency produces a power certificate for the exact assessment. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.exists_power_certificate
    [∀ who, Finite (M.InfoState who)] [∀ who info, Finite (M.Choice who info)]
    [Finite E.History] {assessment : M.BehavioralAssessment}
    {antichain : M.DecisionInformationAntichain}
    (consistent : assessment.IsSequentiallyConsistent antichain) :
    ∃ (coefficient : ∀ who info, M.Choice who info → ℝ)
      (order : ∀ who info, M.Choice who info → Nat)
      (reference : ∀ who (site : M.InformationSite who), M.InformationHistory who site.1),
      (∀ who info choice, 0 < coefficient who info choice) ∧
      (∀ who info choice,
        (if order who info choice = 0 then coefficient who info choice else 0) =
          (assessment.strategy who info choice).toReal) ∧
      (∀ who (site : M.InformationSite who) (history : M.InformationHistory who site.1),
        M.powerHistoryOrder order (reference who site).1.trace ≤
          M.powerHistoryOrder order history.1.trace) ∧
      (∀ who (site : M.InformationSite who) (history : M.InformationHistory who site.1),
        M.powerHistoryOrder order history.1.trace =
            M.powerHistoryOrder order (reference who site).1.trace ↔
          (assessment.belief who site history).toReal ≠ 0) ∧
      (∀ who (site : M.InformationSite who) (history : M.InformationHistory who site.1),
        (assessment.belief who site history).toReal ≠ 0 →
        M.powerHistoryCoefficient coefficient history.1.trace /
            M.powerHistoryCoefficient coefficient (reference who site).1.trace =
          (assessment.belief who site history).toReal /
            (assessment.belief who site (reference who site)).toReal) := by
  classical
  let : ∀ who, Fintype (M.InfoState who) := fun who => Fintype.ofFinite _
  let : ∀ who info, Fintype (M.Choice who info) := fun who info => Fintype.ofFinite _
  let reference := fun who (site : M.InformationSite who) =>
    (assessment.belief who site).support_nonempty.choose
  have referenceNonzero (who : ι) (site : M.InformationSite who) :
      (assessment.belief who site (reference who site)).toReal ≠ 0 :=
    (ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp
      (assessment.belief who site).support_nonempty.choose_spec) (PMF.apply_ne_top _ _)).ne'
  obtain ⟨intercept, integer, positiveActions, zeroActions, positiveHistories, zeroHistories⟩ :=
    consistent.exists_integral_log_certificate M reference referenceNonzero
  have integerNonnegative (coordinate : M.BehavioralCoordinate) : 0 ≤ integer coordinate := by
    by_cases zero : (assessment.strategy coordinate.1 coordinate.2.1 coordinate.2.2).toReal = 0
    · exact (zeroActions coordinate zero).le
    · rw [(positiveActions coordinate zero).2]
  let coefficient := fun who info (choice : M.Choice who info) =>
    Real.exp (-intercept ⟨who, info, choice⟩)
  let order := fun who info (choice : M.Choice who info) =>
    (integer ⟨who, info, choice⟩).toNat
  have coefficientPositive (who : ι) (info : M.InfoState who) (choice : M.Choice who info) :
      0 < coefficient who info choice := Real.exp_pos _
  have orderCast (coordinate : M.BehavioralCoordinate) :
      (order coordinate.1 coordinate.2.1 coordinate.2.2 : ℚ) = (integer coordinate : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (integerNonnegative coordinate)
  have orderDifference (who : ι) (site : M.InformationSite who)
      (history : M.InformationHistory who site.1) :
      (∑ coordinate, ((M.historyActionCount history.1.trace coordinate : ℚ) -
          (M.historyActionCount (reference who site).1.trace coordinate : ℚ)) *
            (integer coordinate : ℚ)) =
        (M.powerHistoryOrder order history.1.trace : ℚ) -
          (M.powerHistoryOrder order (reference who site).1.trace : ℚ) := by
    rw [M.powerHistoryOrder_cast_eq_sum, M.powerHistoryOrder_cast_eq_sum]
    simp only [orderCast, sub_mul, Finset.sum_sub_distrib]
  have equalOrder (who : ι) (site : M.InformationSite who)
      (history : M.InformationHistory who site.1)
      (nonzero : (assessment.belief who site history).toReal ≠ 0) :
      M.powerHistoryOrder order history.1.trace =
        M.powerHistoryOrder order (reference who site).1.trace := by
    have equation := (positiveHistories who site history nonzero).2
    rw [orderDifference] at equation
    exact_mod_cast sub_eq_zero.mp equation
  have higherOrder (who : ι) (site : M.InformationSite who)
      (history : M.InformationHistory who site.1)
      (zero : (assessment.belief who site history).toReal = 0) :
      M.powerHistoryOrder order (reference who site).1.trace <
        M.powerHistoryOrder order history.1.trace := by
    have strict := zeroHistories who site history zero
    rw [orderDifference] at strict
    exact_mod_cast sub_pos.mp strict
  have coefficientLog (history : E.History) :
      Real.log (M.powerHistoryCoefficient coefficient history.trace) =
        historyNatureLog history.trace - ∑ coordinate,
          (M.historyActionCount history.trace coordinate : ℝ) * intercept coordinate := by
    rw [M.powerHistoryCoefficient_log_eq coefficient coefficientPositive]
    simp only [coefficient, Real.log_exp, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  refine ⟨coefficient, order, reference, coefficientPositive, ?_, ?_, ?_, ?_⟩
  · intro who info choice
    by_cases zero : (assessment.strategy who info choice).toReal = 0
    · have strict := zeroActions ⟨who, info, choice⟩ zero
      have positive : 0 < order who info choice := by dsimp only [order]; omega
      rw [ite_eq_right positive.ne', zero]
    · obtain ⟨value, exponent⟩ := positiveActions ⟨who, info, choice⟩ zero
      have realPositive : 0 < (assessment.strategy who info choice).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm zero)
      simp only [order, exponent, Int.toNat_zero, ite_true, coefficient, value, neg_neg]
      exact Real.exp_log realPositive
  · intro who site history
    by_cases zero : (assessment.belief who site history).toReal = 0
    · exact (higherOrder who site history zero).le
    · rw [equalOrder who site history zero]
  · intro who site history
    constructor
    · intro same zero
      have strict := higherOrder who site history zero
      rw [same] at strict
      exact (lt_irrefl _) strict
    · exact equalOrder who site history
  · intro who site history nonzero
    have historyPositive := M.powerHistoryCoefficient_pos coefficient coefficientPositive
      history.1.trace
    have referencePositive := M.powerHistoryCoefficient_pos coefficient coefficientPositive
      (reference who site).1.trace
    have beliefPositive : 0 < (assessment.belief who site history).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm nonzero)
    have referenceBeliefPositive : 0 < (assessment.belief who site (reference who site)).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm (referenceNonzero who site))
    have logs :
        Real.log (M.powerHistoryCoefficient coefficient history.1.trace /
          M.powerHistoryCoefficient coefficient (reference who site).1.trace) =
        Real.log ((assessment.belief who site history).toReal /
          (assessment.belief who site (reference who site)).toReal) := by
      rw [Real.log_div historyPositive.ne' referencePositive.ne', coefficientLog, coefficientLog]
      have equation := (positiveHistories who site history nonzero).1
      simp only [sub_mul, Finset.sum_sub_distrib] at equation
      linarith
    calc
      _ = Real.exp (Real.log (M.powerHistoryCoefficient coefficient history.1.trace /
          M.powerHistoryCoefficient coefficient (reference who site).1.trace)) :=
        (Real.exp_log (div_pos historyPositive referencePositive)).symm
      _ = _ := congrArg Real.exp logs
      _ = _ := Real.exp_log (div_pos beliefPositive referenceBeliefPositive)

end GameTheory.Protocol.InformationModel
