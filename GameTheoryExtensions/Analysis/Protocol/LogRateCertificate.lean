/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.FullSupportApproximation
import GameTheoryExtensions.Analysis.Protocol.FiniteTraceCoordinates
import GameTheory.Protocol.FiniteInformation
import GameTheoryExtensions.Analysis.Protocol.BayesLogLimits
import GameTheoryExtensions.Math.AffineRay
import GameTheoryExtensions.Math.RationalStrictDirection

/-! # Integral log certificates extracted from actual finite-game consistency

Only coordinates drawn by actual histories enter the finite system. The common Bayes sequence
produces finite affine equations and divergent inequalities. A real affine ray
and rational-kernel integer approximation then give one common integral order
vector together with the exact real coefficient intercept. Coordinates outside
the finite cover are extended directly from the prescribed strategy.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)
  [∀ who info, Finite (M.Choice who info)]

/-- Actual consistency yields finite coefficient equations and a single integer
order vector, without assuming any log-rate limits as certificate inputs. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.exists_integral_log_certificate
    [Finite E.History] {assessment : M.BehavioralAssessment}
    {antichain : M.DecisionInformationAntichain}
    (consistent : assessment.IsSequentiallyConsistent antichain)
    (reference : ∀ who (site : M.InformationSite who), M.InformationHistory who site.1)
    (referenceNonzero : ∀ who site,
      (assessment.belief who site (reference who site)).toReal ≠ 0) :
    ∃ (intercept : M.BehavioralCoordinate → ℝ) (integer : M.BehavioralCoordinate → ℤ),
      (∀ coordinate, (assessment.strategy coordinate.1 coordinate.2.1 coordinate.2.2).toReal ≠ 0 →
        intercept coordinate =
            -Real.log ((assessment.strategy coordinate.1 coordinate.2.1 coordinate.2.2).toReal) ∧
          integer coordinate = 0) ∧
      (∀ coordinate, (assessment.strategy coordinate.1 coordinate.2.1 coordinate.2.2).toReal = 0 →
        0 < integer coordinate) ∧
      (∀ who (site : M.InformationSite who) (history : M.InformationHistory who site.1),
        (assessment.belief who site history).toReal ≠ 0 →
        (∑ coordinate : M.RealizedCoordinate,
          ((M.historyActionCount history.1.trace coordinate.1 : ℝ) -
            (M.historyActionCount (reference who site).1.trace coordinate.1 : ℝ)) *
              intercept coordinate.1) =
          historyNatureLog history.1.trace - historyNatureLog (reference who site).1.trace -
            Real.log ((assessment.belief who site history).toReal /
              (assessment.belief who site (reference who site)).toReal) ∧
        (∑ coordinate : M.RealizedCoordinate,
          ((M.historyActionCount history.1.trace coordinate.1 : ℚ) -
            (M.historyActionCount (reference who site).1.trace coordinate.1 : ℚ)) *
              (integer coordinate.1 : ℚ)) = 0) ∧
      (∀ who (site : M.InformationSite who) (history : M.InformationHistory who site.1),
        (assessment.belief who site history).toReal = 0 →
        0 < ∑ coordinate : M.RealizedCoordinate,
          ((M.historyActionCount history.1.trace coordinate.1 : ℚ) -
            (M.historyActionCount (reference who site).1.trace coordinate.1 : ℚ)) *
              (integer coordinate.1 : ℚ)) := by
  classical
  obtain ⟨sequence, full, bayes, strategyLimit, converges⟩ :=
    consistent.exists_everywhere_full M
  let Coordinate := M.RealizedCoordinate
  let BeliefIndex := Σ who, Σ site : M.InformationSite who, M.InformationHistory who site.1
  let atom : Coordinate → ℝ := fun coordinate =>
    (assessment.strategy coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2).toReal
  let belief : BeliefIndex → ℝ := fun index =>
    (assessment.belief index.1 index.2.1 index.2.2).toReal
  let Equation := Sum {coordinate : Coordinate // atom coordinate ≠ 0}
    {index : BeliefIndex // belief index ≠ 0}
  let Inequality := Sum {coordinate : Coordinate // atom coordinate = 0}
    {index : BeliefIndex // belief index = 0}
  let difference (index : BeliefIndex) (coordinate : Coordinate) : ℚ :=
    (M.historyActionCount index.2.2.1.trace coordinate.1 : ℚ) -
      (M.historyActionCount (reference index.1 index.2.1).1.trace coordinate.1 : ℚ)
  let equations : Matrix Equation Coordinate ℚ := fun row coordinate => match row with
    | .inl action => if coordinate = action.1 then 1 else 0
    | .inr history => difference history.1 coordinate
  let inequalities : Matrix Inequality Coordinate ℚ := fun row coordinate => match row with
    | .inl action => if coordinate = action.1 then 1 else 0
    | .inr history => difference history.1 coordinate
  let nature (index : BeliefIndex) := historyNatureLog index.2.2.1.trace -
    historyNatureLog (reference index.1 index.2.1).1.trace
  let limit : Equation → ℝ := fun row => match row with
    | .inl action => -Real.log (atom action.1)
    | .inr history => nature history.1 - Real.log (belief history.1 /
        (assessment.belief history.1.1 history.1.2.1
          (reference history.1.1 history.1.2.1)).toReal)
  let rate := fun n (coordinate : Coordinate) =>
    -Real.log (((sequence n).strategy coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2).toReal)
  have positive (n : Nat) (coordinate : Coordinate) :
      0 < ((sequence n).strategy coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp
      (full n coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2)) (PMF.apply_ne_top _ _)
  have actionLimit (coordinate : Coordinate) (nonzero : atom coordinate ≠ 0) :
      Tendsto (fun n => rate n coordinate) atTop (nhds (-Real.log (atom coordinate))) := by
    exact ((Real.continuousAt_log nonzero).tendsto.comp
      ((strategyLimit coordinate.1.1 coordinate.1.2.1).toReal coordinate.1.2.2)).neg
  have actionDiverges (coordinate : Coordinate) (zero : atom coordinate = 0) :
      Tendsto (fun n => rate n coordinate) atTop atTop := by
    have vanishes := (strategyLimit coordinate.1.1 coordinate.1.2.1).toReal coordinate.1.2.2
    change Tendsto _ atTop (nhds (atom coordinate)) at vanishes
    rw [zero] at vanishes
    have within := tendsto_nhdsWithin_iff.mpr ⟨vanishes,
      Eventually.of_forall fun n => positive n coordinate⟩
    exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp within)
  have rowValue (index : BeliefIndex) (n : Nat) :
      (∑ coordinate, ((difference index coordinate : ℚ) : ℝ) * rate n coordinate) =
        nature index - Real.log
          ((M.historyReachWeight (sequence n).strategy index.2.2.1).toReal /
            (M.historyReachWeight (sequence n).strategy
              (reference index.1 index.2.1).1).toReal) := by
    simpa only [difference, rate, nature, Rat.cast_sub, Rat.cast_natCast] using
      M.historyLogRate_difference_realized (sequence n).strategy (full n) index.2.2.1
        (reference index.1 index.2.1).1
  have singleReal (coordinate : Coordinate) (value : Coordinate → ℝ) :
      (∑ other, (((if other = coordinate then 1 else 0 : ℚ) : ℚ) : ℝ) * value other) =
        value coordinate := by
    rw [Finset.sum_eq_single coordinate]
    · simp
    · intro other _ different
      simp [different]
    · simp
  have singleRational (coordinate : Coordinate) (value : Coordinate → ℚ) :
      (∑ other, (if other = coordinate then 1 else 0 : ℚ) * value other) =
        value coordinate := by
    rw [Finset.sum_eq_single coordinate]
    · simp
    · intro other _ different
      simp [different]
    · simp
  have finiteLimit : Tendsto
      (fun n => (equations.map (Rat.castHom ℝ)).mulVec (rate n)) atTop (nhds limit) := by
    apply tendsto_pi_nhds.mpr
    intro row
    cases row with
    | inl action =>
      change Tendsto (fun n => ∑ coordinate,
        (((if coordinate = action.1 then 1 else 0 : ℚ) : ℚ) : ℝ) * rate n coordinate)
        atTop (nhds (-Real.log (atom action.1)))
      simp_rw [singleReal]
      exact actionLimit action.1 action.2
    | inr history =>
      have logLimit := M.reach_log_ratio_tendsto antichain
        (fun n who site => full n who site.1) bayes converges
        history.1.1 history.1.2.1 history.1.2.2 (reference history.1.1 history.1.2.1)
        history.2 (referenceNonzero _ _)
      have valueLimit := (tendsto_const_nhds (x := nature history.1)).sub logLimit
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.coe_castHom, equations,
        rowValue, limit, belief, Function.comp_apply] using valueLimit
  have infiniteLimit (row : Inequality) :
      Tendsto (fun n => (inequalities.map (Rat.castHom ℝ)).mulVec (rate n) row) atTop atTop := by
    cases row with
    | inl action =>
      change Tendsto (fun n => ∑ coordinate,
        (((if coordinate = action.1 then 1 else 0 : ℚ) : ℚ) : ℝ) * rate n coordinate)
        atTop atTop
      simp_rw [singleReal]
      exact actionDiverges action.1 action.2
    | inr history =>
      have logLimit := M.reach_neg_log_ratio_tendsto antichain
        (fun n who site => full n who site.1) bayes converges
        history.1.1 history.1.2.1 history.1.2.2 (reference history.1.1 history.1.2.1)
        history.2 (referenceNonzero _ _)
      have valueLimit := tendsto_atTop_add_const_left atTop (nature history.1) logLimit
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Rat.coe_castHom, inequalities,
        rowValue, sub_eq_add_neg] using valueLimit
  obtain ⟨intercept, direction, interceptEq, directionEq, directionStrict⟩ :=
    exists_affine_ray (equations.map (Rat.castHom ℝ)).mulVecLin
      (inequalities.map (Rat.castHom ℝ)).mulVecLin rate limit finiteLimit infiniteLimit
  obtain ⟨integer, integerEq, integerStrict⟩ :=
    exists_integer_strict_direction equations inequalities direction directionEq directionStrict
  let extendedIntercept (coordinate : M.BehavioralCoordinate) :=
    if present : coordinate ∈ M.realizedCoordinates then intercept ⟨coordinate, present⟩ else
      -Real.log ((assessment.strategy coordinate.1 coordinate.2.1 coordinate.2.2).toReal)
  let extendedInteger (coordinate : M.BehavioralCoordinate) :=
    if present : coordinate ∈ M.realizedCoordinates then integer ⟨coordinate, present⟩ else
      if (assessment.strategy coordinate.1 coordinate.2.1 coordinate.2.2).toReal = 0 then 1 else 0
  have interceptOn (coordinate : M.RealizedCoordinate) :
      extendedIntercept coordinate.1 = intercept coordinate := dite_eq_left coordinate.2
  have integerOn (coordinate : M.RealizedCoordinate) :
      extendedInteger coordinate.1 = integer coordinate := dite_eq_left coordinate.2
  refine ⟨extendedIntercept, extendedInteger, ?_, ?_, ?_, ?_⟩
  · intro coordinate nonzero
    by_cases present : coordinate ∈ M.realizedCoordinates
    · let localCoordinate : Coordinate := ⟨coordinate, present⟩
      have realEquation := congrFun interceptEq (Sum.inl ⟨localCoordinate, nonzero⟩)
      have integerEquation := congrFun integerEq (Sum.inl ⟨localCoordinate, nonzero⟩)
      constructor
      · change (∑ other, (((if other = localCoordinate then 1 else 0 : ℚ) : ℚ) : ℝ) *
          intercept other) = -Real.log (atom localCoordinate) at realEquation
        rw [singleReal] at realEquation
        simpa only [extendedIntercept, dite_eq_left present] using realEquation
      · change (∑ other, (if other = localCoordinate then 1 else 0 : ℚ) *
          (integer other : ℚ)) = 0 at integerEquation
        rw [singleRational] at integerEquation
        have zero : integer localCoordinate = 0 := by exact_mod_cast integerEquation
        exact (dite_eq_left present).trans zero
    · simp only [extendedIntercept, extendedInteger, dite_eq_right present, ite_eq_right nonzero,
        and_self]
  · intro coordinate zero
    by_cases present : coordinate ∈ M.realizedCoordinates
    · let localCoordinate : Coordinate := ⟨coordinate, present⟩
      have strict := integerStrict (Sum.inl ⟨localCoordinate, zero⟩)
      change (0 : ℚ) < ∑ other, (if other = localCoordinate then 1 else 0 : ℚ) *
        (integer other : ℚ) at strict
      rw [singleRational] at strict
      have positive : 0 < integer localCoordinate := by exact_mod_cast strict
      simpa only [extendedInteger, dite_eq_left present] using positive
    · simp only [extendedInteger, dite_eq_right present, ite_eq_left zero]
      exact zero_lt_one
  · intro who site history nonzero
    let index : BeliefIndex := ⟨who, site, history⟩
    have realEquation := congrFun interceptEq (Sum.inr ⟨index, nonzero⟩)
    have integerEquation := congrFun integerEq (Sum.inr ⟨index, nonzero⟩)
    constructor
    · simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
        Rat.coe_castHom, equations, limit, difference, nature, belief, index,
        Rat.cast_sub, Rat.cast_natCast, interceptOn] using realEquation
    · simpa only [Matrix.mulVec, dotProduct, equations, difference, index, Pi.zero_apply,
        integerOn] using integerEquation
  · intro who site history zero
    have strict := integerStrict (Sum.inr ⟨⟨who, site, history⟩, zero⟩)
    simpa only [Matrix.mulVec, dotProduct, inequalities, difference, integerOn] using strict

end GameTheory.Protocol.InformationModel
