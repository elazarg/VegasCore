/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Math.Probability.NormalizedPower
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Leading powers of actual behavioral history weights

Shared information/action coordinates are normalized separately at each local
menu. The exact evaluator factorization retains every local normalizer,
including when different histories encounter different menus.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)
  [∀ who info, Fintype (M.Choice who info)]

/-- The same local power law is used at every occurrence of an information state. -/
def powerProfile (base : ∀ who, M.BehavioralPolicy who)
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    (order : ∀ who info, M.Choice who info → Nat) (t : ℝ) (tPositive : 0 < t) :
    ∀ who, M.BehavioralPolicy who := fun who info =>
  let : Nonempty (M.Choice who info) := ⟨(base who info).support_nonempty.choose⟩
  normalizedPower (coefficient who info) (positive who info) (order who info) t tPositive

omit [Fintype ι] in
theorem powerProfile_full (base : ∀ who, M.BehavioralPolicy who)
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    (order : ∀ who info, M.Choice who info → Nat) (t : ℝ) (tPositive : 0 < t)
    (who : ι) (site : M.InformationSite who) (choice : M.Choice who site.1) :
    choice ∈ (M.powerProfile base coefficient positive order t tPositive who site.1).support :=
  normalizedPower_supported (coefficient who site.1) (positive who site.1) (order who site.1)
    t tPositive choice

/-- The total exponent counts every occurrence of the shared local coordinates. -/
def powerHistoryOrder (order : ∀ who info, M.Choice who info → Nat) :
    {state : E.State} → E.Trace state → Nat
  | _, .start => 0
  | _, .extend prior joint legal _ =>
      powerHistoryOrder order prior +
        ∑ who, order who (M.infoOf who prior) (M.choicesOfLegal prior ⟨joint, legal⟩ who)

/-- Leading coefficients retain the actual fixed Nature transition probabilities. -/
def powerHistoryCoefficient (coefficient : ∀ who info, M.Choice who info → ℝ) :
    {state : E.State} → E.Trace state → ℝ
  | _, .start => 1
  | target, .extend (source := source) prior joint legal _ =>
      powerHistoryCoefficient coefficient prior *
        ((∏ who, coefficient who (M.infoOf who prior)
          (M.choicesOfLegal prior ⟨joint, legal⟩ who)) *
            ((E.step source ⟨joint, legal⟩) target).toReal)

/-- Each encountered local denominator occurs with its actual multiplicity. -/
def powerHistoryNormalizer (coefficient : ∀ who info, M.Choice who info → ℝ)
    (order : ∀ who info, M.Choice who info → Nat) (t : ℝ) :
    {state : E.State} → E.Trace state → ℝ
  | _, .start => 1
  | _, .extend prior _ _ _ => powerHistoryNormalizer coefficient order t prior *
      ∏ who, powerNormalizer (coefficient who (M.infoOf who prior))
        (order who (M.infoOf who prior)) t

omit [∀ who info, Fintype (M.Choice who info)] in
theorem powerHistoryCoefficient_pos
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    {state : E.State} (trace : E.Trace state) :
    0 < M.powerHistoryCoefficient coefficient trace := by
  induction trace with
  | start => exact zero_lt_one
  | extend prior joint legal realized induction =>
    simp only [powerHistoryCoefficient]
    apply mul_pos induction
    apply mul_pos (Finset.prod_pos fun who _ => positive _ _ _)
    exact ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp realized) (PMF.apply_ne_top _ _)

/-- Exact factorization for the existing evaluator, before any limiting argument. -/
theorem powerProfile_historyReachWeight
    (base : ∀ who, M.BehavioralPolicy who)
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    (order : ∀ who info, M.Choice who info → Nat) (t : ℝ) (tPositive : 0 < t)
    {state : E.State} (trace : E.Trace state) :
    (M.historyReachWeight (M.powerProfile base coefficient positive order t tPositive)
      ⟨state, trace⟩).toReal =
      M.powerHistoryCoefficient coefficient trace * t ^ M.powerHistoryOrder order trace /
        M.powerHistoryNormalizer coefficient order t trace := by
  induction trace with
  | start => simp [historyReachWeight, runBehavioral, runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor_zero, ExecutionProtocol.Trace.length,
      ExecutionProtocol.initHistory, powerHistoryCoefficient, powerHistoryOrder,
      powerHistoryNormalizer]
  | @extend source target prior joint legal realized induction =>
    rw [historyReachProbability_extend, induction]
    simp only [stepProb, behavioralJoint_prob_eq_prod, powerProfile, normalizedPower_toReal,
      powerHistoryCoefficient, powerHistoryOrder, powerHistoryNormalizer,
      Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add]
    ring

/-- Every local normalizer tends to one, so their actual finite history product
also tends to one without requiring cancellation between histories. -/
theorem powerHistoryNormalizer_tendsto
    (base : ∀ who, M.BehavioralPolicy who)
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (order : ∀ who info, M.Choice who info → Nat)
    (constantTerm : ∀ who info choice,
      (if order who info choice = 0 then coefficient who info choice else 0) =
        (base who info choice).toReal)
    {parameter : Nat → ℝ} (vanishes : Tendsto parameter atTop (nhds 0))
    {state : E.State} (trace : E.Trace state) :
    Tendsto (fun n => M.powerHistoryNormalizer coefficient order (parameter n) trace)
      atTop (nhds 1) := by
  induction trace with
  | start => exact tendsto_const_nhds
  | extend prior joint legal realized induction =>
    have localLimit (who : ι) :
        Tendsto (fun n => powerNormalizer (coefficient who (M.infoOf who prior))
          (order who (M.infoOf who prior)) (parameter n)) atTop (nhds 1) := by
      have sum : (∑ choice, if order who (M.infoOf who prior) choice = 0 then
          coefficient who (M.infoOf who prior) choice else 0) = 1 := by
        simp_rw [constantTerm]
        exact (mem_simplexWeights.mp
          (PMF.toReal_mem_simplexWeights (base who (M.infoOf who prior)))).2
      rw [← sum]
      exact powerNormalizer_tendsto _ _ vanishes
    simpa only [powerHistoryNormalizer, Finset.prod_const_one, mul_one] using
      induction.mul (tendsto_finsetProd Finset.univ fun who _ => localLimit who)

/-- The actual reach weight divided by its leading power converges to the
strictly positive coefficient determined by Nature and shared action data. -/
theorem powerProfile_history_scaled_tendsto
    (base : ∀ who, M.BehavioralPolicy who)
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    (order : ∀ who info, M.Choice who info → Nat)
    (constantTerm : ∀ who info choice,
      (if order who info choice = 0 then coefficient who info choice else 0) =
        (base who info choice).toReal)
    {parameter : Nat → ℝ} (parameterPositive : ∀ n, 0 < parameter n)
    (vanishes : Tendsto parameter atTop (nhds 0)) {state : E.State} (trace : E.Trace state) :
    Tendsto (fun n =>
      (M.historyReachWeight (M.powerProfile base coefficient positive order
        (parameter n) (parameterPositive n)) ⟨state, trace⟩).toReal /
          parameter n ^ M.powerHistoryOrder order trace)
      atTop (nhds (M.powerHistoryCoefficient coefficient trace)) := by
  have denominator := M.powerHistoryNormalizer_tendsto base coefficient order constantTerm
    vanishes trace
  have limit : Tendsto (fun n => M.powerHistoryCoefficient coefficient trace /
      M.powerHistoryNormalizer coefficient order (parameter n) trace) atTop
        (nhds (M.powerHistoryCoefficient coefficient trace)) := by
    simpa only [div_one, Pi.div_def] using
      (tendsto_const_nhds (x := M.powerHistoryCoefficient coefficient trace)).div denominator
        (by norm_num : (1 : ℝ) ≠ 0)
  apply limit.congr'
  filter_upwards [] with n
  rw [M.powerProfile_historyReachWeight]
  field_simp [ne_of_gt (parameterPositive n)]

end GameTheory.Protocol.InformationModel
