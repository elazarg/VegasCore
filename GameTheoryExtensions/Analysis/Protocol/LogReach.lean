/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.PowerReach
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Shared behavioral coordinates in actual log reach weights

Finite history occurrence counts use actual information/action pairs. Fixed
Nature factors are kept separately. Under full support the existing evaluator's
log reach weight is exactly the affine form in these shared action log masses.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)

/-- One globally shared player, information state and legal local action. -/
abbrev BehavioralCoordinate := Σ who, Σ info : M.InfoState who, M.Choice who info

open Classical in
/-- Occurrence counts include every actual local draw with its multiplicity. -/
def historyActionCount : {state : E.State} → E.Trace state → M.BehavioralCoordinate → Nat
  | _, .start => fun _ => 0
  | _, .extend prior joint legal _ => fun coordinate =>
      historyActionCount prior coordinate + ∑ who,
        if coordinate = ⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩
          then 1 else 0

/-- The fixed log Nature contribution on a legal realized history. -/
def historyNatureLog : {state : E.State} → E.Trace state → ℝ
  | _, .start => 0
  | target, .extend (source := source) prior joint legal _ =>
      historyNatureLog prior + Real.log (((E.step source ⟨joint, legal⟩) target).toReal)

section Finite

variable [∀ who, Fintype (M.InfoState who)] [∀ who info, Fintype (M.Choice who info)]

theorem historyActionCount_sum_extend {R : Type*} [Semiring R]
    (value : M.BehavioralCoordinate → R)
    {source target : E.State} (prior : E.Trace source)
    (joint : ∀ who, Option (E.Action who)) (legal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, legal⟩).support) :
    (∑ coordinate, (M.historyActionCount (prior.extend joint legal realized) coordinate : R) *
      value coordinate) =
      (∑ coordinate, (M.historyActionCount prior coordinate : R) * value coordinate) +
        ∑ who, value ⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩ := by
  classical
  simp only [historyActionCount, Nat.cast_add, Nat.cast_sum, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro who _
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The shared-coordinate count vector evaluates to the actual total power. -/
theorem powerHistoryOrder_eq_sum (order : ∀ who info, M.Choice who info → Nat)
    {state : E.State} (trace : E.Trace state) :
    M.powerHistoryOrder order trace = ∑ coordinate,
      M.historyActionCount trace coordinate * order coordinate.1 coordinate.2.1 coordinate.2.2 := by
  induction trace with
  | start => simp [powerHistoryOrder, historyActionCount]
  | extend prior joint legal realized induction =>
    have step := M.historyActionCount_sum_extend
      (fun coordinate => order coordinate.1 coordinate.2.1 coordinate.2.2)
      prior joint legal realized
    simp only [Nat.cast_id] at step
    simp only [powerHistoryOrder]
    rw [induction]
    exact step.symm

theorem powerHistoryOrder_cast_eq_sum {R : Type*} [Semiring R]
    (order : ∀ who info, M.Choice who info → Nat) {state : E.State} (trace : E.Trace state) :
    (M.powerHistoryOrder order trace : R) = ∑ coordinate,
      (M.historyActionCount trace coordinate : R) *
        (order coordinate.1 coordinate.2.1 coordinate.2.2 : R) := by
  rw [M.powerHistoryOrder_eq_sum]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- Leading coefficients have the same shared log form, with the actual fixed
Nature term and positive supplied local coefficients. -/
theorem powerHistoryCoefficient_log_eq
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    {state : E.State} (trace : E.Trace state) :
    Real.log (M.powerHistoryCoefficient coefficient trace) =
      historyNatureLog trace + ∑ coordinate, (M.historyActionCount trace coordinate : ℝ) *
        Real.log (coefficient coordinate.1 coordinate.2.1 coordinate.2.2) := by
  induction trace with
  | start => simp [powerHistoryCoefficient, historyNatureLog, historyActionCount]
  | extend prior joint legal realized induction =>
    have naturePositive := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp realized)
      (PMF.apply_ne_top _ _)
    have jointPositive : 0 < ∏ who,
        coefficient who (M.infoOf who prior) (M.choicesOfLegal prior ⟨joint, legal⟩ who) :=
      Finset.prod_pos fun who _ => positive _ _ _
    rw [M.historyActionCount_sum_extend]
    simp only [powerHistoryCoefficient]
    rw [Real.log_mul (M.powerHistoryCoefficient_pos coefficient positive prior).ne'
      (mul_pos jointPositive naturePositive).ne', Real.log_mul jointPositive.ne' naturePositive.ne',
      Real.log_prod (fun who _ => (positive who _ _).ne'), induction]
    simp only [historyNatureLog]
    ring

/-- Exact finite affine log representation of the actual canonical evaluator. -/
theorem historyReachWeight_log_eq (profile : ∀ who, M.BehavioralPolicy who)
    (full : ∀ who info choice, choice ∈ (profile who info).support)
    {state : E.State} (trace : E.Trace state) :
    Real.log ((M.historyReachWeight profile ⟨state, trace⟩).toReal) =
      historyNatureLog trace + ∑ coordinate,
        (M.historyActionCount trace coordinate : ℝ) *
          Real.log ((profile coordinate.1 coordinate.2.1 coordinate.2.2).toReal) := by
  classical
  have actionPositive (who : ι) (info : M.InfoState who) (choice : M.Choice who info) :
      0 < (profile who info choice).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (full who info choice)) (PMF.apply_ne_top _ _)
  have reachPositive (history : E.History) :
      0 < (M.historyReachWeight profile history).toReal :=
    ENNReal.toReal_pos
      (M.historyReachWeight_pos_of_fullSupport profile (fun who site => full who site.1)
        history).ne' (PMF.apply_ne_top _ _)
  induction trace with
  | start => simp [historyReachWeight, runBehavioral, runBehavioralFrom, Trace.length,
      runRandomizedFor_zero, historyNatureLog, historyActionCount, ExecutionProtocol.initHistory]
  | @extend source target prior joint legal realized induction =>
    have naturePositive : 0 < ((E.step source ⟨joint, legal⟩) target).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp realized) (PMF.apply_ne_top _ _)
    have jointPositive : 0 < ∏ who,
        (profile who (M.infoOf who prior) (M.choicesOfLegal prior ⟨joint, legal⟩ who)).toReal :=
      Finset.prod_pos fun who _ => actionPositive _ _ _
    rw [M.historyActionCount_sum_extend, historyReachProbability_extend]
    simp only [stepProb, behavioralJoint_prob_eq_prod]
    rw [Real.log_mul (reachPositive ⟨source, prior⟩).ne'
      (mul_pos jointPositive naturePositive).ne',
      Real.log_mul jointPositive.ne' naturePositive.ne', Real.log_prod
        (fun who _ => (actionPositive who _ _).ne'), induction]
    simp only [historyNatureLog]
    ring

/-- The difference of actual log reach weights is the rational count-difference
row evaluated on the negative action logs, plus the fixed Nature difference. -/
theorem historyLogRate_difference (profile : ∀ who, M.BehavioralPolicy who)
    (full : ∀ who info choice, choice ∈ (profile who info).support)
    (history reference : E.History) :
    (∑ coordinate, ((M.historyActionCount history.trace coordinate : ℝ) -
      (M.historyActionCount reference.trace coordinate : ℝ)) *
        (-Real.log ((profile coordinate.1 coordinate.2.1 coordinate.2.2).toReal))) =
      historyNatureLog history.trace - historyNatureLog reference.trace -
        Real.log ((M.historyReachWeight profile history).toReal /
          (M.historyReachWeight profile reference).toReal) := by
  have positive (member : E.History) : 0 < (M.historyReachWeight profile member).toReal :=
    ENNReal.toReal_pos
      (M.historyReachWeight_pos_of_fullSupport profile (fun who site => full who site.1)
        member).ne' (PMF.apply_ne_top _ _)
  rw [Real.log_div (positive history).ne' (positive reference).ne',
    M.historyReachWeight_log_eq profile full history.trace,
    M.historyReachWeight_log_eq profile full reference.trace]
  simp only [sub_mul, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end Finite

end GameTheory.Protocol.InformationModel
