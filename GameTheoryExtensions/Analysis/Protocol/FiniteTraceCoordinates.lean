/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.PowerReach
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Finite behavioral coordinates drawn along actual histories

A finite set of legal histories draws only finitely many shared information and
choice coordinates, even when the ambient information carriers are infinite.
The finite cover retains every actual occurrence with its multiplicity and
supports the existing power and log-reach formulas without nominal-state sums.
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


open Classical in
/-- Coordinates actually drawn along this trace, including inactive draws. -/
def drawCoordinates : {state : E.State} → E.Trace state → Finset M.BehavioralCoordinate
  | _, .start => ∅
  | _, .extend prior joint legal _ => drawCoordinates prior ∪
      Finset.univ.image (fun who =>
        ⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩)

theorem draw_mem_extend {source target : E.State} (prior : E.Trace source)
    (joint : ∀ who, Option (E.Action who)) (legal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, legal⟩).support) (who : ι) :
    (⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩ :
      M.BehavioralCoordinate) ∈
      M.drawCoordinates (prior.extend joint legal realized) := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨who, Finset.mem_univ _, rfl⟩)

/-- No count outside the factual trace cover can contribute to any sum. -/
theorem historyActionCount_eq_zero_of_not_mem_draw {state : E.State} (trace : E.Trace state)
    (coordinate : M.BehavioralCoordinate) (missing : coordinate ∉ M.drawCoordinates trace) :
    M.historyActionCount trace coordinate = 0 := by
  classical
  induction trace with
  | start => rfl
  | extend prior joint legal realized ih =>
      simp only [drawCoordinates, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and, not_or] at missing
      simp only [historyActionCount]
      rw [ih missing.1, zero_add]
      apply Finset.sum_eq_zero
      intro who _
      apply ite_eq_right
      intro same
      exact missing.2 ⟨who, same.symm⟩

open Classical in
/-- The finite union of coordinate draws over every actual legal history. -/
def realizedCoordinates [Finite E.History] : Finset M.BehavioralCoordinate :=
  let : Fintype E.History := Fintype.ofFinite _
  Finset.univ.biUnion (fun history : E.History => M.drawCoordinates history.trace)

theorem drawCoordinates_subset_realized [Finite E.History] {state : E.State}
    (trace : E.Trace state) : M.drawCoordinates trace ⊆ M.realizedCoordinates := by
  classical
  let : Fintype E.History := Fintype.ofFinite _
  intro coordinate member
  change coordinate ∈ Finset.univ.biUnion (fun history : E.History =>
    M.drawCoordinates history.trace)
  exact Finset.mem_biUnion.mpr ⟨⟨state, trace⟩, Finset.mem_univ _, member⟩

theorem historyActionCount_eq_zero_of_not_mem_realized [Finite E.History]
    {state : E.State} (trace : E.Trace state) (coordinate : M.BehavioralCoordinate)
    (missing : coordinate ∉ M.realizedCoordinates) :
    M.historyActionCount trace coordinate = 0 :=
  M.historyActionCount_eq_zero_of_not_mem_draw trace coordinate
    (fun drawn => missing (M.drawCoordinates_subset_realized trace drawn))

/-- The finite carrier of shared coordinates needed by actual history laws. -/
abbrev RealizedCoordinate [Finite E.History] := {coordinate // coordinate ∈ M.realizedCoordinates}

instance [Finite E.History] : Fintype M.RealizedCoordinate := inferInstance

theorem draw_mem_realized [Finite E.History] {source target : E.State} (prior : E.Trace source)
    (joint : ∀ who, Option (E.Action who)) (legal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, legal⟩).support) (who : ι) :
    (⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩ :
      M.BehavioralCoordinate) ∈
      M.realizedCoordinates :=
  M.drawCoordinates_subset_realized _ (M.draw_mem_extend prior joint legal realized who)

section Cover

theorem historyActionCount_sum_extend_cover {R : Type*} [Semiring R]
    (cover : Finset M.BehavioralCoordinate) (value : cover → R)
    {source target : E.State} (prior : E.Trace source)
    (joint : ∀ who, Option (E.Action who)) (legal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, legal⟩).support)
    (covered : M.drawCoordinates (prior.extend joint legal realized) ⊆ cover) :
    (∑ coordinate : cover,
      (M.historyActionCount (prior.extend joint legal realized) coordinate.1 : R) *
        value coordinate) =
      (∑ coordinate : cover, (M.historyActionCount prior coordinate.1 : R) *
        value coordinate) +
        ∑ who, value ⟨⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩,
          covered (M.draw_mem_extend prior joint legal realized who)⟩ := by
  classical
  simp only [historyActionCount, Nat.cast_add, Nat.cast_sum, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro who _
  have same (coordinate : cover) :
      coordinate.1 = ⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩ ↔
        coordinate = ⟨⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩,
          covered (M.draw_mem_extend prior joint legal realized who)⟩ :=
    ⟨fun equal => Subtype.ext equal, fun equal => congrArg Subtype.val equal⟩
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul, same,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem powerHistoryOrder_cast_eq_sum_cover {R : Type*} [Semiring R]
    (cover : Finset M.BehavioralCoordinate)
    (order : ∀ who info, M.Choice who info → Nat) {state : E.State} (trace : E.Trace state)
    (covered : M.drawCoordinates trace ⊆ cover) :
    (M.powerHistoryOrder order trace : R) = ∑ coordinate : cover,
      (M.historyActionCount trace coordinate.1 : R) *
        (order coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2 : R) := by
  classical
  revert covered
  induction trace with
  | start => intro covered; simp [powerHistoryOrder, historyActionCount]
  | extend prior joint legal realized ih =>
      intro covered
      have priorCovered : M.drawCoordinates prior ⊆ cover :=
        fun coordinate member => covered (Finset.mem_union_left _ member)
      have step := M.historyActionCount_sum_extend_cover cover
        (fun coordinate => (order coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2 : R))
        prior joint legal realized covered
      simp only [powerHistoryOrder, Nat.cast_add, Nat.cast_sum]
      rw [ih priorCovered]
      exact step.symm

theorem powerHistoryOrder_eq_sum_cover (cover : Finset M.BehavioralCoordinate)
    (order : ∀ who info, M.Choice who info → Nat) {state : E.State} (trace : E.Trace state)
    (covered : M.drawCoordinates trace ⊆ cover) :
    M.powerHistoryOrder order trace = ∑ coordinate : cover,
      M.historyActionCount trace coordinate.1 *
        order coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2 := by
  simpa using M.powerHistoryOrder_cast_eq_sum_cover (R := ℕ) cover order trace covered

theorem powerHistoryCoefficient_log_eq_cover
    (cover : Finset M.BehavioralCoordinate)
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    {state : E.State} (trace : E.Trace state)
    (covered : M.drawCoordinates trace ⊆ cover) :
    Real.log (M.powerHistoryCoefficient coefficient trace) =
      historyNatureLog trace + ∑ coordinate : cover,
        (M.historyActionCount trace coordinate.1 : ℝ) *
          Real.log (coefficient coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2) := by
  classical
  revert covered
  induction trace with
  | start => intro covered; simp [powerHistoryCoefficient, historyNatureLog, historyActionCount]
  | extend prior joint legal realized ih =>
      intro covered
      have priorCovered : M.drawCoordinates prior ⊆ cover :=
        fun coordinate member => covered (Finset.mem_union_left _ member)
      have naturePositive := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp realized)
        (PMF.apply_ne_top _ _)
      have jointPositive : 0 < ∏ who,
          coefficient who (M.infoOf who prior) (M.choicesOfLegal prior ⟨joint, legal⟩ who) :=
        Finset.prod_pos fun who _ => positive _ _ _
      rw [M.historyActionCount_sum_extend_cover cover _ prior joint legal realized covered]
      simp only [powerHistoryCoefficient]
      rw [Real.log_mul (M.powerHistoryCoefficient_pos coefficient positive prior).ne'
        (mul_pos jointPositive naturePositive).ne',
        Real.log_mul jointPositive.ne' naturePositive.ne',
        Real.log_prod (fun who _ => (positive who _ _).ne'), ih priorCovered]
      simp only [historyNatureLog]
      ring

theorem historyReachWeight_log_eq_cover (cover : Finset M.BehavioralCoordinate)
    (profile : ∀ who, M.BehavioralPolicy who)
    (full : ∀ who info choice, choice ∈ (profile who info).support)
    {state : E.State} (trace : E.Trace state)
    (covered : M.drawCoordinates trace ⊆ cover) :
    Real.log ((M.historyReachWeight profile ⟨state, trace⟩).toReal) =
      historyNatureLog trace + ∑ coordinate : cover,
        (M.historyActionCount trace coordinate.1 : ℝ) *
          Real.log ((profile coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2).toReal) := by
  classical
  have actionPositive (who : ι) (info : M.InfoState who) (choice : M.Choice who info) :
      0 < (profile who info choice).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (full who info choice)) (PMF.apply_ne_top _ _)
  have reachPositive (history : E.History) :
      0 < (M.historyReachWeight profile history).toReal :=
    ENNReal.toReal_pos
      (M.historyReachWeight_pos_of_fullSupport profile (fun who site => full who site.1)
        history).ne' (PMF.apply_ne_top _ _)
  revert covered
  induction trace with
  | start =>
      intro covered
      simp [historyReachWeight, runBehavioral, runBehavioralFrom, Trace.length,
        runRandomizedFor_zero, historyNatureLog, historyActionCount, ExecutionProtocol.initHistory]
  | @extend source target prior joint legal realized ih =>
      intro covered
      have priorCovered : M.drawCoordinates prior ⊆ cover :=
        fun coordinate member => covered (Finset.mem_union_left _ member)
      have naturePositive : 0 < ((E.step source ⟨joint, legal⟩) target).toReal :=
        ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp realized) (PMF.apply_ne_top _ _)
      have jointPositive : 0 < ∏ who,
          (profile who (M.infoOf who prior) (M.choicesOfLegal prior ⟨joint, legal⟩ who)).toReal :=
        Finset.prod_pos fun who _ => actionPositive _ _ _
      rw [M.historyActionCount_sum_extend_cover cover _ prior joint legal realized covered,
        historyReachProbability_extend]
      simp only [stepProb, behavioralJoint_prob_eq_prod]
      rw [Real.log_mul (reachPositive ⟨source, prior⟩).ne'
        (mul_pos jointPositive naturePositive).ne',
        Real.log_mul jointPositive.ne' naturePositive.ne', Real.log_prod
          (fun who _ => (actionPositive who _ _).ne'), ih priorCovered]
      simp only [historyNatureLog]
      ring

theorem historyLogRate_difference_cover (cover : Finset M.BehavioralCoordinate)
    (profile : ∀ who, M.BehavioralPolicy who)
    (full : ∀ who info choice, choice ∈ (profile who info).support)
    (history reference : E.History)
    (historyCovered : M.drawCoordinates history.trace ⊆ cover)
    (referenceCovered : M.drawCoordinates reference.trace ⊆ cover) :
    (∑ coordinate : cover,
      ((M.historyActionCount history.trace coordinate.1 : ℝ) -
        (M.historyActionCount reference.trace coordinate.1 : ℝ)) *
          (-Real.log ((profile coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2).toReal))) =
      historyNatureLog history.trace - historyNatureLog reference.trace -
        Real.log ((M.historyReachWeight profile history).toReal /
          (M.historyReachWeight profile reference).toReal) := by
  have positive (member : E.History) : 0 < (M.historyReachWeight profile member).toReal :=
    ENNReal.toReal_pos
      (M.historyReachWeight_pos_of_fullSupport profile (fun who site => full who site.1)
        member).ne' (PMF.apply_ne_top _ _)
  rw [Real.log_div (positive history).ne' (positive reference).ne',
    M.historyReachWeight_log_eq_cover cover profile full history.trace historyCovered,
    M.historyReachWeight_log_eq_cover cover profile full reference.trace referenceCovered]
  simp only [sub_mul, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end Cover

section Realized

variable [Finite E.History]

theorem historyActionCount_sum_extend_realized {R : Type*} [Semiring R]
    (value : M.RealizedCoordinate → R)
    {source target : E.State} (prior : E.Trace source)
    (joint : ∀ who, Option (E.Action who)) (legal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, legal⟩).support) :
    (∑ coordinate : M.RealizedCoordinate,
      (M.historyActionCount (prior.extend joint legal realized) coordinate.1 : R) *
        value coordinate) =
      (∑ coordinate : M.RealizedCoordinate, (M.historyActionCount prior coordinate.1 : R) *
        value coordinate) +
        ∑ who, value ⟨⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩,
          M.draw_mem_realized prior joint legal realized who⟩ :=
  M.historyActionCount_sum_extend_cover M.realizedCoordinates value prior joint legal realized
    (M.drawCoordinates_subset_realized _)

theorem powerHistoryOrder_cast_eq_sum_realized {R : Type*} [Semiring R]
    (order : ∀ who info, M.Choice who info → Nat) {state : E.State} (trace : E.Trace state) :
    (M.powerHistoryOrder order trace : R) = ∑ coordinate : M.RealizedCoordinate,
      (M.historyActionCount trace coordinate.1 : R) *
        (order coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2 : R) :=
  M.powerHistoryOrder_cast_eq_sum_cover M.realizedCoordinates order trace
    (M.drawCoordinates_subset_realized trace)

theorem powerHistoryCoefficient_log_eq_realized
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    {state : E.State} (trace : E.Trace state) :
    Real.log (M.powerHistoryCoefficient coefficient trace) =
      historyNatureLog trace + ∑ coordinate : M.RealizedCoordinate,
        (M.historyActionCount trace coordinate.1 : ℝ) *
          Real.log (coefficient coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2) :=
  M.powerHistoryCoefficient_log_eq_cover M.realizedCoordinates coefficient positive trace
    (M.drawCoordinates_subset_realized trace)

theorem historyReachWeight_log_eq_realized (profile : ∀ who, M.BehavioralPolicy who)
    (full : ∀ who info choice, choice ∈ (profile who info).support)
    {state : E.State} (trace : E.Trace state) :
    Real.log ((M.historyReachWeight profile ⟨state, trace⟩).toReal) =
      historyNatureLog trace + ∑ coordinate : M.RealizedCoordinate,
        (M.historyActionCount trace coordinate.1 : ℝ) *
          Real.log ((profile coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2).toReal) :=
  M.historyReachWeight_log_eq_cover M.realizedCoordinates profile full trace
    (M.drawCoordinates_subset_realized trace)

theorem historyLogRate_difference_realized (profile : ∀ who, M.BehavioralPolicy who)
    (full : ∀ who info choice, choice ∈ (profile who info).support)
    (history reference : E.History) :
    (∑ coordinate : M.RealizedCoordinate,
      ((M.historyActionCount history.trace coordinate.1 : ℝ) -
        (M.historyActionCount reference.trace coordinate.1 : ℝ)) *
          (-Real.log ((profile coordinate.1.1 coordinate.1.2.1 coordinate.1.2.2).toReal))) =
      historyNatureLog history.trace - historyNatureLog reference.trace -
        Real.log ((M.historyReachWeight profile history).toReal /
          (M.historyReachWeight profile reference).toReal) :=
  M.historyLogRate_difference_cover M.realizedCoordinates profile full history reference
    (M.drawCoordinates_subset_realized history.trace)
    (M.drawCoordinates_subset_realized reference.trace)

end Realized

end GameTheory.Protocol.InformationModel
