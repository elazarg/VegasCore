/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkSourceLikelihood
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # Actual source consistency for the private-type resolution fork

Alice's fully mixed source disclosures have FALSE weights t and t² at HIGH
and LOW. A common subsequence of the actual source Bayes assessments retains
those information likelihoods. Native information and native equilibrium
claims are separate obligations.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter

def sourceTrembleWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem sourceTrembleWeight_positive (n : ℕ) : 0 < sourceTrembleWeight n := by
  unfold sourceTrembleWeight
  positivity

theorem sourceTrembleWeight_lt_one (n : ℕ) : sourceTrembleWeight n < 1 := by
  unfold sourceTrembleWeight
  apply (div_lt_one (by positivity : 0 < (n : ℝ) + 2)).mpr
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

theorem sourceTrembleWeight_tendsto :
    Tendsto sourceTrembleWeight atTop (nhds 0) := by
  have limit := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  convert limit using 1
  funext n
  norm_num [sourceTrembleWeight, Function.comp_def, Nat.cast_add, add_assoc]

def sourceFalseWeight (n : ℕ) (high : Bool) : ℝ :=
  if high then sourceTrembleWeight n else (sourceTrembleWeight n) ^ 2

theorem sourceFalseWeight_positive (n : ℕ) (high : Bool) :
    0 < sourceFalseWeight n high := by
  cases high <;> simp only [sourceFalseWeight, Bool.false_eq_true, ite_false, ite_true]
  · exact sq_pos_of_pos (sourceTrembleWeight_positive n)
  · exact sourceTrembleWeight_positive n

theorem sourceFalseWeight_lt_one (n : ℕ) (high : Bool) :
    sourceFalseWeight n high < 1 := by
  cases high <;> simp only [sourceFalseWeight, Bool.false_eq_true, ite_false, ite_true]
  · nlinarith [sourceTrembleWeight_positive n, sourceTrembleWeight_lt_one n]
  · exact sourceTrembleWeight_lt_one n

def sourceAliceTremble (n : ℕ) (high : Bool) : PMF Bool :=
  mix (sourceFalseWeight n high) (sourceFalseWeight_positive n high).le
    (sourceFalseWeight_lt_one n high).le (PMF.pure false) (PMF.pure true)

def sourceBobTremble (n : ℕ) (disclose : Bool) : PMF Bool :=
  mix (sourceTrembleWeight n) (sourceTrembleWeight_positive n).le
    (sourceTrembleWeight_lt_one n).le (PMF.uniformOfFintype Bool)
      (PMF.pure (!disclose))

theorem sourceAliceTremble_full (n : ℕ) (high : Bool) :
    FullSupport (sourceAliceTremble n high) := by
  intro answer
  change answer ∈ (mix _ _ _ _ _).support
  rw [mem_support_mix_pure_iff _ _ _ (sourceFalseWeight_positive n high)
    (sourceFalseWeight_lt_one n high)]
  cases answer <;> simp

theorem sourceBobTremble_full (n : ℕ) (disclose : Bool) :
    FullSupport (sourceBobTremble n disclose) := by
  intro answer
  exact mem_support_mix_left _ _ _ (sourceTrembleWeight_positive n) (by simp)

def sourceAssessmentSequence (n : ℕ) : sourceModel.BehavioralAssessment :=
  sourceBayes (sourceAliceTremble n) (sourceBobTremble n)
    (sourceAliceTremble_full n) (sourceBobTremble_full n)

def sourceEquilibriumProfile : Profile sourceModel.behavioralSignature :=
  sourceProfile (fun _ => PMF.pure true) (fun disclose => PMF.pure (!disclose))

theorem source_alice_profile_map (aliceLaw bobLaw : Bool → PMF Bool) (high : Bool) :
    (sourceProfile aliceLaw bobLaw alice
      (setup.protocolObserve alice (SourcePosition.ready high).state)).map Subtype.val =
      (aliceLaw high).map (fun disclose => some (OwnAction.reveal alice 0 disclose)) := by
  rw [sourceProfile, Setup.toProtocolBehavioralPolicy_map_val]
  cases high <;> rfl

theorem source_bob_profile_map (aliceLaw bobLaw : Bool → PMF Bool)
    (high disclose : Bool) :
    (sourceProfile aliceLaw bobLaw bob
      (setup.protocolObserve bob (SourcePosition.guessed high disclose).state)).map Subtype.val =
      (bobLaw disclose).map (fun guess => some (OwnAction.reveal bob 1 guess)) := by
  rw [sourceProfile, Setup.toProtocolBehavioralPolicy_map_val]
  cases high <;> cases disclose <;> rfl

theorem sourceAssessmentSequence_strategy_converges
    (who : Player) (site : sourceModel.InformationSite who) :
    PMFConvergesPointwise (fun n => (sourceAssessmentSequence n).strategy who site.1)
      (sourceEquilibriumProfile who site.1) := by
  classical
  obtain ⟨history, _, _⟩ := site.2
  have observed : site.1 = setup.protocolObserve who history.1.state :=
    history.2.symm.trans (source_history_observe who history.1)
  have mapped : PMFConvergesPointwise
      (fun n => ((sourceAssessmentSequence n).strategy who site.1).map Subtype.val)
      ((sourceEquilibriumProfile who site.1).map Subtype.val) := by
    fin_cases who
    · obtain ⟨high, same⟩ := source_alice_active_state site history
      rw [observed, same]
      change PMFConvergesPointwise
        (fun n => (sourceProfile (sourceAliceTremble n) (sourceBobTremble n) alice
          (setup.protocolObserve alice (SourcePosition.ready high).state)).map Subtype.val)
        ((sourceProfile (fun _ => PMF.pure true) (fun disclose => PMF.pure (!disclose)) alice
          (setup.protocolObserve alice (SourcePosition.ready high).state)).map Subtype.val)
      simp only [source_alice_profile_map]
      have vanishes : Tendsto (fun n => sourceFalseWeight n high) atTop (nhds 0) := by
        cases high
        · simpa [sourceFalseWeight] using sourceTrembleWeight_tendsto.pow 2
        · exact sourceTrembleWeight_tendsto
      exact (pmfConvergesPointwise_mix_zero _
        (fun n => (sourceFalseWeight_positive n high).le)
        (fun n => (sourceFalseWeight_lt_one n high).le) vanishes _ _).map _
    · obtain ⟨high, disclose, same⟩ := source_bob_active_state site history
      rw [observed, same]
      change PMFConvergesPointwise
        (fun n => (sourceProfile (sourceAliceTremble n) (sourceBobTremble n) bob
          (setup.protocolObserve bob (SourcePosition.guessed high disclose).state)).map Subtype.val)
        ((sourceProfile (fun _ => PMF.pure true) (fun disclose => PMF.pure (!disclose)) bob
          (setup.protocolObserve bob (SourcePosition.guessed high disclose).state)).map Subtype.val)
      simp only [source_bob_profile_map]
      exact (pmfConvergesPointwise_mix_zero _
        (fun n => (sourceTrembleWeight_positive n).le)
        (fun n => (sourceTrembleWeight_lt_one n).le) sourceTrembleWeight_tendsto _ _).map _
  intro choice
  simpa only [pmf_map_apply_of_injective _ Subtype.val_injective] using mapped choice.val

private theorem sourceAliceTremble_converges (high : Bool) :
    PMFConvergesPointwise (fun n => sourceAliceTremble n high) (PMF.pure true) := by
  have vanishes : Tendsto (fun n => sourceFalseWeight n high) atTop (nhds 0) := by
    cases high
    · simpa [sourceFalseWeight] using sourceTrembleWeight_tendsto.pow 2
    · exact sourceTrembleWeight_tendsto
  exact pmfConvergesPointwise_mix_zero _
    (fun n => (sourceFalseWeight_positive n high).le)
    (fun n => (sourceFalseWeight_lt_one n high).le) vanishes _ _

@[simp] theorem sourceAliceTremble_false_mass (n : ℕ) (high : Bool) :
    (sourceAliceTremble n high false).toReal = sourceFalseWeight n high := by
  rw [sourceAliceTremble, mix_apply_toReal]
  simp

@[simp] theorem sourceAliceTremble_true_mass (n : ℕ) (high : Bool) :
    (sourceAliceTremble n high true).toReal = 1 - sourceFalseWeight n high := by
  rw [sourceAliceTremble, mix_apply_toReal]
  simp

theorem sourceAssessmentSequence_false_type_mass (n : ℕ)
    (site : sourceModel.InformationSite bob) (observed : site.1 = sourceBobInput false) :
    (((sourceAssessmentSequence n).belief bob site).toOuterMeasure
      {history | sourceBobType history.1.state = some true}).toReal =
        1 / (1 + 3 * sourceTrembleWeight n) := by
  rw [sourceAssessmentSequence, source_bayes_type_mass _ _ _ _ site false observed]
  simp only [sourceAliceTremble_false_mass, sourceFalseWeight,
    Bool.false_eq_true, ite_false, ite_true]
  have positive := sourceTrembleWeight_positive n
  have denominator : (1 / 4 : ℝ) * sourceTrembleWeight n +
      3 / 4 * sourceTrembleWeight n ^ 2 ≠ 0 := by positivity
  have second : 1 + 3 * sourceTrembleWeight n ≠ 0 := by positivity
  field_simp [denominator, second]

theorem sourceAssessmentSequence_type_limit (site : sourceModel.InformationSite bob)
    (disclose : Bool) (observed : site.1 = sourceBobInput disclose) :
    Tendsto (fun n => (((sourceAssessmentSequence n).belief bob site).toOuterMeasure
      {history | sourceBobType history.1.state = some true}).toReal) atTop
      (nhds (if disclose then (1 / 4 : ℝ) else 1)) := by
  cases disclose with
  | false =>
      have rewritten : (fun n => (((sourceAssessmentSequence n).belief bob site).toOuterMeasure
          {history | sourceBobType history.1.state = some true}).toReal) =
          fun n => 1 / (1 + 3 * sourceTrembleWeight n) :=
        funext fun n => sourceAssessmentSequence_false_type_mass n site observed
      rw [rewritten]
      have denominator : Tendsto (fun n => 1 + 3 * sourceTrembleWeight n) atTop
          (nhds (1 : ℝ)) := by
        simpa only [mul_zero, add_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add
            ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3)).mul
              sourceTrembleWeight_tendsto)
      simpa only [one_div, Bool.false_eq_true, ite_false, inv_one] using
        denominator.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  | true =>
      have high := (sourceAliceTremble_converges true).toReal true
      have low := (sourceAliceTremble_converges false).toReal true
      simp only [PMF.pure_apply_self, ENNReal.toReal_one] at high low
      have numerator : Tendsto
          (fun n => (1 / 4 : ℝ) * (sourceAliceTremble n true true).toReal) atTop
          (nhds ((1 / 4 : ℝ) * 1)) := tendsto_const_nhds.mul high
      have lower : Tendsto
          (fun n => (3 / 4 : ℝ) * (sourceAliceTremble n false true).toReal) atTop
          (nhds ((3 / 4 : ℝ) * 1)) := tendsto_const_nhds.mul low
      have denominator := numerator.add lower
      have ratio := numerator.div denominator
        (by norm_num : (1 / 4 : ℝ) * 1 + 3 / 4 * 1 ≠ 0)
      have rewritten : (fun n => (((sourceAssessmentSequence n).belief bob site).toOuterMeasure
          {history | sourceBobType history.1.state = some true}).toReal) =
          fun n => ((1 / 4 : ℝ) * (sourceAliceTremble n true true).toReal) /
            ((1 / 4 : ℝ) * (sourceAliceTremble n true true).toReal +
              3 / 4 * (sourceAliceTremble n false true).toReal) := by
        funext n
        exact source_bayes_type_mass _ _ _ _ site true observed
      rw [rewritten]
      convert ratio using 1; norm_num

/-- One actual fully mixed source sequence certifies the strategy and the
on-path and off-path hidden-type beliefs simultaneously. -/
theorem exists_consistent_source_assessment :
    ∃ assessment : sourceModel.BehavioralAssessment,
      assessment.strategy = sourceEquilibriumProfile ∧
      assessment.IsSequentiallyConsistent (setup.decision_antichain sourceAdmission) ∧
      ∀ (site : sourceModel.InformationSite bob) (disclose : Bool),
        site.1 = sourceBobInput disclose →
        ((assessment.belief bob site).toOuterMeasure
          {history | sourceBobType history.1.state = some true}).toReal =
            if disclose then (1 / 4 : ℝ) else 1 := by
  classical
  obtain ⟨assessment, strategy, index, increasing, converges, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion_subsequence
      (setup.decision_antichain sourceAdmission) sourceEquilibriumProfile
      sourceAssessmentSequence
      (fun n who site => sourceProfile_full _ _
        (sourceAliceTremble_full n) (sourceBobTremble_full n) who site.1)
      (fun n => sourceModel.bayesAssessment_isBayesConsistent
        (sourceProfile (sourceAliceTremble n) (sourceBobTremble n))
        (fun who site => sourceProfile_full _ _
          (sourceAliceTremble_full n) (sourceBobTremble_full n) who site.1)
        (setup.decision_antichain sourceAdmission))
      sourceAssessmentSequence_strategy_converges
  refine ⟨assessment, strategy, consistent, ?_⟩
  intro site disclose observed
  have actual := (sourceAssessmentSequence_type_limit site disclose observed).comp
    increasing.tendsto_atTop
  have projected : Tendsto
      (fun n => (((sourceAssessmentSequence (index n)).belief bob site).toOuterMeasure
        {history | sourceBobType history.1.state = some true}).toReal) atTop
      (nhds ((assessment.belief bob site).toOuterMeasure
        {history | sourceBobType history.1.state = some true}).toReal) := by
    let event : Set (sourceModel.InformationHistory bob site.1) :=
      {history | sourceBobType history.1.state = some true}
    have limit := (converges.belief bob site).expect_of_bounded
      (fun history => if history ∈ event then (1 : ℝ) else 0)
      (C := 1) (fun _ => by split_ifs <;> norm_num)
    have eventExpectation (law : PMF (sourceModel.InformationHistory bob site.1)) :
        expect law (fun history => if history ∈ event then (1 : ℝ) else 0) =
          (law.toOuterMeasure event).toReal := by
      calc
        _ = expect law (fun history =>
            @ite ℝ (history ∈ event) (Classical.propDecidable _) 1 0) := by
          apply expect_congr_on_support
          intro history _
          split_ifs <;> rfl
        _ = _ := expect_indicator law event
    simp_rw [eventExpectation] at limit
    exact limit
  exact tendsto_nhds_unique projected actual

end Vegas.PrivateResolutionFork
