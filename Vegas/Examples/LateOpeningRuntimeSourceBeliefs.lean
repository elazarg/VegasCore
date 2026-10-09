/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSource
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Actual source beliefs at the answer commitment

The mandatory opening leaves exactly three possible histories at Bob's
answer commitment. Their labels remain uniform under every behavioral
strategy, so every consistent assessment has this same posterior.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSource

open SourceProgram GameTheory.Math.Probability GameTheory.Protocol
open scoped ENNReal

theorem bobBindingInfo_injective : Function.Injective bobBindingInfo := by
  intro first second same
  have observations := congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj (Option.some.inj same)))
  have publications := congrArg
    (fun observation : SourceObservation simpleExpr bob
      ((2, .publication .bool) :: initialCtx) => observation.cells.get .here) observations
  exact PublicationResult.success.inj publications

private theorem uniform_label_pair_apply (outer bit : Bool) (label : Fin 3) :
    ((PMF.uniformOfFintype (Fin 3)).map (fun value => (outer, value))) (bit, label) =
      if bit = outer then (3 : ℝ≥0∞)⁻¹ else 0 := by
  classical
  by_cases same : bit = outer
  · subst outer
    rw [ite_eq_left rfl,
      pmf_map_apply_of_injective _ (fun _ _ equal => (Prod.mk.inj equal).2) label]
    simp [PMF.uniformOfFintype_apply]
  · rw [ite_eq_right same, PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro value
    have different : (bit, label) ≠ (outer, value) :=
      fun equal => same (Prod.mk.inj equal).1
    simp [different]

theorem prior_apply (bit : Bool) (label : Fin 3) :
    prior (bit, label) = bitLaw bit * (3 : ℝ≥0∞)⁻¹ := by
  classical
  simp only [prior, PMF.bind_apply, uniform_label_pair_apply, tsum_fintype]
  cases bit <;> simp

theorem bitLaw_ne_zero (bit : Bool) : bitLaw bit ≠ 0 := by
  apply (PMF.mem_support_iff _ _).mp
  cases bit
  · exact mem_support_mix_right (9 / 20) (by norm_num) (by norm_num) (by norm_num)
      ((PMF.mem_support_pure_iff _ _).mpr rfl)
  · exact mem_support_mix_left (9 / 20) (by norm_num) (by norm_num) (by norm_num)
      ((PMF.mem_support_pure_iff _ _).mpr rfl)

def bobBindingMember (bit : Bool) (label : Fin 3) :
    setup.intendedModel.InformationHistory bob (bobBindingSite bit).1 :=
  ⟨openedHistory bit label, bobBindingInfo_opened bit label⟩

theorem bobBindingMember_injective (bit : Bool) :
    Function.Injective (bobBindingMember bit) := by
  intro first second same
  exact (Prod.mk.inj (openedHistory_injective (congrArg Subtype.val same))).2

/-- Every legal history at this commitment is one of the three initialized
label histories, including histories that a given strategy does not reach. -/
theorem bobBindingMember_surjective (bit : Bool) :
    Function.Surjective (bobBindingMember bit) := by
  intro history
  let assessment := InformationModel.BehavioralAssessment.ofStrategy intendedUniformProfile
  have mixed : assessment.IsFullyMixed := intendedUniformProfile_mixed
  have supported := mixed.history_supported history.1.trace
  change history.1 ∈
    (setup.intendedModel.runBehavioral intendedUniformProfile history.1.trace.length).support
    at supported
  rw [bobBindingInfo_length history, opening_prefix, PMF.support_map] at supported
  obtain ⟨⟨otherBit, label⟩, _, sameHistory⟩ := supported
  have sameInfo := congrArg
    (fun member : setup.intendedProtocol.History => setup.intendedModel.infoOf bob member.trace)
    sameHistory
  rw [bobBindingInfo_opened, history.2] at sameInfo
  have sameBit := bobBindingInfo_injective sameInfo
  change otherBit = bit at sameBit
  subst otherBit
  exact ⟨label, Subtype.ext sameHistory⟩

def bobBindingEquiv (bit : Bool) :
    Fin 3 ≃ setup.intendedModel.InformationHistory bob (bobBindingSite bit).1 :=
  Equiv.ofBijective (bobBindingMember bit)
    ⟨bobBindingMember_injective bit, bobBindingMember_surjective bit⟩

theorem bobBindingMember_reach
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (bit : Bool) (label : Fin 3) :
    setup.intendedModel.historyReachWeight profile (bobBindingMember bit label).1 =
      prior (bit, label) := by
  change setup.intendedModel.runBehavioral profile 2 (openedHistory bit label) = _
  rw [opening_prefix]
  exact pmf_map_apply_of_injective prior openedHistory_injective (bit, label)

theorem bobBinding_informationMass
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (bit : Bool) :
    setup.intendedModel.informationMass profile bob (bobBindingSite bit) = bitLaw bit := by
  classical
  unfold InformationModel.informationMass
  rw [← (bobBindingEquiv bit).tsum_eq]
  change (∑' label : Fin 3,
    setup.intendedModel.historyReachWeight profile (bobBindingMember bit label).1) = _
  simp only [bobBindingMember_reach, prior_apply, tsum_fintype]
  rw [← Finset.mul_sum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change bitLaw bit * ((3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹) = bitLaw bit
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

theorem bayes_bobBinding_uniform
    {assessment : setup.intendedModel.BehavioralAssessment}
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
      assessment intended_decisionRecall.decisionInformationAntichain) (bit : Bool) :
    assessment.belief bob (bobBindingSite bit) =
      (PMF.uniformOfFintype (Fin 3)).map (bobBindingMember bit) := by
  have positive : 0 <
      setup.intendedModel.informationMass assessment.strategy bob (bobBindingSite bit) := by
    rw [bobBinding_informationMass]
    exact pos_iff_ne_zero.mpr (bitLaw_ne_zero bit)
  apply PMF.ext
  intro history
  obtain ⟨label, rfl⟩ := bobBindingMember_surjective bit history
  rw [bayes bob (bobBindingSite bit) positive,
    bobBindingMember_reach, bobBinding_informationMass, prior_apply,
    pmf_map_apply_of_injective _ (bobBindingMember_injective bit)]
  rw [mul_comm, ENNReal.mul_div_cancel_right (bitLaw_ne_zero bit) (bitLaw.apply_ne_top bit)]
  simp [PMF.uniformOfFintype_apply]

/-- Consistency fixes the posterior without an equilibrium or chosen
tremble rates: the source has already disclosed the bit, and no action has
selected among the three private labels. -/
theorem consistent_bobBinding_uniform
    {assessment : setup.intendedModel.BehavioralAssessment}
    (consistent : assessment.IsSequentiallyConsistent
      intended_decisionRecall.decisionInformationAntichain) (bit : Bool) :
    assessment.belief bob (bobBindingSite bit) =
      (PMF.uniformOfFintype (Fin 3)).map (bobBindingMember bit) := by
  let : Finite setup.intendedProtocol.History :=
    setup.intended_finite_history finiteBindingTypes
  exact bayes_bobBinding_uniform
    (consistent.isBayesConsistent intended_decisionRecall.decisionInformationAntichain) bit

end Vegas.Examples.LateOpeningRuntimeSource
