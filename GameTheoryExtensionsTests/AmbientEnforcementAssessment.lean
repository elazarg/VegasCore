/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.AmbientEnforcementInformation
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheory.Analysis.Protocol.Examples
import GameTheoryExtensions.Math.Probability.Support

/-! # Common consistent beliefs with optional ambient disclosure

Alice stays silent. Bob uses an arbitrary law on silence and guesses correctly
after disclosure. The approximants tremble equally at both Alice types, so the
posterior on silence remains uniform. All decision sites use one sequence.
-/

noncomputable section

namespace GameTheoryExtensionsTests.AmbientEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open GameTheory.Protocol.ExecutionProtocol
open GameTheory.Analysis.Protocol.Examples

def bobRespond (guesses : PMF Bool) : (model true).BehavioralPolicy true := fun info =>
  match info with
  | some (some bit) => choose true true bit (some (some bit))
  | some none => guesses.bind (fun guess => choose true true guess (some none))
  | none => choose true true false none

def silentProfile (guesses : PMF Bool) : Profile (model true).behavioralSignature
  | false => choose true false false
  | true => bobRespond guesses

def targetAssessment (profile : Profile (model true).behavioralSignature) :
    (model true).BehavioralAssessment where
  strategy := profile
  belief who decision := by
    cases who
    · exact PMF.pure ⟨aliceHistory true ((decision.1.getD none).getD false), by
        obtain ⟨bit, rfl⟩ := alice_site_eq decision; rfl⟩
    · by_cases same : decision = bobSilentSite true
      · subst decision
        exact (PMF.uniformOfFintype Bool).map (silentHistory true)
      · exact PMF.pure ⟨bobHistory true ((decision.1.getD none).getD false) true, by
          rcases target_bob_site_eq decision with equal | ⟨bit, equal⟩
          · exact (same equal).elim
          · subst decision; rfl⟩

theorem target_silent_belief (profile : Profile (model true).behavioralSignature) :
    (targetAssessment profile).belief true (bobSilentSite true) =
      (PMF.uniformOfFintype Bool).map (silentHistory true) := by
  simp [targetAssessment]

def uniformReference : (model true).BehavioralAssessment := .ofStrategy fun who info =>
  mix (1 / 2) (by norm_num) (by norm_num)
    (choose true who false info) (choose true who true info)

theorem uniformReference_full : uniformReference.IsFullyMixed := by
  intro who ⟨info, _⟩ ⟨value, legal⟩
  change (⟨value, legal⟩ : (model true).Choice who info) ∈
    (mix (1 / 2) (by norm_num) (by norm_num)
      (choose true who false info) (choose true who true info)).support
  simp only [choose]
  rw [mem_support_mix_pure_iff _ _ _ (by norm_num) (by norm_num)]
  simp only [Subtype.mk.injEq]
  change value.isSome = decisionInfo true who info at legal
  simp only [decisionInfo, Bool.true_or, Bool.true_and] at legal ⊢
  cases info <;> cases value
  all_goals simp_all only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    Bool.true_eq_false, ite_true, ite_false]
  all_goals first | trivial | simp

def targetPerturb (guesses : PMF Bool) (n : Nat) :
    Profile (model true).behavioralSignature :=
  (uniformReference.perturb (silentProfile guesses) (trembleWeight n)
    (trembleWeight_nonneg n) (trembleWeight_le_one n)).strategy

theorem targetPerturb_full (guesses : PMF Bool) (n : Nat) :
    (targetAssessment (targetPerturb guesses n)).IsFullyMixed :=
  uniformReference.perturb_fullyMixed uniformReference_full (silentProfile guesses)
    (trembleWeight n) (trembleWeight_nonneg n) (trembleWeight_le_one n) (trembleWeight_pos n)

theorem target_reach_silent (guesses : PMF Bool) (n : Nat) (bit : Bool) :
    ((model true).historyReachWeight (targetPerturb guesses n) (bobHistory true bit false)).toReal =
      (1 - trembleWeight n / 2) / 2 := by
  classical
  change (((model true).runBehavioralFrom (targetPerturb guesses n) 2
    (arena true).initHistory) (bobHistory true bit false)).toReal = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model true)
      (single true),
    ← pmf_map_apply_of_injective _ (state_injective true), run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, PMF.pure_bind,
    initHistory, kernel, PMF.bind_map, toReal_bind_apply]
  change expect (PMF.uniformOfFintype Bool) (fun hidden =>
    (((choiceLaw (targetPerturb guesses n) false (some (some hidden))).map
      (fun disclose => State.bob hidden disclose)) (.bob bit false)).toReal) = _
  have weight : (ENNReal.ofReal (trembleWeight n) * 2⁻¹ +
      ENNReal.ofReal (1 - trembleWeight n)).toReal =
        trembleWeight n / 2 + (1 - trembleWeight n) := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
        ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_ofReal (trembleWeight_nonneg n),
      ENNReal.toReal_ofReal (by linarith [trembleWeight_le_one n]), ENNReal.toReal_inv,
      ENNReal.toReal_ofNat]
    ring
  rw [expect_eq_sum, Fintype.sum_bool]
  cases bit <;>
    simp [choiceLaw, targetPerturb, InformationModel.BehavioralAssessment.perturb,
      uniformReference, silentProfile, choose, decisionInfo, mix_map,
      Fintype.card_bool, PMF.pure_map, weight] <;> ring

theorem target_mass_silent (guesses : PMF Bool) (n : Nat) :
    ((model true).informationMass (targetPerturb guesses n) true (bobSilentSite true)).toReal =
      1 - trembleWeight n / 2 := by
  unfold InformationModel.informationMass
  rw [← (silentHistories true).tsum_eq, tsum_fintype]
  change (∑ bit : Bool, (model true).historyReachWeight (targetPerturb guesses n)
    (bobHistory true bit false)).toReal = _
  have finiteWeight (bit : Bool) : (model true).historyReachWeight (targetPerturb guesses n)
      (bobHistory true bit false) ≠ ⊤ := PMF.apply_ne_top _ _
  rw [ENNReal.toReal_sum fun bit _ => finiteWeight bit]
  simp only [target_reach_silent, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    nsmul_eq_mul]
  ring

theorem target_belief_silent_prob (profile : Profile (model true).behavioralSignature)
    (bit : Bool) :
    (((targetAssessment profile).belief true (bobSilentSite true))
      (silentHistory true bit)).toReal = 1 / 2 := by
  classical
  rw [target_silent_belief, pmf_map_apply_of_injective _ (silentHistory_injective true)]
  norm_num [toReal_uniformOfFintype_apply, Fintype.card_bool]

theorem targetPerturb_bayes (guesses : PMF Bool) (n : Nat) :
    InformationModel.BehavioralAssessment.IsBayesConsistent (model true)
      (targetAssessment (targetPerturb guesses n)) (antichain true) := by
  intro who decision positive history
  cases who
  · obtain ⟨bit, rfl⟩ := alice_site_eq decision
    have equal : (targetAssessment (targetPerturb guesses n)).belief false (aliceSite bit) =
        (model true).bayesBelief (targetPerturb guesses n) false (aliceSite bit)
          (antichain true false (aliceSite bit)) positive := by
      exact (eq_pure_of_subsingleton _ history).trans
        (eq_pure_of_subsingleton _ history).symm
    rw [equal]
    exact InformationModel.bayesBelief_apply _ _ _ _ _ _ _
  · rcases target_bob_site_eq decision with rfl | ⟨bit, rfl⟩
    · obtain ⟨bit, same⟩ := history_at_silent true history
      have historyEq : history = silentHistory true bit := Subtype.ext same
      subst history
      change (targetAssessment (targetPerturb guesses n)).belief true (bobSilentSite true)
          (silentHistory true bit) =
        (model true).historyReachWeight (targetPerturb guesses n) (bobHistory true bit false) /
          (model true).informationMass (targetPerturb guesses n) true (bobSilentSite true)
      have massNe : (model true).informationMass (targetPerturb guesses n) true
          (bobSilentSite true) ≠ 0 := positive.ne'
      have weightNe : (model true).historyReachWeight (targetPerturb guesses n)
          (bobHistory true bit false) ≠ ⊤ := PMF.apply_ne_top _ _
      rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
          (ENNReal.div_ne_top weightNe massNe), ENNReal.toReal_div,
        target_belief_silent_prob, target_reach_silent, target_mass_silent]
      have nonzero : 1 - trembleWeight n / 2 ≠ 0 := by
        have small := trembleWeight_le_one n
        linarith
      have positiveTwo : 2 - trembleWeight n ≠ 0 := by
        have small := trembleWeight_le_one n
        linarith
      field_simp [nonzero, positiveTwo]
    · have equal : (targetAssessment (targetPerturb guesses n)).belief true
          (bobDisclosedSite bit) =
        (model true).bayesBelief (targetPerturb guesses n) true (bobDisclosedSite bit)
          (antichain true true (bobDisclosedSite bit)) positive := by
        exact (eq_pure_of_subsingleton _ history).trans
          (eq_pure_of_subsingleton _ history).symm
      rw [equal]
      exact InformationModel.bayesBelief_apply _ _ _ _ _ _ _

theorem target_converges (guesses : PMF Bool) :
    InformationModel.BehavioralAssessmentConvergesPointwise
      (fun n => targetAssessment (targetPerturb guesses n))
        (targetAssessment (silentProfile guesses)) := by
  constructor
  · intro who decision
    exact uniformReference.perturb_strategy_converges (silentProfile guesses) trembleWeight
      trembleWeight_nonneg trembleWeight_le_one trembleWeight_tendsto_zero who decision.1
  · intro who decision
    exact pmfConvergesPointwise_const _

theorem target_consistent (guesses : PMF Bool) :
    (targetAssessment (silentProfile guesses)).IsSequentiallyConsistent (antichain true) :=
  ⟨fun n => targetAssessment (targetPerturb guesses n),
    fun n => ⟨targetPerturb_full guesses n, targetPerturb_bayes guesses n⟩,
    target_converges guesses⟩

end GameTheoryExtensionsTests.AmbientEnforcement
