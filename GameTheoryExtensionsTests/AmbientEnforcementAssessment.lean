/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.AmbientEnforcementInformation
import GameTheoryExtensions.Math.Probability.FinDist
import GameTheory.Analysis.Protocol.Examples

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

def bobRespond (guesses : FinDist Bool) : (model true).BehavioralPolicy true := fun info =>
  match info with
  | some (some bit) => choose true true bit (some (some bit))
  | some none => guesses.bind (fun guess => choose true true guess (some none))
  | none => choose true true false none

def silentProfile (guesses : FinDist Bool) : Profile (model true).behavioralSignature
  | false => choose true false false
  | true => bobRespond guesses

def targetAssessment (profile : Profile (model true).behavioralSignature) :
    (model true).BehavioralAssessment where
  strategy := profile
  belief who decision := by
    cases who
    · exact FinDist.pure ⟨aliceHistory true ((decision.1.getD none).getD false), by
        obtain ⟨bit, rfl⟩ := alice_site_eq decision; rfl⟩
    · by_cases same : decision = bobSilentSite true
      · subst decision
        exact (FinDist.uniformOfFintype (α := Bool)).map (silentHistory true)
      · exact FinDist.pure ⟨bobHistory true ((decision.1.getD none).getD false) true, by
          rcases target_bob_site_eq decision with equal | ⟨bit, equal⟩
          · exact (same equal).elim
          · subst decision; rfl⟩

theorem target_silent_belief (profile : Profile (model true).behavioralSignature) :
    (targetAssessment profile).belief true (bobSilentSite true) =
      (FinDist.uniformOfFintype (α := Bool)).map (silentHistory true) := by
  simp [targetAssessment]

def uniformReference : (model true).BehavioralAssessment := .ofStrategy fun who info =>
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (choose true who false info) (choose true who true info)

theorem uniformReference_full : uniformReference.IsFullyMixed := by
  intro who ⟨info, _⟩ ⟨value, legal⟩
  change (⟨value, legal⟩ : (model true).Choice who info) ∈
    (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (choose true who false info) (choose true who true info)).support
  simp only [choose]
  rw [FinDist.mem_support_mix_pure_iff _ _ _ (by norm_num) (by norm_num)]
  simp only [Subtype.mk.injEq]
  change value.isSome = decisionInfo true who info at legal
  simp only [decisionInfo, Bool.true_or, Bool.true_and] at legal ⊢
  cases info <;> cases value
  all_goals simp_all only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    Bool.true_eq_false, ite_true, ite_false]
  all_goals first | trivial | (rename_i value; cases value; simp)

def targetPerturb (guesses : FinDist Bool) (n : Nat) :
    Profile (model true).behavioralSignature :=
  (uniformReference.perturb (silentProfile guesses) (trembleWeight n)
    (trembleWeight_nonneg n) (trembleWeight_le_one n)).strategy

theorem targetPerturb_full (guesses : FinDist Bool) (n : Nat) :
    (targetAssessment (targetPerturb guesses n)).IsFullyMixed :=
  uniformReference.perturb_fullyMixed uniformReference_full (silentProfile guesses)
    (trembleWeight n) (trembleWeight_nonneg n) (trembleWeight_le_one n) (trembleWeight_pos n)

theorem target_reach_silent (guesses : FinDist Bool) (n : Nat) (bit : Bool) :
    (model true).historyReachProbability (targetPerturb guesses n) (bobHistory true bit false) =
      (1 - trembleWeight n / 2) / 2 := by
  classical
  change ((model true).runBehavioralFrom (targetPerturb guesses n) 2
    (arena true).initHistory).prob (bobHistory true bit false) = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model true)
      (single true),
    ← FinDist.prob_map_of_injective History.state (state_injective true), run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, FinDist.pure_bind,
    initHistory, kernel, FinDist.bind_map, FinDist.prob_bind]
  change (FinDist.uniformOfFintype (α := Bool)).expect (fun hidden =>
    ((choiceLaw (targetPerturb guesses n) false (some (some hidden))).map
      (fun disclose => State.bob hidden disclose)).prob (.bob bit false)) = _
  rw [FinDist.expect_eq_sum, Fintype.sum_bool]
  cases bit <;>
    simp [choiceLaw, targetPerturb, InformationModel.BehavioralAssessment.perturb,
      uniformReference, silentProfile, choose, decisionInfo, FinDist.map_mix,
      FinDist.prob_mix, FinDist.prob_uniformOfFintype, Fintype.card_bool,
      FinDist.prob_pure_eq_ite] <;> ring

theorem target_mass_silent (guesses : FinDist Bool) (n : Nat) :
    (model true).informationMass (targetPerturb guesses n) true (bobSilentSite true) =
      1 - trembleWeight n / 2 := by
  unfold InformationModel.informationMass
  rw [← (silentHistories true).sum_comp]
  change (∑ bit : Bool, (model true).historyReachProbability (targetPerturb guesses n)
    (bobHistory true bit false)) = _
  simp only [target_reach_silent, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    nsmul_eq_mul]
  ring

theorem target_belief_silent_prob (profile : Profile (model true).behavioralSignature)
    (bit : Bool) :
    ((targetAssessment profile).belief true (bobSilentSite true)).prob
      (silentHistory true bit) = 1 / 2 := by
  classical
  rw [target_silent_belief, FinDist.prob_map_of_injective _ (silentHistory_injective true)]
  norm_num [FinDist.prob_uniformOfFintype, Fintype.card_bool]

theorem targetPerturb_bayes (guesses : FinDist Bool) (n : Nat) :
    InformationModel.BehavioralAssessment.IsBayesConsistent (model true)
      (targetAssessment (targetPerturb guesses n)) (antichain true) := by
  intro who decision positive history
  cases who
  · obtain ⟨bit, rfl⟩ := alice_site_eq decision
    have equal : (targetAssessment (targetPerturb guesses n)).belief false (aliceSite bit) =
        (model true).bayesBelief (targetPerturb guesses n) false (aliceSite bit)
          (antichain true false (aliceSite bit)) positive := by
      exact (FinDist.eq_pure_of_subsingleton _ history).trans
        (FinDist.eq_pure_of_subsingleton _ history).symm
    rw [equal]
    exact InformationModel.bayesBelief_prob _ _ _ _ _ _ _
  · rcases target_bob_site_eq decision with rfl | ⟨bit, rfl⟩
    · obtain ⟨bit, same⟩ := history_at_silent true history
      have historyEq : history = silentHistory true bit := Subtype.ext same
      subst history
      change ((targetAssessment (targetPerturb guesses n)).belief true (bobSilentSite true)).prob
        (silentHistory true bit) =
          (model true).historyReachProbability (targetPerturb guesses n)
            (bobHistory true bit false) /
          (model true).informationMass (targetPerturb guesses n) true (bobSilentSite true)
      rw [target_belief_silent_prob, target_reach_silent, target_mass_silent]
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
        exact (FinDist.eq_pure_of_subsingleton _ history).trans
          (FinDist.eq_pure_of_subsingleton _ history).symm
      rw [equal]
      exact InformationModel.bayesBelief_prob _ _ _ _ _ _ _

theorem target_converges (guesses : FinDist Bool) :
    InformationModel.BehavioralAssessmentConvergesPointwise
      (fun n => targetAssessment (targetPerturb guesses n))
        (targetAssessment (silentProfile guesses)) := by
  constructor
  · intro who decision
    exact uniformReference.perturb_strategy_converges (silentProfile guesses) trembleWeight
      trembleWeight_nonneg trembleWeight_le_one trembleWeight_tendsto_zero who decision.1
  · intro who decision
    exact finDistConvergesPointwise_const _

theorem target_consistent (guesses : FinDist Bool) :
    (targetAssessment (silentProfile guesses)).IsSequentiallyConsistent (antichain true) :=
  ⟨fun n => targetAssessment (targetPerturb guesses n),
    fun n => ⟨targetPerturb_full guesses n, targetPerturb_bayes guesses n⟩,
    target_converges guesses⟩

end GameTheoryExtensionsTests.AmbientEnforcement
