/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.DisclosureEnforcementInformation
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import Mathlib.Analysis.SpecificLimits.Basic
import GameTheoryExtensions.Math.Probability.Support

/-! # Common consistent beliefs for a private finite decision problem

The sender stays silent. Each private state uses the same disclosure tremble,
so silence retains exactly the original prior. Disclosure identifies the state.
One common sequence witnesses consistency at all sites, including disclosures.
-/

noncomputable section

namespace GameTheory.Protocol.DisclosureEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel

variable {Secret Decision : Type} [Nonempty Decision]
  (prior : PMF Secret) (full : ∀ secret, secret ∈ prior.support)

def receiverRespond (ambient : Bool) (decisions : PMF Decision) (response : Secret → Decision) :
    (model (Decision := Decision) prior ambient).BehavioralPolicy true := fun info =>
  match info with
  | some (some secret) => choose prior ambient true (response secret) (some (some secret))
  | some none => decisions.bind (fun decision => choose prior ambient true decision (some none))
  | none => choose prior ambient true (fallback true) none

def silentProfile (ambient : Bool) (decisions : PMF Decision) (response : Secret → Decision) :
    Profile (model (Decision := Decision) prior ambient).behavioralSignature
  | false => choose prior ambient false false
  | true => receiverRespond prior ambient decisions response

def beliefs (ambient : Bool) (who : Bool)
    (decision : (model (Decision := Decision) prior ambient).InformationSite who) :
    PMF ((model prior ambient).InformationHistory who decision.1) := by
    classical
    cases who
    · cases ambient
      · exact (source_no_sender_site prior decision).elim
      · exact PMF.pure ⟨senderHistory prior full true
          ((decision.1.getD none).getD prior.support_nonempty.choose), by
            obtain ⟨secret, rfl⟩ := sender_site_eq prior full decision
            rfl⟩
    · by_cases same : decision = receiverSilentSite prior full ambient
      · subst decision
        exact prior.map (silentHistory prior full ambient)
      · exact PMF.pure ⟨receiverHistory prior full ambient
          ((decision.1.getD none).getD prior.support_nonempty.choose) true, by
            rcases receiver_site_cases prior full ambient decision with equal | ⟨secret, rfl, equal⟩
            · exact (same equal).elim
            · change some (some ((decision.1.getD none).getD _)) = decision.1
              rw [equal]
              rfl⟩

def assessment (ambient : Bool)
    (profile : Profile (model (Decision := Decision) prior ambient).behavioralSignature) :
    (model (Decision := Decision) prior ambient).BehavioralAssessment :=
  ⟨profile, beliefs prior full ambient⟩

theorem silent_belief (ambient : Bool)
    (profile : Profile (model (Decision := Decision) prior ambient).behavioralSignature) :
    (assessment prior full ambient profile).belief true (receiverSilentSite prior full ambient) =
      prior.map (silentHistory prior full ambient) := by
  classical
  simp [assessment, beliefs]

private def trembleWeight (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)

private theorem trembleWeight_pos (n : Nat) : 0 < trembleWeight n := by
  unfold trembleWeight
  positivity

private theorem trembleWeight_nonneg (n : Nat) : 0 ≤ trembleWeight n :=
  (trembleWeight_pos n).le

private theorem trembleWeight_le_one (n : Nat) : trembleWeight n ≤ 1 := by
  unfold trembleWeight
  apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

private theorem trembleWeight_tendsto_zero : Tendsto trembleWeight atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable [Fintype Decision]

private def perturbProfile (ambient : Bool) (decisions : PMF Decision)
    (response : Secret → Decision)
    (n : Nat) : Profile (model (Decision := Decision) prior ambient).behavioralSignature :=
  ((reference prior ambient).perturb (silentProfile prior ambient decisions response)
    (trembleWeight n) (trembleWeight_nonneg n) (trembleWeight_le_one n)).strategy

private theorem perturb_full (ambient : Bool) (decisions : PMF Decision)
    (response : Secret → Decision)
    (n : Nat) :
    (assessment prior full ambient
      (perturbProfile prior ambient decisions response n)).IsFullyMixed :=
  (reference prior ambient).perturb_fullyMixed (reference_full prior ambient)
    (silentProfile prior ambient decisions response) (trembleWeight n)
    (trembleWeight_nonneg n) (trembleWeight_le_one n) (trembleWeight_pos n)

private theorem perturb_sender_law (decisions : PMF Decision) (response : Secret → Decision)
    (n : Nat) (secret : Secret) :
    choiceLaw (perturbProfile prior true decisions response n) false (some (some secret)) =
      mix (trembleWeight n) (trembleWeight_nonneg n) (trembleWeight_le_one n)
        (PMF.uniformOfFintype Bool) (PMF.pure false) := by
  simp only [choiceLaw, decisionInfo, Option.isSome_some, Set.mem_ofPred_eq, perturbProfile,
    BehavioralAssessment.perturb, reference, choose, Bool.true_or, Bool.true_and,
        pmf_bind_pure_eq_map,
    BehavioralAssessment.ofStrategy_strategy, silentProfile, ↓reduceIte, Bool.or_false,
        Bool.and_self,
    mix_map, PMF.pure_map, Option.getD_some]
  rw [PMF.map_comp]
  congr 1
  simp only [Function.comp_def, Option.getD_some]
  exact PMF.map_id _

private theorem perturb_source_sender_law (decisions : PMF Decision)
    (response : Secret → Decision)
    (n : Nat) (secret : Secret) :
    choiceLaw (perturbProfile prior false decisions response n) false (some (some secret)) =
      PMF.pure false := by
  simp only [choiceLaw, decisionInfo, Option.isSome_some, Set.mem_ofPred_eq, perturbProfile,
    BehavioralAssessment.perturb, reference, choose, Bool.false_or, Bool.and_eq_true,
    pmf_bind_pure_eq_map, BehavioralAssessment.ofStrategy_strategy, silentProfile,
    Bool.false_eq_true, and_true, ↓reduceIte, Bool.or_self, Bool.and_true, mix_map, PMF.pure_map,
    Option.getD_none]
  rw [PMF.map_comp]
  simp only [Function.comp_def, Option.getD_none, pmf_map_fun_const, mix_self]

/-- The weight the silent receiver history retains: all of it in the source, and
all but half the tremble when the sender may disclose. -/
private def silentWeight (ambient : Bool) (n : Nat) : ℝ :=
  if ambient then 1 - trembleWeight n / 2 else 1

private theorem silentWeight_pos (ambient : Bool) (n : Nat) : 0 < silentWeight ambient n := by
  unfold silentWeight
  cases ambient
  · norm_num
  · have := trembleWeight_le_one n
    simp only [↓reduceIte]
    linarith

private theorem reach_silent_toReal (ambient : Bool) (decisions : PMF Decision)
    (response : Secret → Decision)
    (n : Nat) (secret : Secret) :
    ((model prior ambient).historyReachWeight (perturbProfile prior ambient decisions response n)
      (receiverHistory prior full ambient secret false)).toReal =
      (prior secret).toReal * silentWeight ambient n := by
  classical
  change (((model prior ambient).runBehavioralFrom
    (perturbProfile prior ambient decisions response n) 2 (arena prior ambient).initHistory)
      (receiverHistory prior full ambient secret false)).toReal = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    (model prior ambient) (single prior ambient)]
  refine (congrArg ENNReal.toReal
    (pmf_map_apply_of_injective _ (state_injective prior full ambient) _)).symm.trans ?_
  rw [run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, PMF.pure_bind,
    initHistory, kernel, PMF.bind_map, Function.comp_def]
  have stateEq : (receiverHistory (Decision := Decision) prior full ambient secret false).state =
      .receiver secret false := by
    cases ambient <;> rfl
  rw [stateEq]
  change ((prior.bind fun hidden =>
    (choiceLaw (perturbProfile prior ambient decisions response n) false (some (some hidden))).map
      (fun disclose => State.receiver hidden (ambient && disclose)))
        (.receiver secret false)).toReal = _
  rw [bind_apply_of_unique_branch _ _ _ secret, ENNReal.toReal_mul]
  · congr 1
    cases ambient
    · rw [perturb_source_sender_law]
      simp [silentWeight]
    · rw [perturb_sender_law]
      simp only [Bool.true_and]
      refine (congrArg ENNReal.toReal (pmf_map_apply_of_injective _
        (f := fun disclose => State.receiver (Decision := Decision) secret disclose) (by
          intro first second same
          exact (State.receiver.inj same).2) false)).trans ?_
      rw [mix_apply_toReal, toReal_uniformOfFintype_apply, Fintype.card_bool, toReal_pure_apply]
      simp only [↓reduceIte, silentWeight]
      push_cast
      ring
  · intro hidden _ reached
    obtain ⟨disclose, _, same⟩ := PMF.support_map .. ▸ reached
    exact (State.receiver.inj same).1

private theorem reach_silent (ambient : Bool) (decisions : PMF Decision)
    (response : Secret → Decision)
    (n : Nat) (secret : Secret) :
    (model prior ambient).historyReachWeight (perturbProfile prior ambient decisions response n)
      (receiverHistory prior full ambient secret false) =
      prior secret * ENNReal.ofReal (silentWeight ambient n) := by
  have real := reach_silent_toReal prior full ambient decisions response n secret
  rw [← ENNReal.toReal_ofReal (silentWeight_pos ambient n).le, ← ENNReal.toReal_mul] at real
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top)).mp real

private theorem mass_silent (ambient : Bool) (decisions : PMF Decision)
    (response : Secret → Decision)
    (n : Nat) :
    (model prior ambient).informationMass (perturbProfile prior ambient decisions response n)
        true (receiverSilentSite prior full ambient) =
      ENNReal.ofReal (silentWeight ambient n) := by
  unfold InformationModel.informationMass
  refine ((silentHistories prior full ambient).tsum_eq _).symm.trans ?_
  simp only [silentHistories, Equiv.ofBijective_apply, silentHistory, reach_silent,
    ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Fintype Decision] in
theorem belief_silent_prob (ambient : Bool)
    (profile : Profile (model (Decision := Decision) prior ambient).behavioralSignature)
    (secret : Secret) :
    ((assessment prior full ambient profile).belief true
      (receiverSilentSite prior full ambient)) (silentHistory prior full ambient secret) =
        prior secret := by
  rw [silent_belief, pmf_map_apply_of_injective _ (silentHistory_injective prior full ambient)]

private theorem perturb_bayes (ambient : Bool) (decisions : PMF Decision)
    (response : Secret → Decision) (n : Nat) :
    BehavioralAssessment.IsBayesConsistent (model prior ambient)
      (assessment prior full ambient (perturbProfile prior ambient decisions response n))
        (antichain prior ambient) := by
  classical
  intro who decision positive history
  cases who
  · cases ambient
    · exact (source_no_sender_site prior decision).elim
    · obtain ⟨secret, rfl⟩ := sender_site_eq prior full decision
      have equal :
          (assessment prior full true (perturbProfile prior true decisions response n)).belief
              false (senderSite prior full secret) =
            (model prior true).bayesBelief (perturbProfile prior true decisions response n)
              false (senderSite prior full secret)
              (antichain prior true false (senderSite prior full secret)) positive :=
        (eq_pure_of_subsingleton _ history).trans
          (eq_pure_of_subsingleton _ history).symm
      rw [equal]
      exact InformationModel.bayesBelief_apply _ _ _ _ _ _ _
  · rcases receiver_site_cases prior full ambient decision with rfl | ⟨secret, rfl, same⟩
    · obtain ⟨secret, same⟩ := history_at_silent prior full ambient history
      have historyEq : history = silentHistory prior full ambient secret := Subtype.ext same
      subst history
      change ((assessment prior full ambient
        (perturbProfile prior ambient decisions response n)).belief true
          (receiverSilentSite prior full ambient)) (silentHistory prior full ambient secret) =
        (model prior ambient).historyReachWeight (perturbProfile prior ambient decisions response n)
            (receiverHistory prior full ambient secret false) /
          (model prior ambient).informationMass (perturbProfile prior ambient decisions response n)
            true (receiverSilentSite prior full ambient)
      rw [belief_silent_prob, reach_silent, mass_silent,
        ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr (silentWeight_pos ambient n)).ne'
          ENNReal.ofReal_ne_top]
    · have siteEq : decision = receiverDisclosedSite prior full secret := Subtype.ext same
      subst decision
      have equal :
          (assessment prior full true (perturbProfile prior true decisions response n)).belief
              true (receiverDisclosedSite prior full secret) =
            (model prior true).bayesBelief (perturbProfile prior true decisions response n)
              true (receiverDisclosedSite prior full secret)
              (antichain prior true true (receiverDisclosedSite prior full secret)) positive :=
        (eq_pure_of_subsingleton _ history).trans
          (eq_pure_of_subsingleton _ history).symm
      rw [equal]
      exact InformationModel.bayesBelief_apply _ _ _ _ _ _ _

private theorem converges (ambient : Bool) (decisions : PMF Decision)
    (response : Secret → Decision) :
    BehavioralAssessmentConvergesPointwise
      (fun n => assessment prior full ambient (perturbProfile prior ambient decisions response n))
      (assessment prior full ambient (silentProfile prior ambient decisions response)) := by
  constructor
  · intro who decision
    exact (reference prior ambient).perturb_strategy_converges
      (silentProfile prior ambient decisions response) trembleWeight
      trembleWeight_nonneg trembleWeight_le_one trembleWeight_tendsto_zero who decision.1
  · intro who decision
    exact pmfConvergesPointwise_const (beliefs prior full ambient who decision)

omit [Fintype Decision] in
theorem consistent [Finite Decision] (ambient : Bool) (decisions : PMF Decision)
    (response : Secret → Decision) :
    (assessment prior full ambient
      (silentProfile prior ambient decisions response)).IsSequentiallyConsistent
      (antichain prior ambient) := by
  classical
  let := Fintype.ofFinite Decision
  exact ⟨fun n => assessment prior full ambient (perturbProfile prior ambient decisions response n),
    fun n => ⟨perturb_full prior full ambient decisions response n,
      perturb_bayes prior full ambient decisions response n⟩,
    converges prior full ambient decisions response⟩

end GameTheory.Protocol.DisclosureEnforcement
