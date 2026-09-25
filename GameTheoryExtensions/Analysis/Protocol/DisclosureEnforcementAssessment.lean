/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.DisclosureEnforcementInformation
import GameTheoryExtensions.Math.Probability.FinDist
import Mathlib.Analysis.SpecificLimits.Basic

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
  (prior : FinDist Secret) (full : ∀ secret, secret ∈ prior.support)

def receiverRespond (ambient : Bool) (decisions : FinDist Decision) (response : Secret → Decision) :
    (model (Decision := Decision) prior ambient).BehavioralPolicy true := fun info =>
  match info with
  | some (some secret) => choose prior ambient true (response secret) (some (some secret))
  | some none => decisions.bind (fun decision => choose prior ambient true decision (some none))
  | none => choose prior ambient true (fallback true) none

def silentProfile (ambient : Bool) (decisions : FinDist Decision) (response : Secret → Decision) :
    Profile (model (Decision := Decision) prior ambient).behavioralSignature
  | false => choose prior ambient false false
  | true => receiverRespond prior ambient decisions response

def beliefs (ambient : Bool) (who : Bool)
    (decision : (model (Decision := Decision) prior ambient).InformationSite who) :
    FinDist ((model prior ambient).InformationHistory who decision.1) := by
    classical
    cases who
    · cases ambient
      · exact (source_no_sender_site prior decision).elim
      · exact FinDist.pure ⟨senderHistory prior full true
          ((decision.1.getD none).getD prior.support_nonempty.choose), by
            obtain ⟨secret, rfl⟩ := sender_site_eq prior full decision
            rfl⟩
    · by_cases same : decision = receiverSilentSite prior full ambient
      · subst decision
        exact prior.map (silentHistory prior full ambient)
      · exact FinDist.pure ⟨receiverHistory prior full ambient
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

private def perturbProfile (ambient : Bool) (decisions : FinDist Decision)
    (response : Secret → Decision)
    (n : Nat) : Profile (model (Decision := Decision) prior ambient).behavioralSignature :=
  ((reference prior ambient).perturb (silentProfile prior ambient decisions response)
    (trembleWeight n) (trembleWeight_nonneg n) (trembleWeight_le_one n)).strategy

private theorem perturb_full (ambient : Bool) (decisions : FinDist Decision)
    (response : Secret → Decision)
    (n : Nat) :
    (assessment prior full ambient
      (perturbProfile prior ambient decisions response n)).IsFullyMixed :=
  (reference prior ambient).perturb_fullyMixed (reference_full prior ambient)
    (silentProfile prior ambient decisions response) (trembleWeight n)
    (trembleWeight_nonneg n) (trembleWeight_le_one n) (trembleWeight_pos n)

private theorem perturb_sender_law (decisions : FinDist Decision) (response : Secret → Decision)
    (n : Nat) (secret : Secret) :
    choiceLaw (perturbProfile prior true decisions response n) false (some (some secret)) =
      FinDist.mix (trembleWeight n) (trembleWeight_nonneg n) (trembleWeight_le_one n)
        (FinDist.uniformOfFintype (α := Bool)) (FinDist.pure false) := by
  simp [choiceLaw, perturbProfile, BehavioralAssessment.perturb, reference, silentProfile,
    choose, decisionInfo, FinDist.map_mix, FinDist.map_bind]

private theorem perturb_source_sender_law (decisions : FinDist Decision)
    (response : Secret → Decision)
    (n : Nat) (secret : Secret) :
    choiceLaw (perturbProfile prior false decisions response n) false (some (some secret)) =
      FinDist.pure false := by
  simp [choiceLaw, perturbProfile, BehavioralAssessment.perturb, reference, silentProfile,
    choose, decisionInfo, FinDist.map_mix, FinDist.map_bind]

private theorem reach_silent (ambient : Bool) (decisions : FinDist Decision)
    (response : Secret → Decision)
    (n : Nat) (secret : Secret) :
    (model prior ambient).historyReachProbability
        (perturbProfile prior ambient decisions response n)
        (receiverHistory prior full ambient secret false) =
      prior.prob secret * (if ambient then 1 - trembleWeight n / 2 else 1) := by
  classical
  change ((model prior ambient).runBehavioralFrom
    (perturbProfile prior ambient decisions response n) 2 (arena prior ambient).initHistory).prob
      (receiverHistory prior full ambient secret false) = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    (model prior ambient) (single prior ambient),
    ← FinDist.prob_map_of_injective History.state (state_injective prior full ambient), run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, FinDist.pure_bind,
    initHistory, kernel, FinDist.bind_map]
  have stateEq : (receiverHistory (Decision := Decision) prior full ambient secret false).state =
      .receiver secret false := by
    cases ambient <;> rfl
  rw [stateEq]
  change (prior.bind fun hidden =>
    (choiceLaw (perturbProfile prior ambient decisions response n) false (some (some hidden))).map
      (fun disclose => State.receiver hidden (ambient && disclose))).prob
        (.receiver secret false) = _
  rw [FinDist.prob_bind_of_unique_branch _ _ _ secret]
  · congr 1
    cases ambient
    · rw [perturb_source_sender_law]
      simp
    · rw [perturb_sender_law]
      simp only [Bool.true_and, ↓reduceIte]
      rw [FinDist.prob_map_of_injective
        (fun disclose => State.receiver (Decision := Decision) secret disclose) (by
          intro first second same
          exact (State.receiver.inj same).2)]
      simp [FinDist.prob_mix, FinDist.prob_uniformOfFintype, Fintype.card_bool]
      ring
  · intro hidden _ reached
    obtain ⟨disclose, _, same⟩ := FinDist.support_map .. ▸ reached
    exact (State.receiver.inj same).1

private theorem mass_silent (ambient : Bool) (decisions : FinDist Decision)
    (response : Secret → Decision)
    (n : Nat) :
    (model prior ambient).informationMass (perturbProfile prior ambient decisions response n)
        true (receiverSilentSite prior full ambient) =
      if ambient then 1 - trembleWeight n / 2 else 1 := by
  classical
  let : Fintype Secret := Fintype.ofEquiv
    ((model (Decision := Decision) prior ambient).InformationHistory true
      (receiverSilentSite prior full ambient).1) (silentHistories prior full ambient).symm
  unfold InformationModel.informationMass
  rw [← (silentHistories prior full ambient).sum_comp]
  simp only [silentHistories, Equiv.ofBijective_apply, silentHistory, reach_silent]
  rw [← Finset.sum_mul, FinDist.sum_prob, one_mul]

omit [Fintype Decision] in
theorem belief_silent_prob (ambient : Bool)
    (profile : Profile (model (Decision := Decision) prior ambient).behavioralSignature)
    (secret : Secret) :
    ((assessment prior full ambient profile).belief true
      (receiverSilentSite prior full ambient)).prob
      (silentHistory prior full ambient secret) = prior.prob secret := by
  classical
  rw [silent_belief, FinDist.prob_map_of_injective _
    (silentHistory_injective prior full ambient)]

private theorem perturb_bayes (ambient : Bool) (decisions : FinDist Decision)
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
        (FinDist.eq_pure_of_subsingleton _ history).trans
          (FinDist.eq_pure_of_subsingleton _ history).symm
      rw [equal]
      exact InformationModel.bayesBelief_prob _ _ _ _ _ _ _
  · rcases receiver_site_cases prior full ambient decision with rfl | ⟨secret, rfl, same⟩
    · obtain ⟨secret, same⟩ := history_at_silent prior full ambient history
      have historyEq : history = silentHistory prior full ambient secret := Subtype.ext same
      subst history
      change ((assessment prior full ambient
        (perturbProfile prior ambient decisions response n)).belief true
          (receiverSilentSite prior full ambient)).prob (silentHistory prior full ambient secret) =
        (model prior ambient).historyReachProbability
            (perturbProfile prior ambient decisions response n)
            (receiverHistory prior full ambient secret false) /
          (model prior ambient).informationMass (perturbProfile prior ambient decisions response n)
            true (receiverSilentSite prior full ambient)
      rw [belief_silent_prob, reach_silent, mass_silent]
      have positiveWeight : (if ambient then 1 - trembleWeight n / 2 else 1) ≠ 0 := by
        cases ambient
        · norm_num
        · have := trembleWeight_le_one n
          simp only [↓reduceIte]
          linarith
      rw [mul_div_cancel_right₀ _ positiveWeight]
    · have siteEq : decision = receiverDisclosedSite prior full secret := Subtype.ext same
      subst decision
      have equal :
          (assessment prior full true (perturbProfile prior true decisions response n)).belief
              true (receiverDisclosedSite prior full secret) =
            (model prior true).bayesBelief (perturbProfile prior true decisions response n)
              true (receiverDisclosedSite prior full secret)
              (antichain prior true true (receiverDisclosedSite prior full secret)) positive :=
        (FinDist.eq_pure_of_subsingleton _ history).trans
          (FinDist.eq_pure_of_subsingleton _ history).symm
      rw [equal]
      exact InformationModel.bayesBelief_prob _ _ _ _ _ _ _

private theorem converges (ambient : Bool) (decisions : FinDist Decision)
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
    exact finDistConvergesPointwise_const (beliefs prior full ambient who decision)

omit [Fintype Decision] in
theorem consistent [Finite Decision] (ambient : Bool) (decisions : FinDist Decision)
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
