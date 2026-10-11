/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLabelReach
import GameTheoryExtensions.Analysis.Protocol.ConsistentLikelihood

/-! # Bayes and limiting native beliefs along private-label history orbits -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeLabelBeliefs

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeService
open LateOpeningRuntimeLabelOrbits LateOpeningRuntimeLabelReach LateOpeningRuntimeLabelTrace

variable (horizon : Nat) (scheduler : app.Scheduler)
local notation "M" => rawMenu.information initial horizon scheduler
local notation "antichain" => rawMenu.decisionInformationAntichain initial horizon scheduler

theorem belief_permutation_of_bayes (permutation : Equiv.Perm (Fin 3))
    (assessment : (M).BehavioralAssessment)
    (uniformAlice : (assessment.strategy alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice))
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent (M) assessment antichain)
    (site : (M).InformationSite bob)
    (positive : 0 < (M).informationMass assessment.strategy bob site)
    (history : (M).InformationHistory bob site.1) :
    assessment.belief bob site
        (informationHistoryEquiv horizon scheduler permutation site history) =
      assessment.belief bob site history := by
  rw [bayes bob site positive, bayes bob site positive]
  exact congrArg (fun weight => weight / (M).informationMass assessment.strategy bob site)
    (historyReachWeight_permutation horizon scheduler permutation assessment.strategy
      uniformAlice history.1)

theorem belief_permutation_of_uniform_sequence (permutation : Equiv.Perm (Fin 3))
    (sequence : Nat → (M).BehavioralAssessment) (assessment : (M).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent (M)
      (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (uniformAlice : ∀ n, ((sequence n).strategy alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice))
    (site : (M).InformationSite bob) (history : (M).InformationHistory bob site.1) :
    assessment.belief bob site
        (informationHistoryEquiv horizon scheduler permutation site history) =
      assessment.belief bob site history := by
  have same : (fun n => (sequence n).belief bob site
      (informationHistoryEquiv horizon scheduler permutation site history)) =
      (fun n => (sequence n).belief bob site history) := by
    funext n
    exact belief_permutation_of_bayes horizon scheduler permutation (sequence n)
      (uniformAlice n) (bayes n) site
      ((M).informationMass_pos_of_fullSupport (sequence n).strategy (mixed n) bob site) history
  have permuted := converges.2 bob site
    (informationHistoryEquiv horizon scheduler permutation site history)
  rw [same] at permuted
  exact tendsto_nhds_unique permuted (converges.2 bob site history)


def historyLabel (history : (rawMenu.protocol initial horizon scheduler).History) : Fin 3 :=
  match history.state with
  | none => 0
  | some control => inputLabel control.execution.application.config.inputs

theorem informationHistory_label_permutation (permutation : Equiv.Perm (Fin 3))
    (site : (M).InformationSite bob) (history : (M).InformationHistory bob site.1) :
    historyLabel horizon scheduler
        (informationHistoryEquiv horizon scheduler permutation site history).1 =
      permutation (historyLabel horizon scheduler history.1) := by
  have active := InformationModel.InformationSite.active (M) site history
  cases controlEq : history.1.state with
  | none =>
      simp only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
        controlEq, Option.bind_none] at active
      cases active
  | some control =>
      change historyLabel horizon scheduler
        (permuteHistory horizon scheduler permutation history.1) = _
      unfold historyLabel permuteHistory permuteProtocolState
      simp only [controlEq, Option.map_some]
      exact inputLabel_permuted permutation control.execution.application.config.inputs

private theorem uniform_of_permutation_invariant (law : PMF (Fin 3))
    (invariant : ∀ permutation : Equiv.Perm (Fin 3), law.map permutation = law) :
    law = PMF.uniformOfFintype (Fin 3) := by
  have atoms (label : Fin 3) : law label = law 0 := by
    have mass := pmf_map_apply_of_injective law (Equiv.swap 0 label).injective 0
    rw [invariant, Equiv.swap_apply_left] at mass
    exact mass
  have total : (3 : ℝ) * (law 0).toReal = 1 := by
    simpa only [tsum_fintype, atoms, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using pmf_weight_tsum_one law
  ext label
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top law label)
    (PMF.apply_ne_top (PMF.uniformOfFintype (Fin 3)) label)).mp
  rw [atoms, PMF.uniformOfFintype_apply]
  norm_num
  linarith

theorem label_belief_uniform_of_uniform_sequence
    (sequence : Nat → (M).BehavioralAssessment) (assessment : (M).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent (M)
      (sequence n) antichain)
    (converges : BehavioralAssessmentConvergesPointwise sequence assessment)
    (uniformAlice : ∀ n, ((sequence n).strategy alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice)) (site : (M).InformationSite bob) :
    (assessment.belief bob site).map (fun history => historyLabel horizon scheduler history.1) =
      PMF.uniformOfFintype (Fin 3) := by
  apply uniform_of_permutation_invariant
  intro permutation
  have orbit : (assessment.belief bob site).map
      (informationHistoryEquiv horizon scheduler permutation site) =
      assessment.belief bob site := by
    ext history
    obtain ⟨before, rfl⟩ := (informationHistoryEquiv horizon scheduler permutation site).surjective
      history
    rw [pmf_map_apply_of_injective _
      (informationHistoryEquiv horizon scheduler permutation site).injective]
    exact (belief_permutation_of_uniform_sequence horizon scheduler permutation sequence assessment
      mixed bayes converges uniformAlice site before).symm
  have mapped := congrArg (PMF.map (fun history : (M).InformationHistory bob site.1 =>
    historyLabel horizon scheduler history.1)) orbit
  rw [PMF.map_comp] at mapped
  have commute : ((fun history : (M).InformationHistory bob site.1 =>
      historyLabel horizon scheduler history.1) ∘
      informationHistoryEquiv horizon scheduler permutation site) =
      permutation ∘ (fun history : (M).InformationHistory bob site.1 =>
        historyLabel horizon scheduler history.1) := by
    funext history
    exact informationHistory_label_permutation horizon scheduler permutation site history
  rw [commute, ← PMF.map_comp] at mapped
  exact mapped

end Vegas.Examples.LateOpeningRuntimeLabelBeliefs
