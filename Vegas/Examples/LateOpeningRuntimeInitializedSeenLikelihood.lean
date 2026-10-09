/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSeenLikelihood
import Vegas.Examples.LateOpeningRuntimeInitializedTypeLikelihood
import Vegas.Examples.LateOpeningRuntimeBindingObservationWitness
import Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw

/-! # Initialized type weights in complete native seen-information groups

A fixed complete receiver-information class is filtered by each immutable
initialized label separately. Its type weight retains the original prior
and protected-silence atom; no representative's private label is exposed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLatePrefixKernel
  LateOpeningRuntimeBindingPrefix LateOpeningRuntimeFirstRetryComparison
  LateOpeningRuntimeSeenLikelihood LateOpeningRuntimeInitializedTypeLikelihood
open Filter

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem seen_execution_ready (bit : Bool) (label : Fin 3) (accepted : Bool) :
    (seenExecution bit label accepted).application.config.cut.Ready bobBindEvent := by
  cases accepted
  · exact LateOpeningRuntimeBindingObservation.failedAnswerDecision_binding_ready
      bit label 0 true false
  · simp only [seenExecution, ↓reduceIte]
    rw [LateOpeningRuntimeLateAcceptance.answerDecision_physical]
    change bobBindEvent ∉ ({aliceEvent} : Finset nativeGraph.EventId) ∧
      nativeGraph.order.predecessors bobBindEvent ⊆ {aliceEvent}
    decide

theorem seen_information_label (bit : Bool) (label otherLabel : Fin 3) (accepted : Bool) :
    LateOpeningRuntimeBindingObservation.bobInformation (seenExecution bit label accepted) =
      LateOpeningRuntimeBindingObservation.bobInformation
        (seenExecution bit otherLabel accepted) := by
  cases accepted
  · exact LateOpeningRuntimeBindingObservation.failed_information_label
      bit label otherLabel 0 true false
  · exact LateOpeningRuntimeLateAcceptance.answerDecision_first_label_info
      bit label otherLabel true

def typedSeenEvent (bit : Bool) (representativeLabel label : Fin 3) (accepted : Bool) :
    Set app.ProtocolState :=
  typedInformationEvent (LateOpeningRuntimeBindingObservation.bobInformation
    (seenExecution bit representativeLabel accepted)) bit label

variable (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1) (bit : Bool) (representativeLabel : Fin 3) (accepted : Bool)
  (current : representative.1.state =
    some ⟨14, some bob, seenExecution bit representativeLabel accepted⟩)

include current in
/-- Every initialized label is counted at this one fixed full information class. -/
theorem initialized_seen_probability (profile : Profile weight nonnegative) (label : Fin 3) :
    ((bindingPrefix weight nonnegative profile).toOuterMeasure
      (typedSeenEvent bit representativeLabel label accepted)).toReal =
        typeWeight weight nonnegative profile bit label *
          ((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (seenEvent bit label accepted)).toReal := by
  have member : bobObservationRecord bit representativeLabel true ∈
      (seenExecution bit representativeLabel accepted).recall bob := by
    rw [seen_execution_recall]
    exact List.mem_singleton.mpr rfl
  have extraction := initialized_information_probability weight nonnegative site representative
    (seenExecution bit representativeLabel accepted) current
      (bobObservationRecord bit representativeLabel true) member
        (by change 0 < 1; decide) rfl profile bit label
  simpa only [typedSeenEvent, seenEvent,
    seen_information_label bit representativeLabel label accepted] using extraction

include current in
theorem initialized_seen_error (profile : Profile weight nonnegative) (label : Fin 3)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error) :
    |((bindingPrefix weight nonnegative profile).toOuterMeasure
        (typedSeenEvent bit representativeLabel label accepted)).toReal -
      typeWeight weight nonnegative profile bit label *
        genuineProbability weight nonnegative profile bit label *
          earlySilenceProbability weight nonnegative profile bit label *
            settlementProbability weight accepted / 2| ≤
      error * typeWeight weight nonnegative profile bit label *
        genuineProbability weight nonnegative profile bit label := by
  rw [initialized_seen_probability weight nonnegative site representative
    bit representativeLabel accepted current profile label]
  have difference :
      typeWeight weight nonnegative profile bit label *
          ((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (seenEvent bit label accepted)).toReal -
        typeWeight weight nonnegative profile bit label *
          genuineProbability weight nonnegative profile bit label *
            earlySilenceProbability weight nonnegative profile bit label *
              settlementProbability weight accepted / 2 =
      typeWeight weight nonnegative profile bit label *
        (((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (seenEvent bit label accepted)).toReal -
          genuineProbability weight nonnegative profile bit label *
            earlySilenceProbability weight nonnegative profile bit label *
              settlementProbability weight accepted / 2) := by ring
  rw [difference, abs_mul, abs_of_nonneg (typeWeight_nonnegative weight nonnegative
    profile bit label)]
  have close := original_seen_error weight nonnegative profile bit label accepted
    error errorNonnegative bound
  calc
    _ ≤ typeWeight weight nonnegative profile bit label *
        (error * genuineProbability weight nonnegative profile bit label) :=
      mul_le_mul_of_nonneg_left close
        (typeWeight_nonnegative weight nonnegative profile bit label)
    _ = _ := by ring

include current in
/-- All actual raw histories of each initialized label in the same receiver
class are counted, including all private packet aliases. -/
theorem initialized_history_seen_error (profile : Profile weight nonnegative) (label : Fin 3)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error) :
    |InformationModel.finiteHistoryReach profile bob site
        (readoutHistories weight nonnegative site initializedInputs
          (some (setup.eventInputs (sourceInitial bit label)))) -
      typeWeight weight nonnegative profile bit label *
        genuineProbability weight nonnegative profile bit label *
          earlySilenceProbability weight nonnegative profile bit label *
            settlementProbability weight accepted / 2| ≤
      error * typeWeight weight nonnegative profile bit label *
        genuineProbability weight nonnegative profile bit label := by
  rw [initialized_type_reach_eq_prefix weight nonnegative site representative
    (seenExecution bit representativeLabel accepted) current
      (seen_execution_ready bit representativeLabel accepted),
    LateOpeningRuntimeInitializedTypeLikelihood.site_information weight nonnegative site
      representative (seenExecution bit representativeLabel accepted) current]
  exact initialized_seen_error weight nonnegative site representative bit representativeLabel
    accepted current profile label error errorNonnegative bound

/-- Both canonical retained-opening observations are actual native information
classes, constructed from admitted initialized raw histories. -/
theorem exists_seen_representative (positive : 0 < weight) (bit : Bool) (label : Fin 3)
    (accepted : Bool) :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        bob site.1),
      representative.1.state = some ⟨14, some bob, seenExecution bit label accepted⟩ := by
  cases accepted
  · obtain ⟨site, representative, current, _⟩ :=
      LateOpeningRuntimeBindingObservationWitness.failed_information_representative
        weight nonnegative bit label 0 true false (Or.inl rfl)
    exact ⟨site, representative, current⟩
  · obtain ⟨trace⟩ := LateOpeningRuntimeLateHistories.answerDecision_trace
      weight nonnegative positive bit label 0 true (Or.inl rfl)
    let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
      ⟨some ⟨14, some bob, LateOpeningRuntimeLateAcceptance.answerDecision bit label 0 true⟩,
        trace⟩
    have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
      change ¬ (14 = 0 ∧ some bob = none)
      simp
    obtain ⟨site, same⟩ :=
      (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
        bob history running rfl
    exact ⟨site, ⟨history, same.symm⟩, rfl⟩

/-- The original early receiver atom converges to one at the actual legal
seen-opening information class along the same assessment sequence. -/
theorem early_silence_tendsto
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment)
    (bit : Bool) (label : Fin 3) :
    Tendsto (fun n => earlySilenceProbability weight nonnegative (sequence n).strategy bit label)
      atTop (nhds 1) := by
  obtain ⟨site, history, current⟩ :=
    LateOpeningRuntimeEarlyResponseLaw.information_representative
      weight nonnegative bit label 0 true (Or.inl rfl)
  have information := history.2
  change (rawMenu.signals initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf bob
      history.1.trace = site.1 at information
  rw [rawMenu.info, current] at information
  have observed : site.1 = some
      ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).recall bob,
        (LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).observe app bob) :=
    information.symm
  have decoded : PMFConvergesPointwise (fun n =>
      players weight nonnegative (sequence n).strategy bob
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).recall bob)
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).observe app bob))
      (players weight nonnegative assessment.strategy bob
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).recall bob)
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 true).observe app bob)) := by
    have limit := (converges.strategy bob site).map (fun choice => choice.1.getD ⟨none⟩)
    simp only [players, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def]
    rw [← observed]
    exact limit
  have limit := decoded.toReal (⟨none⟩ : app.Action)
  have silent := LateOpeningRuntimeEarlyResponseLaw.sequentially_rational_response_law
    weight nonnegative reward forfeit deposit forfeitNonnegative collateral
      assessment rational bit label 0 true (Or.inl rfl)
  rw [silent, PMF.pure_apply_self, ENNReal.toReal_one] at limit
  simpa only [earlySilenceProbability, LateOpeningRuntimeEarlyResponseLaw.observed,
    ↓reduceIte] using limit

end Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood
