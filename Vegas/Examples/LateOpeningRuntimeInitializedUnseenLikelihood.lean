/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeInitializedTypeLikelihood
import Vegas.Examples.LateOpeningRuntimeUnseenLikelihood
import Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw

/-! # Initialized type weights at accepted unseen-opening observations

The observation fixes Bob's full empty earlier sample and current accepted
opening. Every initialized private label is counted at that same information
class, using the original prior and protected-silence probability.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeInitializedUnseenLikelihood

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeBindingPrefix LateOpeningRuntimeBindingObservation
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeUnseenLikelihood
  LateOpeningRuntimeInitializedTypeLikelihood

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem unseen_execution_ready (bit : Bool) (label : Fin 3) :
    (answerDecision bit label 0 false).application.config.cut.Ready bobBindEvent := by
  rw [answerDecision_physical]
  change bobBindEvent ∉ ({aliceEvent} : Finset nativeGraph.EventId) ∧
    nativeGraph.order.predecessors bobBindEvent ⊆ {aliceEvent}
  decide

theorem unseen_information_label (bit : Bool) (label otherLabel : Fin 3) :
    bobInformation (answerDecision bit label 0 false) =
      bobInformation (answerDecision bit otherLabel 0 false) :=
  answerDecision_first_label_info bit label otherLabel false

def typedUnseenEvent (bit : Bool) (representativeLabel label : Fin 3) :
    Set app.ProtocolState :=
  typedInformationEvent (bobInformation (answerDecision bit representativeLabel 0 false)) bit label

variable (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1) (bit : Bool) (representativeLabel : Fin 3)
  (current : representative.1.state =
    some ⟨14, some bob, answerDecision bit representativeLabel 0 false⟩)

include current in
theorem initialized_unseen_probability (profile : Profile weight nonnegative) (label : Fin 3) :
    ((bindingPrefix weight nonnegative profile).toOuterMeasure
      (typedUnseenEvent bit representativeLabel label)).toReal =
        typeWeight weight nonnegative profile bit label *
          ((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (unseenEvent bit label)).toReal := by
  have member : bobObservationRecord bit representativeLabel false ∈
      (answerDecision bit representativeLabel 0 false).recall bob := by
    rw [answerDecision_bobRecall, bobObserved_first_recall]
    exact List.mem_singleton.mpr rfl
  have extraction := initialized_information_probability weight nonnegative site representative
    (answerDecision bit representativeLabel 0 false) current
      (bobObservationRecord bit representativeLabel false) member
        (by change 0 < 1; decide) rfl profile bit label
  simpa only [typedUnseenEvent, unseenEvent,
    unseen_information_label bit representativeLabel label] using extraction

include current in
theorem initialized_unseen_error (profile : Profile weight nonnegative) (label : Fin 3)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (retryBound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error)
    (openingBound : ∀ actual :
        LateOpeningRuntimeAliceOpeningTremble.EmptyOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceOpeningTremble.nongenuineProbability
        weight nonnegative profile actual ≤ error)
    (firstBound : ∀ actual :
        LateOpeningRuntimeAliceFirstTremble.FirstOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceFirstTremble.nongenuineProbability
        weight nonnegative profile actual ≤ error) :
    |((bindingPrefix weight nonnegative profile).toOuterMeasure
        (typedUnseenEvent bit representativeLabel label)).toReal -
      typeWeight weight nonnegative profile bit label *
        (1 - genuineProbability weight nonnegative profile bit label / 2) *
          earlySilenceProbability weight nonnegative profile bit label *
            inclusionProbability weight| ≤
      2 * error * typeWeight weight nonnegative profile bit label := by
  rw [initialized_unseen_probability weight nonnegative site representative
    bit representativeLabel current profile label]
  have difference :
      typeWeight weight nonnegative profile bit label *
          ((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (unseenEvent bit label)).toReal -
        typeWeight weight nonnegative profile bit label *
          (1 - genuineProbability weight nonnegative profile bit label / 2) *
            earlySilenceProbability weight nonnegative profile bit label *
              inclusionProbability weight =
      typeWeight weight nonnegative profile bit label *
        (((originalLaw weight nonnegative profile bit label).toOuterMeasure
            (unseenEvent bit label)).toReal -
          (1 - genuineProbability weight nonnegative profile bit label / 2) *
            earlySilenceProbability weight nonnegative profile bit label *
              inclusionProbability weight) := by ring
  rw [difference, abs_mul, abs_of_nonneg (typeWeight_nonnegative weight nonnegative
    profile bit label)]
  have close := original_unseen_error weight nonnegative profile bit label
    error errorNonnegative retryBound openingBound
      (first_nongenuine_probability_le weight nonnegative profile bit label error firstBound)
  calc
    _ ≤ typeWeight weight nonnegative profile bit label * (2 * error) :=
      mul_le_mul_of_nonneg_left close
        (typeWeight_nonnegative weight nonnegative profile bit label)
    _ = _ := by ring

include current in
/-- This bound counts every actual hidden raw history of the chosen initialized
label at the fixed full receiver-information class. -/
theorem initialized_history_unseen_error (profile : Profile weight nonnegative) (label : Fin 3)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (retryBound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error)
    (openingBound : ∀ actual :
        LateOpeningRuntimeAliceOpeningTremble.EmptyOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceOpeningTremble.nongenuineProbability
        weight nonnegative profile actual ≤ error)
    (firstBound : ∀ actual :
        LateOpeningRuntimeAliceFirstTremble.FirstOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceFirstTremble.nongenuineProbability
        weight nonnegative profile actual ≤ error) :
    |InformationModel.finiteHistoryReach profile bob site
        (readoutHistories weight nonnegative site initializedInputs
          (some (setup.eventInputs (sourceInitial bit label)))) -
      typeWeight weight nonnegative profile bit label *
        (1 - genuineProbability weight nonnegative profile bit label / 2) *
          earlySilenceProbability weight nonnegative profile bit label *
            inclusionProbability weight| ≤
      2 * error * typeWeight weight nonnegative profile bit label := by
  rw [initialized_type_reach_eq_prefix weight nonnegative site representative
    (answerDecision bit representativeLabel 0 false) current
      (unseen_execution_ready bit representativeLabel),
    LateOpeningRuntimeInitializedTypeLikelihood.site_information weight nonnegative site
      representative (answerDecision bit representativeLabel 0 false) current]
  exact initialized_unseen_error weight nonnegative site representative bit representativeLabel
    current profile label error errorNonnegative retryBound openingBound firstBound

/-- The original early receiver silence atom converges at the actual empty
sample information site along the same assessment sequence. -/
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
  obtain ⟨actual, history, observedState⟩ :=
    LateOpeningRuntimeEarlyResponseLaw.information_representative
      weight nonnegative bit label 0 false (Or.inr rfl)
  have information := history.2
  change (rawMenu.signals initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf bob
      history.1.trace = actual.1 at information
  rw [rawMenu.info, observedState] at information
  have observed : actual.1 = some
      ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 false).recall bob,
        (LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 false).observe app bob) :=
    information.symm
  have decoded : PMFConvergesPointwise (fun n =>
      players weight nonnegative (sequence n).strategy bob
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 false).recall bob)
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 false).observe app bob))
      (players weight nonnegative assessment.strategy bob
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 false).recall bob)
        ((LateOpeningRuntimeEarlyResponseLaw.observed bit label 0 false).observe app bob)) := by
    have limit := (converges.strategy bob actual).map (fun choice => choice.1.getD ⟨none⟩)
    simp only [players, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def]
    rw [← observed]
    exact limit
  have limit := decoded.toReal (⟨none⟩ : app.Action)
  have silent := LateOpeningRuntimeEarlyResponseLaw.sequentially_rational_response_law
    weight nonnegative reward forfeit deposit forfeitNonnegative collateral
      assessment rational bit label 0 false (Or.inr rfl)
  rw [silent, PMF.pure_apply_self, ENNReal.toReal_one] at limit
  simpa only [earlySilenceProbability, LateOpeningRuntimeEarlyResponseLaw.observed,
    Bool.false_eq_true, ↓reduceIte] using limit

end Vegas.Examples.LateOpeningRuntimeInitializedUnseenLikelihood
