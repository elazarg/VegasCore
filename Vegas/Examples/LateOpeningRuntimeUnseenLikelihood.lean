/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSeenLikelihood
import Vegas.Examples.LateOpeningRuntimeAliceOpeningTremble
import Vegas.Examples.LateOpeningRuntimeAliceFirstTremble

/-! # Actual acceptance after the earlier receiver sample was empty

The first-silence branch retains its original final response lottery. Every
genuine final private alias gives the same complete receiver-information law
as the canonical final opening. Nongenuine responses contribute at most their
actual native probability. The first-genuine branch retains the original early
receiver silence atom and the original fair missed-sample factor.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeUnseenLikelihood

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeLatePrefixKernel
  LateOpeningRuntimeLateResponseKernel LateOpeningRuntimeBindingObservation
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeFirstObservation
  LateOpeningRuntimeBobBindingService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def firstSilenceProbability (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3) :
    ℝ := (firstResponses weight nonnegative profile bit label ⟨none⟩).toReal

def firstNongenuineProbability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) : ℝ :=
  ((firstResponses weight nonnegative profile bit label).toOuterMeasure
    {response | ¬ LateOpeningRuntimeAliceFirstResponse.PermittedResponse
      weight nonnegative (LateOpeningRuntimeAliceFirstWitness.decisionHistory
        weight nonnegative bit label) response}).toReal

/-- The actual initialized first callback is one of the uniform native sites. -/
theorem first_nongenuine_probability_le (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (error : ℝ)
    (bound : ∀ actual : LateOpeningRuntimeAliceFirstTremble.FirstOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceFirstTremble.nongenuineProbability
        weight nonnegative profile actual ≤ error) :
    firstNongenuineProbability weight nonnegative profile bit label ≤ error := by
  let decision := LateOpeningRuntimeAliceFirstWitness.decisionHistory
    weight nonnegative bit label
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨22, some alice, decision.execution⟩,
      (LateOpeningRuntimeAliceFirstWitness.firstLateDecision_trace
        weight nonnegative bit label).some⟩
  obtain ⟨site, information⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      alice history (by change ¬ (22 = 0 ∧ some alice = none); simp) rfl
  let representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1 := ⟨history, information.symm⟩
  let actual : LateOpeningRuntimeAliceFirstTremble.FirstOpeningSite weight nonnegative :=
    ⟨site, decision, representative, rfl⟩
  have info := LateOpeningRuntimeAliceFirstResponse.site_information weight nonnegative site
    representative decision rfl
  have decoded : LateOpeningRuntimeAliceFirstResponse.responseLaw weight nonnegative
      site (profile alice site.1) = firstResponses weight nonnegative profile bit label := by
    unfold LateOpeningRuntimeAliceFirstResponse.responseLaw
    rw [info]
    simp only [firstResponses, players, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def,
      decision, LateOpeningRuntimeAliceFirstWitness.decisionHistory]
  have probability := LateOpeningRuntimeAliceFirstTremble.nongenuineProbability_of_representative
    weight nonnegative profile actual decision representative rfl
  rw [decoded] at probability
  change ((firstResponses weight nonnegative profile bit label).toOuterMeasure
    {response | ¬ LateOpeningRuntimeAliceFirstResponse.PermittedResponse
      weight nonnegative decision response}).toReal ≤ error
  rw [← probability]
  exact bound actual

/-- The complete first raw response law is partitioned into genuine private
aliases, silence, and all remaining packets. -/
theorem first_response_partition (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) :
    genuineProbability weight nonnegative profile bit label +
      firstSilenceProbability weight nonnegative profile bit label +
        firstNongenuineProbability weight nonnegative profile bit label = 1 := by
  classical
  let decision := LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label
  let responses := firstResponses weight nonnegative profile bit label
  let genuine : app.Action → ℝ := fun response =>
    if GenuineResponse weight nonnegative decision response then 1 else 0
  let silent : app.Action → ℝ := fun response => if (⟨none⟩ : app.Action) = response then 1 else 0
  let nongenuine : app.Action → ℝ := fun response =>
    if ¬ LateOpeningRuntimeAliceFirstResponse.PermittedResponse
      weight nonnegative decision response then 1 else 0
  have genuineIntegrable : PayoffIntegrable responses genuine :=
    payoffIntegrable_ite_one_zero responses (GenuineResponse weight nonnegative decision)
  have silentIntegrable : PayoffIntegrable responses silent :=
    payoffIntegrable_ite_one_zero responses (fun response => (⟨none⟩ : app.Action) = response)
  have nongenuineIntegrable : PayoffIntegrable responses nongenuine :=
    payoffIntegrable_ite_one_zero responses
    (fun response => ¬ LateOpeningRuntimeAliceFirstResponse.PermittedResponse
      weight nonnegative decision response)
  have genuineExpectation : expect responses genuine =
      genuineProbability weight nonnegative profile bit label := by
    change expect responses (fun response => if response ∈
      {response | GenuineResponse weight nonnegative decision response} then 1 else 0) = _
    rw [expect_indicator]
    rfl
  have silentExpectation : expect responses silent =
      firstSilenceProbability weight nonnegative profile bit label := by
    dsimp only [silent]
    rw [expect_ite_eq, mul_one]
    rfl
  have nongenuineExpectation : expect responses nongenuine =
      firstNongenuineProbability weight nonnegative profile bit label := by
    calc
      _ = expect responses (fun response => @ite ℝ
          (response ∈ {response | ¬ LateOpeningRuntimeAliceFirstResponse.PermittedResponse
            weight nonnegative decision response}) (Classical.propDecidable _) 1 0) := by
        apply expect_congr_on_support
        intro response _
        by_cases permitted : LateOpeningRuntimeAliceFirstResponse.PermittedResponse
            weight nonnegative decision response <;> simp [nongenuine, permitted]
      _ = _ := by
        rw [expect_indicator]
        rfl
  calc
    _ = expect responses (fun response =>
        genuine response + silent response + nongenuine response) := by
      rw [expect_add (payoffIntegrable_add genuineIntegrable silentIntegrable)
        nongenuineIntegrable, expect_add genuineIntegrable silentIntegrable]
      rw [genuineExpectation, silentExpectation, nongenuineExpectation]
    _ = 1 := by
      rw [← expect_constant responses 1]
      apply expect_congr_on_support
      rintro ⟨transmission⟩ _
      cases transmission with
      | none => simp [genuine, silent, nongenuine, GenuineResponse,
          LateOpeningRuntimeAliceFirstResponse.PermittedResponse]
      | some submission =>
          by_cases emitted : LateOpeningRuntimeAliceFirstDecision.EmitsOpening
              weight nonnegative decision submission
          all_goals simp [genuine, silent, nongenuine, GenuineResponse,
            LateOpeningRuntimeAliceFirstResponse.PermittedResponse, emitted]

def unseenEvent (bit : Bool) (label : Fin 3) : Set app.Execution :=
  {final | bobInformation final = bobInformation (answerDecision bit label 0 false)}

def earlySilenceProbability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) : ℝ :=
  let observed := (beforeBob bit label 0).sampledActivation app bob ∅
  (players weight nonnegative profile bob (observed.recall bob)
    (observed.observe app bob) ⟨none⟩).toReal

theorem empty_early_information (bit otherBit : Bool) (label otherLabel : Fin 3)
    (slot otherSlot : Fin 2) :
    bobInformation ((beforeBob bit label slot).sampledActivation app bob ∅) =
      bobInformation ((beforeBob otherBit otherLabel otherSlot).sampledActivation app bob ∅) := by
  simpa only [bobInformation, ReactiveApplication.Execution.sampledActivation,
    MessageNetwork.learn_empty, ReactiveApplication.Execution.observe] using
      beforeBob_info bit otherBit label otherLabel slot otherSlot

theorem unseen_event_quiet (bit : Bool) (label : Fin 3) :
    ∀ final ∈ unseenEvent bit label, SilentRecall final := by
  intro final same entry member
  have recalled := congrArg Prod.fst same
  change final.recall bob = (answerDecision bit label 0 false).recall bob at recalled
  rw [recalled, answerDecision_bobRecall, bobObserved_first_recall] at member
  cases List.mem_singleton.mp member
  rfl

theorem unseen_event_current_observed (bit : Bool) (label : Fin 3) :
    ∀ final ∈ unseenEvent bit label,
      LateOpeningRuntimeOpeningIdentity.ObservedCanonicalOpening bit final := by
  intro final same
  have ledger := congrArg (fun information : BobInformation => information.2.messages.ledger) same
  change (final.observe app bob).messages.ledger =
    ((answerDecision bit label 0 false).observe app bob).messages.ledger at ledger
  have target : ((answerDecision bit label 0 false).observe app bob).messages.ledger =
      [openingMessage bit] := by
    change ((answerDecision bit label 0 false).network.observe bob).ledger = _
    rw [answerDecision_bobNetwork]
  change openingMessage bit ∈ (final.observe app bob).messages.leaked ++
    (final.observe app bob).messages.ledger
  exact List.mem_append_right _ ((ledger.trans target).symm ▸ List.mem_singleton.mpr rfl)

private theorem information_atom (law : PMF app.Execution) (information : BobInformation) :
    (law.toOuterMeasure {final | bobInformation final = information}).toReal =
      ((law.map bobInformation) information).toReal := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

theorem genuine_quiet_unseen_probability (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool) :
    ((quietRetry weight nonnegative bit label submission seen).toOuterMeasure
      (unseenEvent bit label)).toReal = if seen then 0 else inclusionProbability weight := by
  cases seen
  · unfold quietRetry unseenEvent
    rw [information_atom, LateOpeningRuntimeBindingFactors.genuine_first_information_law
      weight nonnegative bit label submission genuine false]
    exact LateOpeningRuntimeBindingFactors.unseen_success_probability
      weight nonnegative bit label 0
  · have zero : (quietRetry weight nonnegative bit label submission true).toOuterMeasure
        (unseenEvent bit label) = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro final reached selected
      have retained := LateOpeningRuntimeEarlyRecall.settlement_recall weight nonnegative
        _ final reached
      have erased := congrArg bobInformation
        (LateOpeningRuntimeBindingObservation.genuine_retry_erased weight nonnegative
          bit label submission genuine true)
      rw [bobInformation_eraseRecall, bobInformation_eraseRecall] at erased
      have original := congrArg Prod.fst erased
      change ((finalDecision bit label ⟨some submission⟩ {(alice, 0)}).respond app alice
        ⟨none⟩).recall bob = (beforeLottery bit label 0 true).recall bob at original
      have observed := congrArg Prod.fst selected
      change final.recall bob = (answerDecision bit label 0 false).recall bob at observed
      simp only [↓reduceIte] at retained
      rw [retained, original, beforeLottery_bobRecall, answerDecision_bobRecall,
        bobObserved_first_recall, bobObserved_first_recall] at observed
      have distinct := congrArg (fun entries : List app.PlayerEntry =>
        entries.map (fun entry => entry.beforeView.messages.leaked)) observed
      change [[openingMessage bit]] = [[]] at distinct
      simp at distinct
    rw [zero, ENNReal.toReal_zero]
    rfl

theorem empty_information_representative (bit : Bool) (label : Fin 3) :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
      (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        alice site.1),
      history.1.state = some ⟨18, some alice,
        (LateOpeningRuntimeAliceEmptyWitness.decisionHistory
          weight nonnegative bit label).execution⟩ := by
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨18, some alice, secondLateDecision bit label 1 false⟩,
      (LateOpeningRuntimeAliceEmptyWitness.secondLateDecision_trace
        weight nonnegative bit label).some⟩
  obtain ⟨site, information⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      alice history (by change ¬ (18 = 0 ∧ some alice = none); simp) rfl
  exact ⟨site, ⟨history, information.symm⟩, rfl⟩

/-- Every genuine final response, including its private syntax, gives the
same complete receiver-information law. The other responses have unit error. -/
theorem final_information_close_opening (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (error : ℝ)
    (bound : ∀ actual : LateOpeningRuntimeAliceOpeningTremble.EmptyOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceOpeningTremble.nongenuineProbability
        weight nonnegative profile actual ≤ error) :
    PMF.WithinTV error
      ((finalResponseLaw weight nonnegative bit label ⟨none⟩ ∅
        (players weight nonnegative profile)).map bobInformation)
      ((settlementKernel weight nonnegative (beforeLottery bit label 1 false)).map
        bobInformation) := by
  classical
  let decision := LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label
  obtain ⟨site, history, current⟩ := empty_information_representative
    weight nonnegative bit label
  let actual : LateOpeningRuntimeAliceOpeningTremble.EmptyOpeningSite weight nonnegative :=
    ⟨site, decision, history, current⟩
  let responses := finalResponses bit label ⟨none⟩ ∅ (players weight nonnegative profile)
  let canonical := (settlementKernel weight nonnegative (beforeLottery bit label 1 false)).map
    bobInformation
  let responseError : app.Action → ℝ := fun response =>
    if LateOpeningRuntimeAliceOpeningRationality.GenuineResponse
      weight nonnegative decision response then 0 else 1
  have close := PMF.WithinTV.bind_right_expect responses responseError
    (payoffIntegrable_of_bounded responses responseError (C := 1) (by
      intro response
      dsimp only [responseError]
      split_ifs <;> norm_num)) (first := fun response =>
      (settlementKernel weight nonnegative
        ((finalDecision bit label ⟨none⟩ ∅).respond app alice response)).map bobInformation)
      (second := fun _ => canonical) (by
        intro response _
        by_cases genuine : LateOpeningRuntimeAliceOpeningRationality.GenuineResponse
            weight nonnegative decision response
        · have zero : responseError response = 0 := by
            dsimp only [responseError]
            rw [ite_eq_left genuine]
          rw [zero]
          rcases response with ⟨transmission⟩
          cases transmission with
          | none => cases genuine
          | some submission =>
              have equal := LateOpeningRuntimeBindingFactors.genuine_final_information_law
                weight nonnegative bit label submission genuine
              rw [equal]
              exact PMF.WithinTV.refl canonical
        · exact (PMF.withinTV_one _ canonical).mono (by
            dsimp only [responseError]
            rw [ite_eq_right genuine]))
  have probability := LateOpeningRuntimeAliceOpeningTremble.nongenuineProbability_of_representative
    weight nonnegative profile actual decision history current
  have information := history.2
  change (rawMenu.signals initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf alice
      history.1.trace = site.1 at information
  rw [rawMenu.info, current] at information
  have observed : site.1 = some (decision.execution.recall alice,
      decision.execution.observe app alice) := information.symm
  have errorMass : expect responses responseError =
      LateOpeningRuntimeAliceOpeningTremble.nongenuineProbability
        weight nonnegative profile actual := by
    have law : LateOpeningRuntimeAliceOpeningRationality.responseLaw
        weight nonnegative site (profile alice) = responses := by
      rw [LateOpeningRuntimeAliceOpeningRationality.responseLaw, observed]
      simp only [responses, finalResponses, players,
        ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
        ReactiveApplication.ResponseMenu.embedPolicy, ReactiveApplication.ResponseMenu.rawChoice,
        PMF.map_comp, Function.comp_def, decision,
        LateOpeningRuntimeAliceEmptyWitness.decisionHistory]
      rfl
    rw [probability]
    change expect responses responseError =
      ((LateOpeningRuntimeAliceOpeningRationality.responseLaw weight nonnegative site
        (profile alice)).toOuterMeasure
          {response | ¬ LateOpeningRuntimeAliceOpeningRationality.GenuineResponse
            weight nonnegative decision response}).toReal
    rw [law, ← expect_indicator]
    apply expect_congr_on_support
    intro response _
    dsimp only [responseError]
    by_cases genuine : LateOpeningRuntimeAliceOpeningRationality.GenuineResponse
        weight nonnegative decision response <;> simp [genuine]
  rw [errorMass, PMF.bind_const] at close
  have restricted := close.mono (bound actual)
  simpa only [finalResponseLaw, PMF.map_bind, responses, canonical] using restricted

theorem first_silent_unseen_error (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (error : ℝ)
    (bound : ∀ actual : LateOpeningRuntimeAliceOpeningTremble.EmptyOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceOpeningTremble.nongenuineProbability
        weight nonnegative profile actual ≤ error) :
    |((firstBindingLaw weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          ⟨none⟩ (players weight nonnegative profile)).toOuterMeasure
        (unseenEvent bit label)).toReal -
      earlySilenceProbability weight nonnegative profile bit label * inclusionProbability weight| ≤
      error * earlySilenceProbability weight nonnegative profile bit label := by
  rw [silent_first_silent_event_probability weight nonnegative bit label
    (players weight nonnegative profile) _ (unseen_event_quiet bit label)]
  have same : bobInformation ((firstSent bit label ⟨none⟩).sampledActivation app bob ∅) =
      bobInformation ((beforeBob bit label 0).sampledActivation app bob ∅) :=
    empty_early_information bit bit label label 1 0
  have policy := congrArg (fun information : BobInformation =>
    players weight nonnegative profile bob information.1 information.2) same
  change players weight nonnegative profile bob
      (((firstSent bit label ⟨none⟩).sampledActivation app bob ∅).recall bob)
      (((firstSent bit label ⟨none⟩).sampledActivation app bob ∅).observe app bob) =
    players weight nonnegative profile bob
      (((beforeBob bit label 0).sampledActivation app bob ∅).recall bob)
      (((beforeBob bit label 0).sampledActivation app bob ∅).observe app bob) at policy
  rw [policy]
  change |earlySilenceProbability weight nonnegative profile bit label *
      ((finalResponseLaw weight nonnegative bit label ⟨none⟩ ∅
        (players weight nonnegative profile)).toOuterMeasure (unseenEvent bit label)).toReal -
    earlySilenceProbability weight nonnegative profile bit label * inclusionProbability weight| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (show
    0 ≤ earlySilenceProbability weight nonnegative profile bit label from ENNReal.toReal_nonneg)]
  have close := (final_information_close_opening weight nonnegative profile bit label
    error bound).apply (bobInformation (answerDecision bit label 0 false))
  have timing : bobInformation (answerDecision bit label 0 false) =
      bobInformation (answerDecision bit label 1 false) :=
    answerDecision_unseen_timing_info bit label label
  rw [timing, LateOpeningRuntimeBindingFactors.unseen_success_probability
    weight nonnegative bit label 1] at close
  have atom := information_atom
    (finalResponseLaw weight nonnegative bit label ⟨none⟩ ∅ (players weight nonnegative profile))
    (bobInformation (answerDecision bit label 0 false))
  change ((finalResponseLaw weight nonnegative bit label ⟨none⟩ ∅
    (players weight nonnegative profile)).toOuterMeasure (unseenEvent bit label)).toReal = _ at atom
  rw [timing] at atom
  rw [atom]
  calc
    _ ≤ earlySilenceProbability weight nonnegative profile bit label * error :=
      mul_le_mul_of_nonneg_left close (show
        0 ≤ earlySilenceProbability weight nonnegative profile bit label from ENNReal.toReal_nonneg)
    _ = _ := by ring

theorem genuine_comparison_unseen_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) :
    ((firstComparison weight nonnegative profile bit label ⟨some submission⟩).toOuterMeasure
      (unseenEvent bit label)).toReal =
        earlySilenceProbability weight nonnegative profile bit label *
          inclusionProbability weight / 2 := by
  simp only [firstComparison, ite_eq_left genuine]
  rw [← expect_indicator, expect_mix _ _ _ _ _ _ (payoffIntegrable_ite_one_zero _ _)
    (payoffIntegrable_ite_one_zero _ _), expect_indicator, expect_indicator,
    early_comparison_event_probability weight nonnegative profile bit label submission true
      (unseenEvent bit label) (unseen_event_quiet bit label),
    early_comparison_event_probability weight nonnegative profile bit label submission false
      (unseenEvent bit label) (unseen_event_quiet bit label),
    genuine_quiet_unseen_probability weight nonnegative bit label submission genuine true,
    genuine_quiet_unseen_probability weight nonnegative bit label submission genuine false]
  have same := LateOpeningRuntimeSeenLikelihood.genuine_early_information
    weight nonnegative bit label submission genuine false
  have past := congrArg Prod.fst same
  have view := congrArg Prod.snd same
  change (earlyObserved bit label submission false).recall bob =
    ((beforeBob bit label 0).sampledActivation app bob ∅).recall bob at past
  change (earlyObserved bit label submission false).observe app bob =
    ((beforeBob bit label 0).sampledActivation app bob ∅).observe app bob at view
  rw [past, view]
  unfold earlySilenceProbability
  norm_num
  ring

open Classical in
theorem response_comparison_unseen_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (response : app.Action) :
    ((firstComparison weight nonnegative profile bit label response).toOuterMeasure
      (unseenEvent bit label)).toReal =
        (if GenuineResponse weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            response then earlySilenceProbability weight nonnegative profile bit label *
              inclusionProbability weight / 2 else 0) +
        (if (⟨none⟩ : app.Action) = response then
          ((firstBindingLaw weight nonnegative
            (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
              ⟨none⟩ (players weight nonnegative profile)).toOuterMeasure
                (unseenEvent bit label)).toReal else 0) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simp [firstComparison, GenuineResponse]
  | some submission =>
      have emitted : GenuineResponse weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            (⟨some submission⟩ : app.Action) ↔
          LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
            (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
              submission := by
        constructor
        · rintro ⟨other, same, genuine⟩
          cases Option.some.inj same
          exact genuine
        · exact fun genuine => ⟨submission, rfl, genuine⟩
      by_cases genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            submission
      · rw [ite_eq_left (emitted.mpr genuine)]
        simp only [ReactiveApplication.Action.mk.injEq, reduceCtorEq, ↓reduceIte, add_zero]
        exact genuine_comparison_unseen_probability weight nonnegative profile bit label
          submission genuine
      · have zero := LateOpeningRuntimeOpeningIdentity.nongenuine_first_observed_event_zero
          weight nonnegative bit label submission genuine (players weight nonnegative profile)
            (unseenEvent bit label) (unseen_event_current_observed bit label)
        rw [ite_eq_right (fun present => genuine (emitted.mp present))]
        simp only [firstComparison, ite_eq_right genuine,
          ReactiveApplication.Action.mk.injEq, reduceCtorEq, ↓reduceIte, add_zero]
        rw [zero, ENNReal.toReal_zero]

theorem comparison_unseen_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) :
    ((comparisonLaw weight nonnegative profile bit label).toOuterMeasure
      (unseenEvent bit label)).toReal =
        genuineProbability weight nonnegative profile bit label *
          earlySilenceProbability weight nonnegative profile bit label *
            inclusionProbability weight / 2 +
        firstSilenceProbability weight nonnegative profile bit label *
          ((firstBindingLaw weight nonnegative
            (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
              ⟨none⟩ (players weight nonnegative profile)).toOuterMeasure
                (unseenEvent bit label)).toReal := by
  classical
  unfold comparisonLaw
  rw [toReal_toOuterMeasure_bind]
  calc
    _ = expect (firstResponses weight nonnegative profile bit label) (fun response =>
        (earlySilenceProbability weight nonnegative profile bit label *
            inclusionProbability weight / 2) *
        (if GenuineResponse weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            response then 1 else 0) +
        (if (⟨none⟩ : app.Action) = response then
          ((firstBindingLaw weight nonnegative
            (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
              ⟨none⟩ (players weight nonnegative profile)).toOuterMeasure
                (unseenEvent bit label)).toReal else 0)) := by
      apply expect_congr_on_support
      intro response _
      rw [response_comparison_unseen_probability]
      split_ifs <;> simp
    _ = _ := by
      rw [expect_add (payoffIntegrable_const_mul
        (payoffIntegrable_ite_one_zero _ _))
          (payoffIntegrable_of_bounded _ _ (C := 1) (by
            intro response
            split_ifs
            · rw [abs_of_nonneg ENNReal.toReal_nonneg]
              exact ENNReal.toReal_le_of_le_ofReal zero_le_one
                (by simpa using outerMeasure_le_one _ _)
            · norm_num))]
      have genuineExpectation : expect (firstResponses weight nonnegative profile bit label)
          (fun response => if GenuineResponse weight nonnegative
            (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
              response then 1 else 0) =
          genuineProbability weight nonnegative profile bit label := by
        change expect (firstResponses weight nonnegative profile bit label)
          (fun response => if response ∈ {response | GenuineResponse weight nonnegative
            (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
              response} then 1 else 0) = _
        rw [expect_indicator]
        rfl
      rw [expect_const_mul, genuineExpectation, expect_ite_eq]
      unfold firstSilenceProbability
      ring

theorem original_unseen_error (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (error : ℝ) (errorNonnegative : 0 ≤ error)
    (retryBound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error)
    (openingBound : ∀ actual :
        LateOpeningRuntimeAliceOpeningTremble.EmptyOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceOpeningTremble.nongenuineProbability
        weight nonnegative profile actual ≤ error)
    (firstBound : firstNongenuineProbability weight nonnegative profile bit label ≤ error) :
    |((originalLaw weight nonnegative profile bit label).toOuterMeasure
        (unseenEvent bit label)).toReal -
      (1 - genuineProbability weight nonnegative profile bit label / 2) *
        earlySilenceProbability weight nonnegative profile bit label *
          inclusionProbability weight| ≤
      2 * error := by
  let alpha := genuineProbability weight nonnegative profile bit label
  let beta := firstSilenceProbability weight nonnegative profile bit label
  let bad := firstNongenuineProbability weight nonnegative profile bit label
  let p := earlySilenceProbability weight nonnegative profile bit label
  let q := inclusionProbability weight
  let actual := ((originalLaw weight nonnegative profile bit label).toOuterMeasure
    (unseenEvent bit label)).toReal
  let comparison := ((comparisonLaw weight nonnegative profile bit label).toOuterMeasure
    (unseenEvent bit label)).toReal
  have alphaNonnegative : 0 ≤ alpha := ENNReal.toReal_nonneg
  have betaNonnegative : 0 ≤ beta := ENNReal.toReal_nonneg
  have badNonnegative : 0 ≤ bad := ENNReal.toReal_nonneg
  have pNonnegative : 0 ≤ p := ENNReal.toReal_nonneg
  have pBound : p ≤ 1 := pmf_toReal_apply_le_one _ _
  have qNonnegative : 0 ≤ q := MessageNetwork.inclusionMass_nonnegative weight nonnegative 1
  have qBound : q ≤ 1 := (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
  have partition : alpha + beta + bad = 1 :=
    first_response_partition weight nonnegative profile bit label
  have retry : |actual - comparison| ≤ error * alpha :=
    (original_close_comparison weight nonnegative profile bit label error errorNonnegative
      retryBound) (unseenEvent bit label)
  have final := first_silent_unseen_error weight nonnegative profile bit label error openingBound
  have difference : comparison - (alpha / 2 + beta) * p * q =
      beta * (((firstBindingLaw weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          ⟨none⟩ (players weight nonnegative profile)).toOuterMeasure
            (unseenEvent bit label)).toReal - p * q) := by
    dsimp only [comparison, alpha, beta, p, q]
    rw [comparison_unseen_probability]
    ring
  have finalError : |comparison - (alpha / 2 + beta) * p * q| ≤ beta * (error * p) := by
    rw [difference, abs_mul, abs_of_nonneg betaNonnegative]
    exact mul_le_mul_of_nonneg_left final betaNonnegative
  have leadingError : |(alpha / 2 + beta) * p * q - (1 - alpha / 2) * p * q| ≤ bad := by
    have difference : (alpha / 2 + beta) * p * q - (1 - alpha / 2) * p * q = -bad * p * q := by
      calc
        _ = (alpha + beta - 1) * p * q := by ring
        _ = _ := by rw [show alpha + beta - 1 = -bad by linarith [partition]]
    rw [difference, abs_mul, abs_mul, abs_neg, abs_of_nonneg badNonnegative,
      abs_of_nonneg pNonnegative, abs_of_nonneg qNonnegative]
    exact (mul_le_mul_of_nonneg_left qBound (mul_nonneg badNonnegative pNonnegative)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left pBound badNonnegative)
  calc
    |actual - (1 - alpha / 2) * p * q| ≤
        |actual - comparison| +
          |comparison - (alpha / 2 + beta) * p * q| +
            |(alpha / 2 + beta) * p * q - (1 - alpha / 2) * p * q| := by
      have first := abs_sub_le actual comparison ((1 - alpha / 2) * p * q)
      have second := abs_sub_le comparison ((alpha / 2 + beta) * p * q)
        ((1 - alpha / 2) * p * q)
      linarith
    _ ≤ error * alpha + beta * (error * p) + bad := by linarith
    _ ≤ error * (alpha + beta) + bad := by
      nlinarith [mul_le_mul_of_nonneg_left pBound (mul_nonneg betaNonnegative errorNonnegative)]
    _ ≤ error + bad := by nlinarith [mul_nonneg errorNonnegative badNonnegative, partition]
    _ ≤ 2 * error := by dsimp only [bad]; linarith [firstBound]

end Vegas.Examples.LateOpeningRuntimeUnseenLikelihood
