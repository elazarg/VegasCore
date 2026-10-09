/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeFirstRetryComparison
import Vegas.Examples.LateOpeningRuntimeOpeningIdentity
import Vegas.Examples.LateOpeningRuntimeEarlyRecall

/-! # Actual likelihoods after an opening was seen at the early callback

The event fixes the complete receiver observation and remembered response,
for either actual acceptance or actual omission. Its original first-prefix
probability has a leading term consisting of genuine first-emission mass,
the original early receiver silence atom, the fair early disclosure factor,
and the physical settlement probability. Nongenuine packets and deferred
first responses contribute exactly zero. The error is relative to the
original genuine-emission mass, even when that mass vanishes.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSeenLikelihood

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeLatePrefixKernel
  LateOpeningRuntimeLateResponseKernel LateOpeningRuntimeBindingObservation
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeEarlyRecall
  LateOpeningRuntimeBobBindingService LateOpeningRuntimeFirstObservation

def seenExecution (bit : Bool) (label : Fin 3) (accepted : Bool) : app.Execution :=
  if accepted then answerDecision bit label 0 true
  else failedAnswerDecision bit label 0 true false

def seenEvent (bit : Bool) (label : Fin 3) (accepted : Bool) : Set app.Execution :=
  {final | bobInformation final = bobInformation (seenExecution bit label accepted)}

def settlementProbability (weight : ℝ) (accepted : Bool) : ℝ :=
  if accepted then inclusionProbability weight else 1 - inclusionProbability weight

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def earlySilenceProbability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) : ℝ :=
  let observed := (beforeBob bit label 0).sampledActivation app bob {(alice, 0)}
  (players weight nonnegative profile bob (observed.recall bob)
    (observed.observe app bob) ⟨none⟩).toReal

theorem seen_execution_recall (bit : Bool) (label : Fin 3) (accepted : Bool) :
    (seenExecution bit label accepted).recall bob = [bobObservationRecord bit label true] := by
  cases accepted
  · simp only [seenExecution, Bool.false_eq_true, ↓reduceIte]
    rw [failedAnswerDecision_recall, bobObserved_first_recall]
  · simp only [seenExecution, ↓reduceIte]
    rw [answerDecision_bobRecall, bobObserved_first_recall]

theorem seen_event_quiet (bit : Bool) (label : Fin 3) (accepted : Bool) :
    ∀ final ∈ seenEvent bit label accepted, SilentRecall final := by
  intro final same entry member
  have remembered := congrArg Prod.fst same
  change final.recall bob = (seenExecution bit label accepted).recall bob at remembered
  rw [remembered, seen_execution_recall] at member
  cases List.mem_singleton.mp member
  rfl

theorem seen_event_early_observed (bit : Bool) (label : Fin 3) (accepted : Bool) :
    ∀ final ∈ seenEvent bit label accepted, EarlyObservedOpening bit final := by
  intro final same
  have remembered := congrArg Prod.fst same
  change final.recall bob = (seenExecution bit label accepted).recall bob at remembered
  refine ⟨bobObservationRecord bit label true, ?_, ?_⟩
  · rw [remembered, seen_execution_recall]
    exact List.mem_singleton.mpr rfl
  · exact List.mem_singleton.mpr rfl

theorem seen_event_current_observed (bit : Bool) (label : Fin 3) (accepted : Bool) :
    ∀ final ∈ seenEvent bit label accepted,
      LateOpeningRuntimeOpeningIdentity.ObservedCanonicalOpening bit final := by
  intro final same
  have leaked := congrArg (fun information : BobInformation =>
    information.2.messages.leaked) same
  change (final.observe app bob).messages.leaked =
    ((seenExecution bit label accepted).observe app bob).messages.leaked at leaked
  have target : ((seenExecution bit label accepted).observe app bob).messages.leaked =
      [openingMessage bit] := by
    cases accepted
    · change ((failedAnswerDecision bit label 0 true false).network.observe bob).leaked = _
      rw [failedAnswerDecision_network]
      rfl
    · change ((answerDecision bit label 0 true).network.observe bob).leaked = _
      rw [answerDecision_bobNetwork]
      rfl
  change openingMessage bit ∈ (final.observe app bob).messages.leaked ++
    (final.observe app bob).messages.ledger
  exact List.mem_append_left _ ((leaked.trans target).symm ▸ List.mem_singleton.mpr rfl)

private theorem seen_outcomes_distinct (bit : Bool) (label : Fin 3) :
    bobInformation (answerDecision bit label 0 true) ≠
      bobInformation (failedAnswerDecision bit label 0 true false) := by
  intro same
  have receipts := congrArg (fun information : BobInformation => information.2.receipts) same
  change (acceptedLottery bit label 0 true).receipts =
    (failedAnswerDecision bit label 0 true false).receipts at receipts
  rw [acceptedLottery_receipts_eq, failedAnswerDecision_receipts] at receipts
  contradiction

private theorem information_atom (law : PMF app.Execution) (information : BobInformation) :
    (law.toOuterMeasure {final | bobInformation final = information}).toReal =
      ((law.map bobInformation) information).toReal := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

theorem canonical_seen_probability (bit : Bool) (label : Fin 3) (accepted : Bool) :
    (((settlementKernel weight nonnegative (beforeLottery bit label 0 true)).map bobInformation)
      (bobInformation (seenExecution bit label accepted))).toReal =
        settlementProbability weight accepted := by
  rw [LateOpeningRuntimeBindingFactors.canonical_seen_information_law, mix_apply_toReal]
  cases accepted
  · simp [seenExecution, settlementProbability, PMF.pure_apply,
      (seen_outcomes_distinct bit label).symm]
  · simp [seenExecution, settlementProbability, PMF.pure_apply, seen_outcomes_distinct]

theorem genuine_quiet_seen_probability (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (accepted : Bool) :
    ((quietRetry weight nonnegative bit label submission true).toOuterMeasure
      (seenEvent bit label accepted)).toReal = settlementProbability weight accepted := by
  unfold seenEvent
  rw [information_atom]
  unfold quietRetry
  rw [LateOpeningRuntimeBindingFactors.genuine_first_information_law
    weight nonnegative bit label submission genuine true]
  exact canonical_seen_probability weight nonnegative bit label accepted

theorem empty_quiet_seen_probability (bit : Bool) (label : Fin 3)
    (submission : app.Submission) (accepted : Bool) :
    ((quietRetry weight nonnegative bit label submission false).toOuterMeasure
      (seenEvent bit label accepted)).toReal = 0 := by
  let silent : Player → app.Policy := fun _ _ _ => PMF.pure ⟨none⟩
  have law : finalResponseLaw weight nonnegative bit label ⟨some submission⟩ ∅ silent =
      quietRetry weight nonnegative bit label submission false := by
    unfold finalResponseLaw finalResponses
    rw [PMF.pure_bind]
    rfl
  rw [← law, empty_early_observed_event_zero weight nonnegative bit label ⟨some submission⟩
    bit silent (seenEvent bit label accepted) (seen_event_early_observed bit label accepted),
    ENNReal.toReal_zero]

private theorem sampled_erase (execution : app.Execution)
    (selected : Finset (MessageId Player)) :
    (execution.sampledActivation app bob selected).eraseRecall app alice =
      (execution.eraseRecall app alice).sampledActivation app bob selected := rfl

theorem genuine_early_information (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool) :
    bobInformation (earlyObserved bit label submission seen) =
      bobInformation ((beforeBob bit label 0).sampledActivation app bob
        (if seen then {(alice, 0)} else ∅)) := by
  have projected := congrArg (fun execution : app.Execution =>
    bobInformation (execution.sampledActivation app bob
      (if seen then {(alice, 0)} else ∅)))
        (genuine_first_erased weight nonnegative bit label submission genuine)
  rw [← sampled_erase, ← sampled_erase, bobInformation_eraseRecall,
    bobInformation_eraseRecall] at projected
  exact projected

theorem early_comparison_filtered_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (submission : app.Submission) (seen accepted : Bool) :
    ((earlyComparison weight nonnegative profile bit label submission seen).toOuterMeasure
      (seenEvent bit label accepted)).toReal =
        (players weight nonnegative profile bob
          ((earlyObserved bit label submission seen).recall bob)
          ((earlyObserved bit label submission seen).observe app bob) ⟨none⟩).toReal *
          ((quietRetry weight nonnegative bit label submission seen).toOuterMeasure
            (seenEvent bit label accepted)).toReal :=
  early_comparison_event_probability weight nonnegative profile bit label submission seen
    (seenEvent bit label accepted) (seen_event_quiet bit label accepted)

theorem genuine_comparison_seen_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (accepted : Bool) :
    ((firstComparison weight nonnegative profile bit label ⟨some submission⟩).toOuterMeasure
      (seenEvent bit label accepted)).toReal =
        earlySilenceProbability weight nonnegative profile bit label *
          settlementProbability weight accepted / 2 := by
  simp only [firstComparison, ite_eq_left genuine]
  rw [← expect_indicator, expect_mix _ _ _ _ _ _ (payoffIntegrable_ite_one_zero _ _)
    (payoffIntegrable_ite_one_zero _ _), expect_indicator, expect_indicator,
    early_comparison_filtered_probability, early_comparison_filtered_probability,
    genuine_quiet_seen_probability weight nonnegative bit label submission genuine accepted,
    empty_quiet_seen_probability weight nonnegative bit label submission accepted]
  have same := genuine_early_information weight nonnegative bit label submission genuine true
  have past := congrArg Prod.fst same
  have view := congrArg Prod.snd same
  change (earlyObserved bit label submission true).recall bob =
    ((beforeBob bit label 0).sampledActivation app bob {(alice, 0)}).recall bob at past
  change (earlyObserved bit label submission true).observe app bob =
    ((beforeBob bit label 0).sampledActivation app bob {(alice, 0)}).observe app bob at view
  rw [past, view]
  unfold earlySilenceProbability
  ring

open Classical in
theorem response_comparison_seen_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (response : app.Action) (accepted : Bool) :
    ((firstComparison weight nonnegative profile bit label response).toOuterMeasure
      (seenEvent bit label accepted)).toReal =
        if GenuineResponse weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            response then earlySilenceProbability weight nonnegative profile bit label *
              settlementProbability weight accepted / 2 else 0 := by
  classical
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      have empty : ¬ GenuineResponse weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            (⟨none⟩ : app.Action) := by
        rintro ⟨_, same, _⟩
        cases same
      rw [ite_eq_right empty]
      exact first_silent_observed_event_zero weight nonnegative bit label bit
        (players weight nonnegative profile) (seenEvent bit label accepted)
          (seen_event_quiet bit label accepted) (seen_event_early_observed bit label accepted)
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
        exact genuine_comparison_seen_probability weight nonnegative profile bit label
          submission genuine accepted
      · rw [ite_eq_right (fun present => genuine (emitted.mp present))]
        simp only [firstComparison, ite_eq_right genuine]
        rw [LateOpeningRuntimeOpeningIdentity.nongenuine_first_observed_event_zero
          weight nonnegative bit label submission genuine (players weight nonnegative profile)
            (seenEvent bit label accepted) (seen_event_current_observed bit label accepted),
          ENNReal.toReal_zero]

theorem comparison_seen_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (accepted : Bool) :
    ((comparisonLaw weight nonnegative profile bit label).toOuterMeasure
      (seenEvent bit label accepted)).toReal =
        genuineProbability weight nonnegative profile bit label *
          earlySilenceProbability weight nonnegative profile bit label *
            settlementProbability weight accepted / 2 := by
  classical
  unfold comparisonLaw
  rw [toReal_toOuterMeasure_bind]
  calc
    _ = expect (firstResponses weight nonnegative profile bit label) (fun response =>
        (earlySilenceProbability weight nonnegative profile bit label *
          settlementProbability weight accepted / 2) *
          if GenuineResponse weight nonnegative
            (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
              response then 1 else 0) := by
      apply expect_congr_on_support
      intro response _
      rw [response_comparison_seen_probability]
      split_ifs <;> simp
    _ = _ := by
      rw [expect_const_mul]
      change (_ * expect (firstResponses weight nonnegative profile bit label)
        (fun response => if response ∈ {response | GenuineResponse weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            response} then 1 else 0)) = _
      rw [expect_indicator]
      unfold genuineProbability
      ring

theorem original_seen_error (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (accepted : Bool)
    (error : ℝ) (errorNonnegative : 0 ≤ error)
    (bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error) :
    |((originalLaw weight nonnegative profile bit label).toOuterMeasure
        (seenEvent bit label accepted)).toReal -
      genuineProbability weight nonnegative profile bit label *
        earlySilenceProbability weight nonnegative profile bit label *
          settlementProbability weight accepted / 2| ≤
      error * genuineProbability weight nonnegative profile bit label := by
  have close := original_close_comparison weight nonnegative profile bit label error
    errorNonnegative bound (seenEvent bit label accepted)
  rwa [comparison_seen_probability] at close

end Vegas.Examples.LateOpeningRuntimeSeenLikelihood
