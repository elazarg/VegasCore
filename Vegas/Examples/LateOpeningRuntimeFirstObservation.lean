/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstDecision
import Vegas.Examples.LateOpeningRuntimeObservation
import Interaction.MessageMonitoring
import GameTheory.Math.Probability.ExpectationMixture

/-! # Exact first pending observations under raw sender lotteries

At the genuine clock-one sender decision following protected silence, every
raw transmission receives Alice's fresh identifier zero. Bob's next actual
activation samples that one pending identifier fairly. The complete canonical
opening is observed precisely when Alice emitted its payload and the sample
selected it. Private submission aliases remain in Alice's own recall.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Vegas.Examples.LateOpeningRuntimeFirstObservation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeAliceFirstDecision LateOpeningRuntimeObservation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def sent (decision : DecisionHistory weight nonnegative) (response : app.Action) :
    app.Execution := decision.execution.respond app alice response

def GenuineResponse (decision : DecisionHistory weight nonnegative) (response : app.Action) :
    Prop := ∃ submission, response.transmission = some submission ∧
      EmitsOpening weight nonnegative decision submission

def ObservedOpening (decision : DecisionHistory weight nonnegative) (execution : app.Execution) :
    Prop := openingMessage decision.bit ∈ execution.network.leaked bob

private theorem serials (decision : DecisionHistory weight nonnegative) :
    decision.execution.network.SerialsBeforeNext :=
  app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler weight nonnegative)
    initial LateOpeningRuntimeService.horizon decision.trace

theorem opening_not_previously_observed (decision : DecisionHistory weight nonnegative) :
    ¬ ObservedOpening weight nonnegative decision decision.execution := by
  intro observed
  have before := (serials weight nonnegative decision).leaked bob _ observed
  change 0 < decision.execution.network.nextSerial alice at before
  rw [decision_serial weight nonnegative decision] at before
  omega

theorem submitted_pending (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) :
    (sent weight nonnegative decision ⟨some submission⟩).network.pending =
      [⟨(alice, 0), app.packet (app.submit decision.execution.application alice submission) alice
        (decision.execution.network.known alice) submission⟩] := by
  change decision.execution.network.pending ++
    [⟨(alice, decision.execution.network.nextSerial alice), _⟩] = _
  rw [decision.pending, decision_serial weight nonnegative decision]
  rfl

private theorem submitted_known (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) :
    (sent weight nonnegative decision ⟨some submission⟩).network.known bob =
      decision.execution.network.known bob := by
  change ((decision.execution.network.inputs ++
    [(⟨(alice, _), _⟩ : Message Player app.Payload)]).filter
    (fun message => message.sender = bob)) ++ decision.execution.network.leaked bob ++
      decision.execution.network.ledger = _
  rw [List.filter_append]
  simp [Message.sender, alice, bob, MessageNetwork.known]

private theorem unknown_identifier (decision : DecisionHistory weight nonnegative) :
    (decision.execution.network.known bob).any (fun message => message.id = (alice, 0)) =
      false := by
  apply Bool.eq_false_iff.mpr
  intro present
  obtain ⟨message, member, identified⟩ := List.any_eq_true.mp present
  have same : message.id = (alice, 0) := of_decide_eq_true identified
  have before := (serials weight nonnegative decision).known bob message member
  rw [same, decision_serial weight nonnegative decision] at before
  omega

theorem sampled_opening_iff (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) :
    ObservedOpening weight nonnegative decision
        ((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
          {(alice, 0)}) ↔ EmitsOpening weight nonnegative decision submission := by
  let execution := sent weight nonnegative decision ⟨some submission⟩
  have pending := submitted_pending weight nonnegative decision submission
  constructor
  · intro observed
    have learned := execution.network.learn_mem bob {(alice, 0)}
      (openingMessage decision.bit) observed
    rcases learned with previous | ⟨current, _⟩
    · exact (opening_not_previously_observed weight nonnegative decision previous).elim
    · rw [pending] at current
      have same := List.mem_singleton.mp current
      exact congrArg Message.payload same.symm
  · intro genuine
    have found : execution.network.lookup (alice, 0) = some (openingMessage decision.bit) := by
      change execution.network.pending.find? (fun message => message.id = (alice, 0)) = _
      rw [pending, genuine]
      rfl
    have unknown : (execution.network.known bob).any
        (fun message => message.id = (alice, 0)) = false := by
      rw [submitted_known weight nonnegative decision submission]
      exact unknown_identifier weight nonnegative decision
    have reported := execution.network.reports_learn_selected (fun _ => true) bob
      {(alice, 0)} (alice, 0) (openingMessage decision.bit) found (by decide) (by simp)
        unknown rfl
    rcases ((MessageNetwork.PlayerView.mem_reports ..).mp reported).1 with leaked | published
    · exact leaked
    · have before := (serials weight nonnegative decision).ledger _ published
      change 0 < decision.execution.network.nextSerial alice at before
      rw [decision_serial weight nonnegative decision] at before
      omega

/-- The actual next scheduler round retains the chosen private alias and
uses Bob's arbitrary raw policy after his fair first pending sample. -/
theorem transmitted_round (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (sent weight nonnegative decision ⟨some submission⟩) =
      mix (1 / 2 : ℝ) (by norm_num) (by norm_num)
        (app.invoke players bob
          ((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
            {(alice, 0)}))
        (app.invoke players bob
          ((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob ∅)) := by
  have foreign : foreignPending bob
      (sent weight nonnegative decision ⟨some submission⟩).network.pending = {(alice, 0)} := by
    rw [submitted_pending]
    rfl
  rw [ReactiveApplication.round, LateOpeningRuntimeService.scheduler]
  change (stageChoice weight nonnegative
    (decision.execution.respond app alice ⟨some submission⟩).environmentRecall.length _).bind _ = _
  rw [app.respond_environmentRecall, decision_cursor weight nonnegative decision]
  change (PMF.pure (.activate bob : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.activation_samples, PMF.bind_map]
  change (leaks bob (sent weight nonnegative decision ⟨some submission⟩).network.pending).bind _ = _
  rw [leaks_singleton bob _ (alice, 0) foreign, mix_bind, PMF.pure_bind, PMF.pure_bind]
  rfl

/-- The exact sample branches continue under the original arbitrary player
policies, including strategies that use Alice's private submission alias. -/
theorem transmitted_continuation (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (players : Player → app.Policy) (count : Nat) :
    (app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (sent weight nonnegative decision ⟨some submission⟩)).bind
          (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players count) =
      mix (1 / 2 : ℝ) (by norm_num) (by norm_num)
        ((app.invoke players bob
          ((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
            {(alice, 0)})).bind
            (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players count))
        ((app.invoke players bob
          ((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob ∅)).bind
            (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
              players count)) :=
  by rw [transmitted_round weight nonnegative, mix_bind]

theorem observed_respond_iff (decision : DecisionHistory weight nonnegative)
    (execution : app.Execution) (who : Player) (response : app.Action) :
    ObservedOpening weight nonnegative decision (execution.respond app who response) ↔
      ObservedOpening weight nonnegative decision execution := by
  rcases response with ⟨transmission⟩
  cases transmission <;> rfl

private theorem observed_empty_false (decision : DecisionHistory weight nonnegative)
    (response : app.Action) :
    ¬ ObservedOpening weight nonnegative decision
      ((sent weight nonnegative decision response).sampledActivation app bob ∅) := by
  simp only [ReactiveApplication.Execution.sampledActivation, MessageNetwork.learn_empty]
  exact (observed_respond_iff weight nonnegative decision decision.execution alice response).not.mpr
    (opening_not_previously_observed weight nonnegative decision)

private theorem invoked_observation_probability (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) (execution : app.Execution) :
    ((app.invoke players bob execution).toOuterMeasure
      {final | ObservedOpening weight nonnegative decision final}).toReal =
        if ObservedOpening weight nonnegative decision execution then 1 else 0 := by
  classical
  rw [← expect_indicator]
  unfold ReactiveApplication.invoke
  rw [expect_map]
  calc
    _ = expect (players bob (execution.recall bob) (execution.observe app bob))
        (fun _ => if ObservedOpening weight nonnegative decision execution
          then (1 : ℝ) else 0) := by
      apply expect_congr_on_support
      intro response _
      simp only [Function.comp_apply, Set.mem_ofPred_eq, observed_respond_iff]
    _ = _ := expect_constant _ _

private theorem silent_round (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (sent weight nonnegative decision ⟨none⟩) =
      app.invoke players bob
        ((sent weight nonnegative decision ⟨none⟩).sampledActivation app bob ∅) := by
  have empty : foreignPending bob (sent weight nonnegative decision ⟨none⟩).network.pending =
      ∅ := by
    change foreignPending bob decision.execution.network.pending = ∅
    rw [decision.pending]
    rfl
  have noSamples : leaks bob (sent weight nonnegative decision ⟨none⟩).network.pending =
      PMF.pure ∅ := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro selected supported
    have subset := (leaks_supported bob _ selected).mp supported
    rw [empty] at subset
    exact Finset.subset_empty.mp subset
  rw [ReactiveApplication.round, LateOpeningRuntimeService.scheduler]
  change (stageChoice weight nonnegative
    (decision.execution.respond app alice ⟨none⟩).environmentRecall.length _).bind _ = _
  rw [app.respond_environmentRecall, decision_cursor weight nonnegative decision]
  change (PMF.pure (.activate bob : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.activation_samples, PMF.bind_map]
  change (leaks bob (sent weight nonnegative decision ⟨none⟩).network.pending).bind _ = _
  rw [noSamples, PMF.pure_bind]
  rfl

/-- Arbitrary forbidden raw packets cannot contribute to the probability
of this exact observed opening, even before any rationality normalization. -/
theorem response_observation_probability (decision : DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) :
    ((app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (sent weight nonnegative decision response)).toOuterMeasure
        {final | ObservedOpening weight nonnegative decision final}).toReal =
      if GenuineResponse weight nonnegative decision response then 1 / 2 else 0 := by
  classical
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      rw [silent_round, invoked_observation_probability,
        ite_eq_right (observed_empty_false weight nonnegative decision ⟨none⟩)]
      simp [GenuineResponse]
  | some submission =>
      have genuine : GenuineResponse weight nonnegative decision ⟨some submission⟩ ↔
          EmitsOpening weight nonnegative decision submission := by
        constructor
        · rintro ⟨other, same, emitted⟩
          cases Option.some.inj same
          exact emitted
        · exact fun emitted => ⟨submission, rfl, emitted⟩
      rw [← expect_indicator, transmitted_round,
        expect_mix _ _ _ _ _ _ (payoffIntegrable_ite_one_zero _ _)
          (payoffIntegrable_ite_one_zero _ _), expect_indicator, expect_indicator,
        invoked_observation_probability, invoked_observation_probability,
        ite_eq_right (observed_empty_false weight nonnegative decision ⟨some submission⟩)]
      simp only [sampled_opening_iff, mul_zero, add_zero, mul_ite, mul_one]
      rw [genuine]

/-- For every raw first-response lottery, the exact opening observation mass
is one half its genuine emission mass. No private alias is discarded. -/
theorem first_observation_probability (decision : DecisionHistory weight nonnegative)
    (responses : PMF app.Action) (players : Player → app.Policy) :
    ((responses.bind fun response =>
      app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (sent weight nonnegative decision response)).toOuterMeasure
          {final | ObservedOpening weight nonnegative decision final}).toReal =
      (1 / 2 : ℝ) * (responses.toOuterMeasure
        {response | GenuineResponse weight nonnegative decision response}).toReal := by
  classical
  rw [toReal_toOuterMeasure_bind]
  calc
    _ = expect responses (fun response => (1 / 2 : ℝ) *
        if GenuineResponse weight nonnegative decision response then 1 else 0) := by
      apply expect_congr_on_support
      intro response _
      rw [response_observation_probability]
      split_ifs <;> norm_num
    _ = _ := by
      rw [expect_const_mul]
      change (1 / 2 : ℝ) * expect responses
        (fun response => if response ∈ {response | GenuineResponse weight nonnegative
          decision response} then 1 else 0) = _
      rw [expect_indicator]

end Vegas.Examples.LateOpeningRuntimeFirstObservation
