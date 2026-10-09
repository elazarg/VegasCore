/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeFirstObservation
import Vegas.Examples.LateOpeningRuntimeBobBindingService
import Interaction.ReactivePolicyInvariant

/-! # Raw late-prefix kernels before the receiver's binding response

The kernel follows the original player policies through seven actual scheduler
rounds and then the receiver's binding activation. Events with silent receiver
recall retain the original probability of the earlier silent response. Every
other earlier response is excluded by remembered output, not by restricting
the raw action menu or conditioning on equilibrium play.

The final lottery, clock advance, expiry and observation are also evaluated
exactly for any raw pending pool. Private sender submission aliases remain in
the returned physical executions.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Vegas.Examples.LateOpeningRuntimeLatePrefixKernel

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeFirstObservation LateOpeningRuntimeAliceFirstDecision
  LateOpeningRuntimeBobBindingService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def afterEarly (players : Player → app.Policy) (execution : app.Execution) : PMF app.Execution :=
  (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 6 execution).bind
    (fun before => before.environmentStep app (.activate bob))

def firstBindingLaw (decision : DecisionHistory weight nonnegative) (response : app.Action)
    (players : Player → app.Policy) : PMF app.Execution :=
  (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 7
    (sent weight nonnegative decision response)).bind
      (fun before => before.environmentStep app (.activate bob))

/-- The final activation is the next command selected by the actual service. -/
theorem first_binding_command (decision : DecisionHistory weight nonnegative)
    (response : app.Action) (players : Player → app.Policy) (before : app.Execution)
    (reached : before ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 7 (sent weight nonnegative decision response)).support) :
    LateOpeningRuntimeService.scheduler weight nonnegative before.environmentRecall
      (before.observeEnvironment app) = PMF.pure (.activate bob) := by
  have cursor := app.runRounds_environmentRecall_length
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 7 _ before reached
  rw [sent, app.respond_environmentRecall, decision_cursor weight nonnegative decision] at cursor
  change stageChoice weight nonnegative before.environmentRecall.length _ = _
  rw [cursor]
  rfl

/-- This law keeps the original policies after the actual fair first sample. -/
theorem transmitted_binding_law (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (players : Player → app.Policy) :
    firstBindingLaw weight nonnegative decision ⟨some submission⟩ players =
      mix (1 / 2 : ℝ) (by norm_num) (by norm_num)
        ((app.invoke players bob
          ((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
            {(alice, 0)})).bind (afterEarly weight nonnegative players))
        ((app.invoke players bob
          ((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob ∅)).bind
            (afterEarly weight nonnegative players)) := by
  unfold firstBindingLaw
  rw [ReactiveApplication.runRounds, PMF.bind_bind,
    transmitted_round weight nonnegative, mix_bind]
  rfl

private def NonSilentRecall (execution : app.Execution) : Prop :=
  ∃ entry ∈ execution.recall bob, entry.action.transmission.isSome = true

private theorem nonSilentRecall_invariant (players : Player → app.Policy) :
    app.PolicyInvariant players NonSilentRecall where
  respond execution who response present _ := by
    obtain ⟨entry, member, issued⟩ := present
    exact ⟨entry, app.respond_recall_mono execution who bob response member, issued⟩
  environment execution next command present reached := by
    change ∃ entry ∈ next.recall bob, entry.action.transmission.isSome = true
    rw [app.environmentStep_recall execution next command reached]
    exact present

private theorem nonSilentRecall_respond (execution : app.Execution)
    (submission : app.Submission) :
    NonSilentRecall (execution.respond app bob ⟨some submission⟩) := by
  unfold NonSilentRecall
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
    List.mem_singleton]
  exact ⟨_, Or.inr rfl, rfl⟩

private theorem nonSilentRecall_not_silent (execution : app.Execution)
    (present : NonSilentRecall execution) : ¬ SilentRecall execution := by
  intro quiet
  obtain ⟨entry, member, issued⟩ := present
  rw [quiet entry member] at issued
  cases issued

/-- An actual remembered raw transmission cannot enter a later silent record. -/
theorem transmitted_early_silent_event_zero (players : Player → app.Policy)
    (execution : app.Execution) (submission : app.Submission) (event : Set app.Execution)
    (quiet : ∀ final ∈ event, SilentRecall final) :
    ((afterEarly weight nonnegative players
      (execution.respond app bob ⟨some submission⟩)).toOuterMeasure event).toReal = 0 := by
  have zero : (afterEarly weight nonnegative players
      (execution.respond app bob ⟨some submission⟩)).toOuterMeasure event = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    intro final reached member
    obtain ⟨before, continued, activated⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
    have invariant := nonSilentRecall_invariant players
    have remembered := invariant.runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 6 _ before
      (nonSilentRecall_respond execution submission) continued
    exact nonSilentRecall_not_silent final
      (invariant.environment before final (.activate bob) remembered activated) (quiet final member)
  rw [zero, ENNReal.toReal_zero]

/-- The original early silence probability is an exact multiplier, for any
final event whose actual complete receiver record is silent. -/
theorem early_silence_event_probability (players : Player → app.Policy)
    (execution : app.Execution) (event : Set app.Execution)
    (quiet : ∀ final ∈ event, SilentRecall final) :
    (((app.invoke players bob execution).bind
      (afterEarly weight nonnegative players)).toOuterMeasure event).toReal =
        (players bob (execution.recall bob) (execution.observe app bob) ⟨none⟩).toReal *
          ((afterEarly weight nonnegative players
            (execution.respond app bob ⟨none⟩)).toOuterMeasure event).toReal := by
  unfold ReactiveApplication.invoke
  rw [PMF.bind_map, toReal_toOuterMeasure_bind]
  calc
    _ = expect (players bob (execution.recall bob) (execution.observe app bob))
        (fun response => if (⟨none⟩ : app.Action) = response then
          ((afterEarly weight nonnegative players
            (execution.respond app bob ⟨none⟩)).toOuterMeasure event).toReal else 0) := by
      apply expect_congr_on_support
      intro response _
      simp only [Function.comp_apply]
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => simp only [↓reduceIte]
      | some submission =>
          rw [transmitted_early_silent_event_zero weight nonnegative players execution
            submission event quiet]
          simp
    _ = _ := expect_ite_eq _ _ _

/-- Every first raw packet remains present in the exact filtered prefix law;
the fair branches retain their respective original early silence weights. -/
theorem transmitted_binding_silent_event_probability
    (decision : DecisionHistory weight nonnegative) (submission : app.Submission)
    (players : Player → app.Policy) (event : Set app.Execution)
    (quiet : ∀ final ∈ event, SilentRecall final) :
    ((firstBindingLaw weight nonnegative decision ⟨some submission⟩ players).toOuterMeasure
      event).toReal =
        (1 / 2 : ℝ) *
          ((players bob
            (((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
              {(alice, 0)}).recall bob)
            (((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
              {(alice, 0)}).observe app bob) ⟨none⟩).toReal *
            ((afterEarly weight nonnegative players
              (((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
                {(alice, 0)}).respond app bob ⟨none⟩)).toOuterMeasure event).toReal) +
        (1 / 2 : ℝ) *
          ((players bob
            (((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
              ∅).recall bob)
            (((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
              ∅).observe app bob) ⟨none⟩).toReal *
            ((afterEarly weight nonnegative players
              (((sent weight nonnegative decision ⟨some submission⟩).sampledActivation app bob
                ∅).respond app bob ⟨none⟩)).toOuterMeasure event).toReal) := by
  rw [transmitted_binding_law, ← expect_indicator,
    expect_mix _ _ _ _ _ _ (payoffIntegrable_ite_one_zero _ _)
      (payoffIntegrable_ite_one_zero _ _), expect_indicator, expect_indicator,
    early_silence_event_probability weight nonnegative players _ event quiet,
    early_silence_event_probability weight nonnegative players _ event quiet]
  norm_num

def lotteryOutcome (execution : app.Execution) (selected : Option (MessageId Player)) :
    app.Execution :=
  match selected with
  | none => recorded execution .wait execution.application
  | some id =>
      { execution.includePending app id with environmentRecall :=
        execution.environmentRecall ++ [⟨execution.observeEnvironment app, .include id⟩] }

def clocked (execution : app.Execution) : app.Execution :=
  recorded execution (.application .advanceClock)
    { execution.application with clock := execution.application.clock + 1 }

def settled (execution : app.Execution) (selected : Option (MessageId Player)) :
    PMF app.Execution :=
  (clocked (lotteryOutcome execution selected)).environmentStep app
    (.application (.expire aliceEvent))

def settlementKernel (execution : app.Execution) : PMF app.Execution :=
  (MessageNetwork.chooseWithOutside weight nonnegative
    (MessageNetwork.pendingIds execution.network.pending)).bind fun selected =>
      (settled execution selected).bind fun before =>
        before.environmentStep app (.activate bob)

private theorem lottery_round (players : Player → app.Policy) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 8) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players execution =
      (MessageNetwork.chooseWithOutside weight nonnegative
        (MessageNetwork.pendingIds execution.network.pending)).map (lotteryOutcome execution) := by
  rw [ReactiveApplication.round, LateOpeningRuntimeService.scheduler, cursor]
  change ((MessageNetwork.chooseWithOutside weight nonnegative
    (MessageNetwork.pendingIds execution.network.pending)).map app.pendingLotteryCommand).bind _ = _
  rw [PMF.bind_map, ← PMF.bind_pure_comp]
  apply bind_congr_on_support
  intro selected _
  simp only [Function.comp_apply]
  cases selected <;>
    simp only [ReactiveApplication.pendingLotteryCommand, Option.elim,
      ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
      ReactiveApplication.Execution.environmentStep, ReactiveApplication.resume,
      PMF.pure_map, PMF.pure_bind]
  all_goals rfl

/-- Exact three-command settlement for every raw pending pool. No subsequent
player policy influences the lottery, clock advance or deterministic expiry. -/
theorem settlement_rounds (players : Player → app.Policy) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 8) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 3 execution =
      (MessageNetwork.chooseWithOutside weight nonnegative
        (MessageNetwork.pendingIds execution.network.pending)).bind (settled execution) := by
  rw [ReactiveApplication.runRounds, lottery_round weight nonnegative players execution cursor,
    PMF.bind_map]
  apply bind_congr_on_support
  intro selected _
  simp only [Function.comp_apply]
  have afterCursor : (lotteryOutcome execution selected).environmentRecall.length = 9 := by
    cases selected <;>
      simp only [lotteryOutcome, recorded, List.length_append, List.length_singleton, cursor]
  have tickCursor : (clocked (lotteryOutcome execution selected)).environmentRecall.length =
      10 := by
    simp only [clocked, recorded, List.length_append, List.length_singleton, afterCursor]
  have tick : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (lotteryOutcome execution selected) =
        PMF.pure (clocked (lotteryOutcome execution selected)) :=
    (fixed_round weight nonnegative players _ _ 9 (.application .advanceClock) afterCursor
      rfl (recorded_clock _)).trans rfl
  have expire : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (clocked (lotteryOutcome execution selected)) =
        settled execution selected := by
    rw [ReactiveApplication.round, LateOpeningRuntimeService.scheduler, tickCursor]
    change (PMF.pure (.application (.expire aliceEvent) : app.Command)).bind _ = _
    rw [PMF.pure_bind, ReactiveApplication.dispatch]
    change ((clocked (lotteryOutcome execution selected)).environmentStep app
      (.application (.expire aliceEvent))).bind PMF.pure = _
    rw [PMF.bind_pure]
    rfl
  rw [ReactiveApplication.runRounds, tick, PMF.pure_bind,
    ReactiveApplication.runRounds, expire]
  change (settled execution selected).bind PMF.pure = _
  rw [PMF.bind_pure]

/-- All raw final responses admit this exact physical lottery-to-observation
kernel, including malformed and duplicate envelopes. -/
theorem settlement_activation (players : Player → app.Policy) (execution : app.Execution)
    (cursor : execution.environmentRecall.length = 8) :
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 3
      execution).bind
      (fun before => before.environmentStep app (.activate bob)) =
        settlementKernel weight nonnegative execution := by
  rw [settlement_rounds weight nonnegative players execution cursor, PMF.bind_bind]
  rfl

end Vegas.Examples.LateOpeningRuntimeLatePrefixKernel
