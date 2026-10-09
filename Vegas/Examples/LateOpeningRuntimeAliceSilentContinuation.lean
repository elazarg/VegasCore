/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceOpeningContinuation
import Vegas.Examples.LateOpeningRuntimeProtectedOpening

/-! # Certain publication failure after Alice's last silence

At a real last callback with no previous Alice packet, silence leaves the
pending pool empty. The next three public commands wait, advance the clock,
and expire Alice's publication. Every later raw policy preserves that failure.
The source forfeit therefore bounds Alice's final utility by reward-forfeit,
independently of Bob's hidden prior behavior or later responses.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceSilentContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeAliceContinuation LateOpeningRuntimeUtility
  LateOpeningRuntimeAliceEmptyDecision LateOpeningRuntimeProtectedOpening

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def silentLaw (decision : DecisionHistory weight nonnegative) (players : Player → app.Policy) :
    PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 18
    (decision.execution.respond app alice ⟨none⟩)

/-- The complete three-command continuation is deterministic; this is stronger
than finding a supported failure branch. -/
theorem silent_prefix (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) :
    ∃ failed, app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 3
      (decision.execution.respond app alice ⟨none⟩) = PMF.pure failed ∧
      failed.application.config.store (.inr aliceEvent) = some (.failure : PublicationResult Bool) ∧
      failed.environmentRecall.length = 11 := by
  let execution := decision.execution.respond app alice ⟨none⟩
  let waited := recorded execution .wait execution.application
  let ticked := recorded waited (.application .advanceClock)
    { waited.application with clock := waited.application.clock + 1 }
  have cursor : execution.environmentRecall.length = 8 :=
    decision_cursor weight nonnegative decision
  have waitedCursor : waited.environmentRecall.length = 9 := by
    change (execution.environmentRecall ++ [_]).length = 9
    rw [List.length_append, List.length_singleton, cursor]
  have tickedCursor : ticked.environmentRecall.length = 10 := by
    change (waited.environmentRecall ++ [_]).length = 10
    rw [List.length_append, List.length_singleton, waitedCursor]
  have pending : execution.network.pending = [] := decision.pending
  have idle : stageChoice weight nonnegative 8 (execution.observeEnvironment app) =
      PMF.pure .wait := by
    change (MessageNetwork.chooseWithOutside weight nonnegative
      (MessageNetwork.pendingIds execution.network.pending)).map _ = _
    rw [pending]
    change (MessageNetwork.chooseWithOutside weight nonnegative ∅).map _ = _
    simp only [MessageNetwork.chooseWithOutside, MessageNetwork.inclusionMass,
      Finset.card_empty, Nat.cast_zero, zero_mul, zero_div, mix_zero, PMF.pure_map]
    rfl
  have first : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      execution = PMF.pure waited := by
    rw [fixed_round weight nonnegative players execution waited 8 .wait cursor idle
      (recorded_wait execution)]
    rfl
  have second : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      waited = PMF.pure ticked := by
    rw [fixed_round weight nonnegative players waited ticked 9 (.application .advanceClock)
      waitedCursor rfl (recorded_clock waited)]
    rfl
  obtain ⟨after⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 decision.execution alice
      ⟨none⟩ decision.trace
  have phase := completion_phase_history weight nonnegative ⟨18, none, execution⟩ after
  obtain ⟨inputs, valid⟩ := phase.invariant
  have ready : ticked.application.config.cut.Ready aliceEvent := decision.ready
  obtain ⟨entered, activated⟩ := valid.activatedAt_eq_some_of_ready_actor aliceEvent
    decision.ready rfl
  have zero := phase.aliceTimer entered activated
  have tickedActivated : ticked.application.activatedAt aliceEvent = some 0 := by
    change execution.application.activatedAt aliceEvent = some 0
    exact zero ▸ activated
  have tickedClock : ticked.application.clock = 3 := by
    change decision.execution.application.clock + 1 = 3
    rw [decision_clock]
  let failed := expired ticked ready
  have third : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      ticked = PMF.pure failed := by
    rw [fixed_round weight nonnegative players ticked failed 10
      (.application (.expire aliceEvent)) tickedCursor rfl
        (expired_environment ticked ready tickedActivated tickedClock)]
    rfl
  refine ⟨failed, ?_, expired_store ticked ready, ?_⟩
  · change app.runRounds _ players 3 execution = _
    rw [ReactiveApplication.runRounds, first, PMF.pure_bind,
      ReactiveApplication.runRounds, second, PMF.pure_bind,
      ReactiveApplication.runRounds, third, PMF.pure_bind,
      ReactiveApplication.runRounds]
  · change (ticked.environmentRecall ++ [_]).length = 11
    rw [List.length_append, List.length_singleton, tickedCursor]

theorem silence_terminal_failure (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) (execution : app.Execution)
    (reached : execution ∈ (silentLaw weight nonnegative decision players).support) :
    execution.application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool) := by
  obtain ⟨failed, prefixLaw, failure, _cursor⟩ := silent_prefix weight nonnegative decision players
  unfold silentLaw at reached
  rw [show 18 = 3 + 15 from rfl, ReactiveApplication.runRounds_add, prefixLaw,
    PMF.pure_bind] at reached
  exact (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr aliceEvent)
      (.failure : PublicationResult Bool)) players).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 15 failed execution failure reached

private theorem completed_failure_base_upper {reward : ℝ} (rewardNonnegative : 0 ≤ reward)
    (forfeit : ℝ) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control))
    (failed : control.execution.application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool)) :
    nativeBaseUtility reward forfeit (some control) alice ≤ reward - forfeit := by
  have complete := LateOpeningRuntimeService.completes weight nonnegative control trace terminal
  obtain ⟨bit, label, aliceResult, binding, answer, decoded⟩ := nativeReadout_complete
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      control trace complete
  have base := nativeBaseUtility_of_readout reward forfeit (some control) _ decoded alice
  have storeDecoded : decodeState? (terminalRefs setup.program)
      control.execution.application.config.store =
      some (terminalStateOf bit label aliceResult binding answer) := by
    unfold serviceSourceReadout at decoded
    simpa only [Option.bind_some, ite_eq_left complete] using decoded
  have agreed := decodeState?_agrees _ _ _ storeDecoded alicePublication
  change control.execution.application.config.store (.inr aliceEvent) = some aliceResult at agreed
  rw [failed] at agreed
  cases Option.some.inj agreed
  rw [base, sourceUtility_alice]
  change grossUtility reward _ alice - forfeit ≤ reward - forfeit
  exact sub_le_sub_right (alice_gross_bounds rewardNonnegative _).2 forfeit

theorem silence_payoff_upper (decision : DecisionHistory weight nonnegative)
    (players : Player → app.Policy) {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice) :
    expect (silentLaw weight nonnegative decision players)
      (aliceUtility reward forfeit deposit) ≤ reward - forfeit := by
  apply expect_le_const _ _
    (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative _) _
  intro execution reached
  obtain ⟨after⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 decision.execution alice
      ⟨none⟩ decision.trace
  obtain ⟨trace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 18 _ execution after reached
  have base := completed_failure_base_upper weight nonnegative rewardNonnegative forfeit
    ⟨0, none, execution⟩ trace ⟨rfl, rfl⟩
      (silence_terminal_failure weight nonnegative decision players execution reached)
  change nativeBaseUtility reward forfeit (app.finished execution) alice ≤
    reward - forfeit at base
  have charged := TerminalAudit.charge_mem_Icc
    (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
    (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
      (fun actual => PMF.pure actual)) (app.finished execution) alice
  have penalty := mul_nonneg charged.1 depositNonnegative
  unfold aliceUtility TerminalAudit.utility
  linarith

/-- A genuine opening strictly improves on last-turn silence whenever the
actual failure risk is below the fixed forfeit margin. -/
theorem opening_silence_regret (positive : 0 < weight)
    (decision : DecisionHistory weight nonnegative) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening
      weight nonnegative decision submission) (players alternatives : Player → app.Policy)
    {reward forfeit : ℝ} (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice) :
    forfeit - reward - (1 - inclusionProbability weight) * (forfeit + deposit alice) ≤
      expect (LateOpeningRuntimeAliceOpeningContinuation.openingLaw
        weight nonnegative decision submission players) (aliceUtility reward forfeit deposit) -
      expect (silentLaw weight nonnegative decision alternatives)
        (aliceUtility reward forfeit deposit) := by
  have lower := LateOpeningRuntimeAliceOpeningContinuation.opening_payoff_lower
    weight nonnegative positive decision submission genuine players rewardNonnegative
      forfeitNonnegative deposit depositNonnegative
  have upper := silence_payoff_upper weight nonnegative decision alternatives
    rewardNonnegative forfeitNonnegative deposit depositNonnegative
  linarith

end Vegas.Examples.LateOpeningRuntimeAliceSilentContinuation
