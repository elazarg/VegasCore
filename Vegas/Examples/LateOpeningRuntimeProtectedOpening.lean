/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLatePrefix
import Vegas.Examples.LateOpeningRuntimeServiceCompletion
import Vegas.Pending.EventOpponentFrame
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveStopping

/-! # Almost-sure disclosure requires the protected opening

The finite-weight public lottery always has a supported outside option,
regardless of pending-pool contents. After missing protected inclusion, an
arbitrary raw continuation therefore has a supported branch on which Alice's
opening expires. This obstruction concerns every raw policy, not only the
canonical late timing examples.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeProtectedOpening

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
open LateOpeningRuntimeLatePrefix

private def SafeBeforeLottery : app.Command → Prop
  | .wait | .activate _ | .application .advanceClock => True
  | .include id => id.1 = bob
  | _ => False

private theorem latestAuthor_safe (view : app.EnvironmentView) :
    SafeBeforeLottery (latestAuthor bob view) := by
  unfold latestAuthor
  split
  · trivial
  · rename_i message found
    have selected := (List.find?_eq_some_iff_append.mp found).1
    exact (of_decide_eq_true selected).1

private theorem before_lottery_safe (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution) (position : 2 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length < 8) (command : app.Command)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      execution.environmentRecall
      (execution.observeEnvironment app)).support) : SafeBeforeLottery command := by
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
    (execution.observeEnvironment app)).support at selected
  generalize cursorEq : execution.environmentRecall.length = cursor at selected position early
  interval_cases cursor <;> simp only [stageChoice, PMF.mem_support_pure_iff] at selected
  all_goals subst command
  all_goals first | exact latestAuthor_safe _ | trivial

private theorem include_opponent_completed (execution : app.Execution) (id : MessageId Player)
    (authored : id.1 = bob) :
    aliceEvent ∈ (execution.includePending app id).application.config.cut.completed ↔
      aliceEvent ∈ execution.application.config.cut.completed := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => rfl
  | some message =>
      change aliceEvent ∈
        ((app.handle execution.application message).getD execution.application).config.cut.completed
          ↔ _
      cases accepted : app.handle execution.application message with
      | none => rfl
      | some next =>
          have identified : message.id = id := by
            exact of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
          apply handle_opponent_completed_iff LateOpeningRuntimeService.runtime
            execution.application next
            ⟨message.id, message.payload.call⟩ aliceEvent alice rfl
              (by simp only [Message.sender, identified, authored]; decide)
          exact reactiveHandle_call accepted

private theorem safe_environment_completed (execution next : app.Execution)
    (command : app.Command) (safe : SafeBeforeLottery command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    aliceEvent ∈ next.application.config.cut.completed ↔
      aliceEvent ∈ execution.application.config.cut.completed := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨sampled, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact include_opponent_completed execution id safe
  | application command =>
      cases command with
      | advanceClock =>
          rw [recorded_clock] at reached
          cases (PMF.mem_support_pure_iff _ _).mp reached
          rfl
      | executeSample event => cases safe
      | expire event => cases safe

private theorem resume_completed (players : Player → app.Policy) (actor : Option Player)
    (execution next : app.Execution)
    (reached : next ∈ (app.resume players actor execution).support) :
    aliceEvent ∈ next.application.config.cut.completed ↔
      aliceEvent ∈ execution.application.config.cut.completed := by
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | some who =>
      obtain ⟨action, _, rfl⟩ := PMF.support_map .. ▸ reached
      rw [(LateOpeningRuntimeService.runtime.reactive_respond_application
        leaks execution who action).1]

private theorem before_lottery_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (execution next : app.Execution)
    (position : 2 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length < 8)
    (reached : next ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players execution).support) :
    aliceEvent ∈ next.application.config.cut.completed ↔
      aliceEvent ∈ execution.application.config.cut.completed := by
  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, supported, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  exact (resume_completed players _ middle next resumed).trans
    (safe_environment_completed execution middle command
      (before_lottery_safe weight nonnegative execution position early command selected) supported)

/-- Arbitrary submissions and intervening Bob service cannot repair Alice's
miss before the public late lottery. -/
theorem before_lottery_completed (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (count : Nat) (execution next : app.Execution)
    (position : 2 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length + count ≤ 8)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) :
    aliceEvent ∈ next.application.config.cut.completed ↔
      aliceEvent ∈ execution.application.config.cut.completed := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      have length : middle.environmentRecall.length = execution.environmentRecall.length + 1 := by
        rw [app.dispatch_environmentRecall players command execution middle dispatched,
          List.length_append, List.length_singleton]
      have framed := before_lottery_round weight nonnegative players execution middle position
        (by omega) moved
      exact (ih middle (by omega) (by omega) continued).trans framed

/-- The actual all-identifier lottery can select nothing for every finite
pending pool and every finite nonnegative inclusion weight. -/
theorem lottery_wait_supported (weight : ℝ) (nonnegative : 0 ≤ weight)
    (view : app.EnvironmentView) :
    (.wait : app.Command) ∈ (app.pendingLotteryScheduler weight nonnegative [] view).support := by
  rw [ReactiveApplication.pendingLotteryScheduler, PMF.support_map]
  refine ⟨none, ?_, rfl⟩
  have positive : 0 < ((MessageNetwork.chooseWithOutside weight nonnegative
      (MessageNetwork.pendingIds view.network.pending)) none).toReal := by
    rw [MessageNetwork.chooseWithOutside_none_toReal]
    positivity
  by_contra absent
  rw [(pmf_toReal_eq_zero_iff).mpr absent] at positive
  exact (lt_irrefl 0) positive

private theorem alice_ready (state : app.State)
    (unfinished : aliceEvent ∉ state.config.cut.completed) : state.config.cut.Ready aliceEvent := by
  refine ⟨unfinished, ?_⟩
  change ∅ ⊆ state.config.cut.completed
  exact Finset.empty_subset _

private theorem passive_round_supported (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (execution next : app.Execution) (command : app.Command)
    (passive : command.actor? app = none)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      execution.environmentRecall (execution.observeEnvironment app)).support)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players execution).support := by
  rw [ReactiveApplication.round, PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨command, selected, ?_⟩
  rw [ReactiveApplication.dispatch, PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨next, reached, ?_⟩
  rw [passive]
  change next ∈ (PMF.pure next).support
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

def expired (execution : app.Execution)
    (ready : execution.application.config.cut.Ready aliceEvent) : app.Execution :=
  recorded execution (.application (.expire aliceEvent))
    (execution.application.complete aliceEvent ready false (.failure : PublicationResult Bool))

theorem expired_environment (execution : app.Execution)
    (ready : execution.application.config.cut.Ready aliceEvent)
    (activated : execution.application.activatedAt aliceEvent = some 0)
    (clock : execution.application.clock = 3) :
    execution.environmentStep app (.application (.expire aliceEvent)) =
      PMF.pure (expired execution ready) := by
  have law := environmentStep_expire_resolve_eq LateOpeningRuntimeService.runtime
    execution.application aliceEvent ready 0 activated (by change 3 ≤ _ - 0; omega)
      alice .bool aliceBinding [] rfl rfl rfl
  rw [ReactiveApplication.Execution.environmentStep]
  change ((environmentStep LateOpeningRuntimeService.runtime execution.application
    (.expire aliceEvent)).map _).map _ = _
  rw [law, PMF.pure_map, PMF.pure_map]
  rfl

theorem expired_store (execution : app.Execution)
    (ready : execution.application.config.cut.Ready aliceEvent) :
    (expired execution ready).application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool) := by
  change (execution.application.config.complete aliceEvent ready false
    (.failure : PublicationResult Bool)).store (.inr aliceEvent) = _
  rw [EventGraph.Config.store_output, EventGraph.Config.complete_output_same]

/-- At the actual lottery cursor, every unresolved raw history has a
supported three-command continuation storing Alice's publication failure.
The selected player policies and pending-pool contents are unrestricted. -/
theorem lottery_miss_expires (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler
      weight nonnegative)).Trace (some ⟨18, none, execution⟩))
    (cursor : execution.environmentRecall.length = 8)
    (unfinished : aliceEvent ∉ execution.application.config.cut.completed) :
    ∃ failed, failed ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 3 execution).support ∧
      failed.application.config.store (.inr aliceEvent) = some (.failure : PublicationResult Bool) ∧
      failed.environmentRecall.length = 11 := by
  let waited := recorded execution .wait execution.application
  let ticked := recorded waited (.application .advanceClock)
    { waited.application with clock := waited.application.clock + 1 }
  have waitedCursor : waited.environmentRecall.length = 9 := by
    change (execution.environmentRecall ++ [_]).length = 9
    rw [List.length_append, List.length_singleton, cursor]
  have tickedCursor : ticked.environmentRecall.length = 10 := by
    change (waited.environmentRecall ++ [_]).length = 10
    rw [List.length_append, List.length_singleton, waitedCursor]
  have waitSelected : (.wait : app.Command) ∈ (LateOpeningRuntimeService.scheduler
      weight nonnegative execution.environmentRecall
        (execution.observeEnvironment app)).support := by
    change .wait ∈ (stageChoice weight nonnegative execution.environmentRecall.length _).support
    rw [cursor]
    exact lottery_wait_supported weight nonnegative _
  have waitReached : waited ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players execution).support := by
    apply passive_round_supported weight nonnegative players execution waited .wait rfl waitSelected
    rw [recorded_wait]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have tickSelected : (.application .advanceClock : app.Command) ∈
      (LateOpeningRuntimeService.scheduler weight nonnegative waited.environmentRecall
        (waited.observeEnvironment app)).support := by
    change _ ∈ (stageChoice weight nonnegative waited.environmentRecall.length _).support
    rw [waitedCursor]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have tickReached : ticked ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players waited).support := by
    apply passive_round_supported weight nonnegative players waited ticked _ rfl tickSelected
    rw [recorded_clock]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have phase := completion_phase_history weight nonnegative ⟨18, none, execution⟩ trace
  have ready : ticked.application.config.cut.Ready aliceEvent := alice_ready _ unfinished
  obtain ⟨inputs, valid⟩ := phase.invariant
  obtain ⟨entered, activated⟩ := valid.activatedAt_eq_some_of_ready_actor aliceEvent
    (alice_ready _ unfinished) rfl
  have zero := phase.aliceTimer entered activated
  have tickedActivated : ticked.application.activatedAt aliceEvent = some 0 := by
    change execution.application.activatedAt aliceEvent = some 0
    exact zero ▸ activated
  have tickedClock : ticked.application.clock = 3 := by
    have clock : execution.application.clock = 2 := by
      simpa only [Clocked, cursor, show LateOpeningRuntimeService.clockAt 8 = 2 by decide]
        using phase.clocked
    change execution.application.clock + 1 = 3
    omega
  let failed := expired ticked ready
  have expireSelected : (.application (.expire aliceEvent) : app.Command) ∈
      (LateOpeningRuntimeService.scheduler weight nonnegative ticked.environmentRecall
        (ticked.observeEnvironment app)).support := by
    change _ ∈ (stageChoice weight nonnegative ticked.environmentRecall.length _).support
    rw [tickedCursor]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have expireReached : failed ∈
      (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
        players ticked).support := by
    apply passive_round_supported weight nonnegative players ticked failed _ rfl expireSelected
    rw [expired_environment ticked ready tickedActivated tickedClock]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  refine ⟨failed, ?_, expired_store ticked ready, ?_⟩
  · simp only [ReactiveApplication.runRounds, PMF.bind_pure, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨waited, waitReached,
      Set.mem_iUnion₂.mpr ⟨ticked, tickReached, expireReached⟩⟩
  · change (ticked.environmentRecall ++ [_]).length = 11
    rw [List.length_append, List.length_singleton, tickedCursor]

/-- Every actual protected-inclusion miss admits a supported terminal failure
under every later raw policy. No lower bound on its probability is assumed. -/
theorem protected_miss_terminal_failure (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨24, none, execution⟩))
    (cursor : execution.environmentRecall.length = 2)
    (unfinished : aliceEvent ∉ execution.application.config.cut.completed) :
    ∃ terminal, terminal ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 24 execution).support ∧
      terminal.application.config.store (.inr aliceEvent) = some (.failure : PublicationResult Bool)
        ∧ terminal.environmentRecall.length = LateOpeningRuntimeService.horizon := by
  let builder := LateOpeningRuntimeService.scheduler weight nonnegative
  obtain ⟨lottery, reachedLottery⟩ := (app.runRounds builder players 6 execution).support_nonempty
  have lotteryCursor : lottery.environmentRecall.length = 8 := by
    rw [app.runRounds_environmentRecall_length builder players 6 execution lottery reachedLottery,
      cursor]
  have lotteryUnfinished : aliceEvent ∉ lottery.application.config.cut.completed := by
    rw [before_lottery_completed weight nonnegative players 6 execution lottery
      (by omega) (by omega) reachedLottery]
    exact unfinished
  obtain ⟨lotteryTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    builder players 18 6 execution lottery trace reachedLottery
  obtain ⟨failed, reachedFailure, failure, failureCursor⟩ := lottery_miss_expires weight
    nonnegative players lottery lotteryTrace lotteryCursor lotteryUnfinished
  obtain ⟨terminal, reachedTerminal⟩ := (app.runRounds builder players 15 failed).support_nonempty
  have terminalFailure := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr aliceEvent)
      (.failure : PublicationResult Bool)) players).runRounds builder 15 failed terminal
        failure reachedTerminal
  refine ⟨terminal, ?_, terminalFailure, ?_⟩
  · change terminal ∈ (app.runRounds builder players (6 + (3 + 15)) execution).support
    rw [ReactiveApplication.runRounds_add, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨lottery, reachedLottery, ?_⟩
    rw [ReactiveApplication.runRounds_add, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨failed, reachedFailure, reachedTerminal⟩
  · rw [app.runRounds_environmentRecall_length builder players 15 failed terminal reachedTerminal,
      failureCursor]

def aliceSucceeded (execution : app.Execution) : Bool :=
  match execution.application.config.store (.inr aliceEvent) with
  | none => false
  | some result => result.isSuccess

private theorem roundsFrom_split (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) :
    app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative) players 26 =
      (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
        players 2).bind (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          players 24) := by
  unfold ReactiveApplication.roundsFrom
  rw [PMF.bind_bind]
  apply bind_congr_on_support
  intro state _
  exact ReactiveApplication.runRounds_add app _ players 2 24 _

/-- Almost-sure terminal Alice success forces her opening to have completed
at the protected inclusion cursor. This holds for unrestricted raw policies. -/
theorem almost_sure_success_forces_protected_completion (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy)
    (success : (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 26).map aliceSucceeded = PMF.pure true)
    (execution : app.Execution)
    (reached : execution ∈ (app.roundsFrom initial
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 2).support) :
    aliceEvent ∈ execution.application.config.cut.completed := by
  by_contra unfinished
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 2 (by decide) execution reached
  have cursor := app.roundsFrom_recall initial (LateOpeningRuntimeService.scheduler
    weight nonnegative) players 2 execution reached
  obtain ⟨terminal, continued, failure, _⟩ := protected_miss_terminal_failure weight nonnegative
    players execution trace cursor unfinished
  have terminalReached : terminal ∈ (app.roundsFrom initial
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 26).support := by
    rw [roundsFrom_split, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨execution, reached, continued⟩
  have succeeded : aliceSucceeded terminal ∈ ((app.roundsFrom initial
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 26).map
        aliceSucceeded).support :=
    (PMF.support_map ..).symm ▸ ⟨terminal, terminalReached, rfl⟩
  rw [success, PMF.mem_support_pure_iff] at succeeded
  simp only [aliceSucceeded, failure, PublicationResult.isSuccess] at succeeded
  cases succeeded

end Vegas.Examples.LateOpeningRuntimeProtectedOpening
