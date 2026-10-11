/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingService
import Interaction.ReactiveTrafficIdentity
import Vegas.Pending.EventOpponentFrame

/-! # Physical stability between protected Bob binding and opening -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeProtectedBobPrefix

open Interaction Vegas.EventGraphRuntime GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobAudit
  LateOpeningRuntimeReadout

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- After Alice and Bob's binding are completed, no previously pending envelope
can complete Bob's opening when Bob's authored traffic consists only of his
accepted canonical binding. This includes arbitrary Alice packets. -/
theorem pending_handle_none (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (aliceCompleted : aliceEvent ∈ control.execution.application.config.cut.completed)
    (bobCompleted : bobBindEvent ∈ control.execution.application.config.cut.completed)
    (clean : CleanBindings control.execution)
    (message : Message Player (WitnessedPacket nativeGraph))
    (pending : message ∈ control.execution.network.pending) :
    app.handle control.execution.application message = none := by
  have member := (app.retained_envelopes_mem_inputs control.execution
    (app.history_provenance initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace)
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace)).pending message pending
  cases handled : app.handle control.execution.application message with
  | none => rfl
  | some next =>
      have base := reactiveHandle_call handled
      by_cases owner : message.sender = bob
      · obtain ⟨token, content, _⟩ := clean message member owner
        have addressed : Payload.event? nativeGraph message.payload.call = some bobBindEvent := by
          rw [content]
          rfl
        have rejected := handle_eq_none_of_completed LateOpeningRuntimeService.runtime
          control.execution.application ⟨message.id, message.payload.call⟩ bobBindEvent
          addressed bobCompleted
        rw [rejected] at base
        cases base
      · have sender : message.sender = alice := by
          have cases (who : Player) : who = alice ∨ who = bob := by
            fin_cases who <;> simp [alice, bob]
          exact (cases message.sender).resolve_right owner
        obtain ⟨event, addressed, actor⟩ := handle_event_actor LateOpeningRuntimeService.runtime
          control.execution.application next ⟨message.id, message.payload.call⟩ base
        change nativeGraph.actor? event = some message.sender at actor
        have eventEq : event = aliceEvent := by
          fin_cases event
          · rfl
          all_goals change some bob = some message.sender at actor
          all_goals rw [sender] at actor
          all_goals exact False.elim ((by decide : some bob ≠ some alice) actor)
        subst event
        have rejected := handle_eq_none_of_completed LateOpeningRuntimeService.runtime
          control.execution.application ⟨message.id, message.payload.call⟩ aliceEvent
          addressed aliceCompleted
        rw [rejected] at base
        cases base

theorem include_application_eq (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (aliceCompleted : aliceEvent ∈ control.execution.application.config.cut.completed)
    (bobCompleted : bobBindEvent ∈ control.execution.application.config.cut.completed)
    (clean : CleanBindings control.execution) (id : MessageId Player) :
    (control.execution.includePending app id).application = control.execution.application := by
  cases found : control.execution.network.lookup id with
  | none => simp [ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, found]
  | some message =>
      have pending := List.mem_of_find?_eq_some found
      have rejected := pending_handle_none weight nonnegative control trace aliceCompleted
        bobCompleted clean message pending
      simp [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, rejected]

private theorem clean_respond_alice (execution : app.Execution) (action : app.Action)
    (clean : CleanBindings execution) : CleanBindings (execution.respond app alice action) := by
  intro message member owner
  cases action with
  | mk transmission =>
      cases transmission with
      | none => exact clean message member owner
      | some material =>
          change message ∈ execution.network.inputs ++ [_] at member
          rcases List.mem_append.mp member with prior | issued
          · exact clean message prior owner
          · cases List.mem_singleton.mp issued
            exact False.elim ((by decide : alice ≠ bob) owner)

private theorem clean_environment (execution next : app.Execution) (command : app.Command)
    (clean : CleanBindings execution)
    (supported : next ∈ (execution.environmentStep app command).support) :
    CleanBindings next := by
  have inputs := app.environmentStep_inputs execution next command supported
  have receipts := app.environmentStep_receipts_prefix execution next command supported
  intro message member owner
  rw [inputs] at member
  obtain ⟨token, content, accepted⟩ := clean message member owner
  exact ⟨token, content, receipts.subset accepted⟩

private theorem prefix_command (execution : app.Execution)
    (late : 6 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length < 11) (command : app.Command)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      execution.environmentRecall (execution.observeEnvironment app)).support) :
    command = .activate alice ∨ command = .application .advanceClock ∨
      command = .application (.expire aliceEvent) ∨ command = .wait ∨
      ∃ id, command = .include id := by
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
    (execution.observeEnvironment app)).support at selected
  generalize execution.environmentRecall.length = cursor at selected late early
  interval_cases cursor
  · cases (PMF.mem_support_pure_iff _ _).mp selected
    exact Or.inr (Or.inl rfl)
  · cases (PMF.mem_support_pure_iff _ _).mp selected
    exact Or.inl rfl
  · unfold stageChoice ReactiveApplication.pendingLotteryScheduler
      ReactiveApplication.Scheduler.ofObservation at selected
    obtain ⟨choice, _, rfl⟩ := PMF.support_map .. ▸ selected
    cases choice with
    | none => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | some id => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨id, rfl⟩)))
  · cases (PMF.mem_support_pure_iff _ _).mp selected
    exact Or.inr (Or.inl rfl)
  · cases (PMF.mem_support_pure_iff _ _).mp selected
    exact Or.inr (Or.inr (Or.inl rfl))

private theorem environment_config_eq (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (aliceCompleted : aliceEvent ∈ control.execution.application.config.cut.completed)
    (bobCompleted : bobBindEvent ∈ control.execution.application.config.cut.completed)
    (clean : CleanBindings control.execution)
    (late : 6 ≤ control.execution.environmentRecall.length)
    (early : control.execution.environmentRecall.length < 11)
    (command : app.Command) (next : app.Execution)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      control.execution.environmentRecall (control.execution.observeEnvironment app)).support)
    (supported : next ∈ (control.execution.environmentStep app command).support) :
    next.application.config = control.execution.application.config := by
  rcases prefix_command weight nonnegative control.execution late early command selected with
    rfl | rfl | rfl | rfl | ⟨id, rfl⟩
  all_goals unfold ReactiveApplication.Execution.environmentStep at supported
  all_goals obtain ⟨updated, changed, rfl⟩ := PMF.support_map .. ▸ supported
  · obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ changed
    rfl
  · obtain ⟨physical, moved, rfl⟩ := PMF.support_map .. ▸ changed
    change physical ∈ (PMF.pure { control.execution.application with
      clock := control.execution.application.clock + 1 }).support at moved
    cases (PMF.mem_support_pure_iff _ _).mp moved
    rfl
  · obtain ⟨physical, moved, rfl⟩ := PMF.support_map .. ▸ changed
    change physical ∈ (environmentStep LateOpeningRuntimeService.runtime
      control.execution.application (.expire aliceEvent)).support at moved
    rw [environmentStep_expire_of_not_ready LateOpeningRuntimeService.runtime
      control.execution.application aliceEvent (fun ready => ready.1 aliceCompleted)] at moved
    cases (PMF.mem_support_pure_iff _ _).mp moved
    rfl
  · cases (PMF.mem_support_pure_iff _ _).mp changed
    rfl
  · cases (PMF.mem_support_pure_iff _ _).mp changed
    exact congrArg (fun physical => physical.config)
      (include_application_eq weight nonnegative control trace aliceCompleted bobCompleted clean id)

/-- Throughout the actual foreign scheduler prefix, Alice's arbitrary raw
responses and every pending-visibility/lottery draw preserve the entire physical
configuration and Bob's accepted-binding traffic. -/
theorem runRounds_config_and_clean (players : Player → app.Policy)
    (count remaining : Nat) (execution final : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining + count, none, execution⟩))
    (aliceCompleted : aliceEvent ∈ execution.application.config.cut.completed)
    (bobCompleted : bobBindEvent ∈ execution.application.config.cut.completed)
    (clean : CleanBindings execution)
    (late : 6 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length + count ≤ 11)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) :
    final.application.config = execution.application.config ∧ CleanBindings final := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rfl, clean⟩
  | succ count ih =>
      obtain ⟨next, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have sourceTrace : (app.protocol initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
            (some ⟨remaining + count + 1, none, execution⟩) := by
        simpa only [Nat.add_assoc] using trace
      obtain ⟨nextTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) players (remaining + count)
        execution next sourceTrace moved
      have length := app.round_environmentRecall_length
        (LateOpeningRuntimeService.scheduler weight nonnegative) players execution next moved
      have cursor : execution.environmentRecall.length < 11 := by omega
      obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨observed, sampled, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have physical := environment_config_eq weight nonnegative
        ⟨remaining + count + 1, none, execution⟩ sourceTrace aliceCompleted bobCompleted
        clean late cursor command observed selected sampled
      have observedClean := clean_environment execution observed command clean sampled
      have actors : command.actor? app = some alice ∨ command.actor? app = none := by
        rcases prefix_command weight nonnegative execution late cursor command selected with
          rfl | rfl | rfl | rfl | ⟨id, rfl⟩ <;> simp [ReactiveApplication.Command.actor?]
      have framed : next.application.config = execution.application.config ∧
          CleanBindings next := by
        rcases actors with alice | passive
        · rw [alice] at resumed
          obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
          exact ⟨(reactive_respond_application LateOpeningRuntimeService.runtime leaks
            observed LateOpeningRuntimeSource.alice response).1.trans physical,
            clean_respond_alice observed response observedClean⟩
        · rw [passive] at resumed
          cases (PMF.mem_support_pure_iff _ _).mp resumed
          exact ⟨physical, observedClean⟩
      have inherited := ih next nextTrace
        (framed.1 ▸ aliceCompleted) (framed.1 ▸ bobCompleted) framed.2
        (by omega) (by omega) continued
      exact ⟨inherited.1.trans framed.1, inherited.2⟩

/-- The early accepted binding reaches the actual clock-three opening callback
with its original configuration intact, even after arbitrary Alice traffic and
all supported observation draws. The opening is genuinely ready and timely. -/
theorem opening_callback_after_binding (players : Player → app.Policy)
    (execution after observed : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨20, none, execution⟩))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (clean : CleanBindings execution)
    (reached : after ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 5 execution).support)
    (sampled : observed ∈ (after.environmentStep app (.activate bob)).support) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, observed⟩)) ∧
      observed.application.config = execution.application.config ∧
        CleanBindings observed ∧ observed.application.config.cut.Ready bobRevealEvent ∧
          observed.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent ∧
            observed.application.clock = 3 := by
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  have cursor : execution.environmentRecall.length = 6 := by
    change execution.environmentRecall.length + 20 = 26 at accounted
    omega
  have framed := runRounds_config_and_clean weight nonnegative players 5 15 execution after trace
    (ready.2 (by decide)) (ready.2 (by decide)) clean (by omega) (by omega) reached
  obtain ⟨afterTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 15 5 execution after
    trace reached
  have afterCursor : after.environmentRecall.length = 11 := by
    have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) afterTrace
    change after.environmentRecall.length + 15 = 26 at accounted
    omega
  have selected : (.activate bob : app.Command) ∈
      (LateOpeningRuntimeService.scheduler weight nonnegative after.environmentRecall
        (after.observeEnvironment app)).support := by
    change _ ∈ (stageChoice weight nonnegative after.environmentRecall.length _).support
    rw [afterCursor]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨observedTrace⟩ := app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 after observed (.activate bob)
    afterTrace selected sampled
  have physical : observed.application = after.application := by
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ sampled
    obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
    rfl
  have configEq := (congrArg (fun state => state.config) physical).trans framed.1
  have observedReady : observed.application.config.cut.Ready bobRevealEvent := configEq ▸ ready
  have clock : observed.application.clock = 3 := by
    rw [physical, clock_history weight nonnegative ⟨15, none, after⟩ afterTrace, afterCursor]
    decide
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
    ⟨14, some bob, observed⟩ observedTrace
  have activated := (valid.activated_iff bobRevealEvent).mpr ⟨observedReady, by decide⟩
  obtain ⟨entered, timer⟩ := Option.isSome_iff_exists.mp activated
  have timely : observed.application.WithinDeadline LateOpeningRuntimeService.runtime
      bobRevealEvent := by
    unfold State.WithinDeadline
    rw [timer]
    change observed.application.clock - entered < 4
    omega
  exact ⟨⟨observedTrace⟩, configEq,
    clean_environment after observed (.activate bob) framed.2 sampled,
    observedReady, timely, clock⟩

/-- A genuine protected first binding survives every foreign raw prefix and
admits its actual accepted canonical opening at Bob's clock-three callback.
The sampled observation and all Alice future policies are unrestricted. -/
theorem early_binding_opening (players : Player → app.Policy) (answer : Answer)
    (execution after observed : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, some bob, execution⟩))
    (quiet : LateOpeningRuntimeBobBindingService.SilentRecall execution)
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (reached : after ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 6 (execution.respond app bob (LateOpeningRuntimeBobSuffix.binding answer))).support)
    (sampled : observed ∈ (after.environmentStep app (.activate bob)).support) :
    ∃ candidate material served,
      Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
          (some ⟨14, some bob, observed⟩)) ∧
      LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob (observed.recall bob)
        (observed.observe app bob) bobRevealEvent true = ⟨some material⟩ ∧
      app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (observed.respond app bob ⟨some material⟩) = PMF.pure served ∧
      served.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
      ((LateOpeningRuntimeBobService.openingMessage observed candidate answer).id, true) ∈
        served.receipts := by
  obtain ⟨bound, service, value, _, openingReady, _, clean, _⟩ :=
    LateOpeningRuntimeBobBindingService.binding_round weight nonnegative 21 execution trace
      quiet ready timely answer
  obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [service players, PMF.mem_support_pure_iff] at moved
  subst middle
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 execution bob
    (LateOpeningRuntimeBobSuffix.binding answer) trace
  obtain ⟨boundTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 20
    (execution.respond app bob (LateOpeningRuntimeBobSuffix.binding answer)) bound respondedTrace
    (by rw [service players]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨⟨observedTrace⟩, configEq, _, observedReady, observedTimely, _⟩ :=
    opening_callback_after_binding weight nonnegative players bound after observed boundTrace
      openingReady clean continued sampled
  have observedValue : observed.application.config.store (.inr bobBindEvent) =
      some (.success answer) := configEq ▸ value
  obtain ⟨candidate, material, served, decision, _, law, output, accepted⟩ :=
    LateOpeningRuntimeBobService.canonical_round weight nonnegative players 14 observed
      observedTrace answer observedValue observedReady observedTimely
  exact ⟨candidate, material, served, ⟨observedTrace⟩, decision, law, output, accepted⟩

end Vegas.Examples.LateOpeningRuntimeProtectedBobPrefix
