/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingService
import Vegas.Pending.ReactiveServiceOpportunity
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveStopping

/-! # Quiet Bob reaches a timely first binding against arbitrary Alice play

After Bob's early callback, every later Alice response and every supported
public lottery outcome leads to dependency settlement by clock three. If
Alice was still unresolved and Bob had only answered with silence, his first
binding remains unconsumed and its activation is recent enough for the actual
clock-three callback. Pending syntax and private observation samples are
unrestricted.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobQuietPrefix

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeBobBindingService

private def Allowed : app.Command → Prop
  | .wait | .include _ | .application .advanceClock => True
  | .activate who => who ≠ bob
  | .application (.expire event) => event = aliceEvent
  | _ => False

private theorem allowed_actor (command : app.Command) (allowed : Allowed command) :
    command.actor? app ≠ some bob := by
  cases command with
  | activate who =>
      exact fun same => allowed (Option.some.inj same)
  | wait | «include» id | application command => simp [ReactiveApplication.Command.actor?]

private theorem allowed_before_binding (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution) (position : 5 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length < 11) (command : app.Command)
    (selected : command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      execution.environmentRecall (execution.observeEnvironment app)).support) :
    Allowed command := by
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length _).support
    at selected
  generalize cursorEq : execution.environmentRecall.length = cursor at selected position early
  interval_cases cursor <;> simp only [stageChoice, PMF.mem_support_pure_iff] at selected
  all_goals first
    | solve
      | subst command
        simp only [Allowed] <;> decide
    | solve
      | subst command
        unfold latestAuthor
        split <;> trivial
    | change command ∈ (app.pendingLotteryScheduler weight nonnegative []
        (execution.observeEnvironment app)).support at selected
      rw [ReactiveApplication.pendingLotteryScheduler, PMF.support_map] at selected
      obtain ⟨chosen, _, rfl⟩ := selected
      cases chosen <;> trivial

private theorem silent_pending (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (quiet : SilentRecall control.execution) (message : Message Player app.Payload)
    (pending : message ∈ control.execution.network.pending) : message.sender ≠ bob := by
  have serials := app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler
    weight nonnegative) initial LateOpeningRuntimeService.horizon trace
  have zero := (silent_resources weight nonnegative control trace quiet).1
  intro authored
  have bound := serials.pending message pending
  change message.id.2 < control.execution.network.nextSerial message.sender at bound
  rw [authored, zero] at bound
  omega

private theorem include_completed (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (quiet : SilentRecall control.execution) (id : MessageId Player) :
    bobBindEvent ∈ (control.execution.includePending app id).application.config.cut.completed ↔
      bobBindEvent ∈ control.execution.application.config.cut.completed := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : control.execution.network.lookup id with
  | none => rfl
  | some message =>
      change bobBindEvent ∈
        ((app.handle control.execution.application message).getD
          control.execution.application).config.cut.completed ↔ _
      cases accepted : app.handle control.execution.application message with
      | none => rfl
      | some next =>
          apply handle_opponent_completed_iff LateOpeningRuntimeService.runtime
            control.execution.application next ⟨message.id, message.payload.call⟩
              bobBindEvent bob rfl
              (Ne.symm (silent_pending weight nonnegative control trace quiet message
                (List.mem_of_find?_eq_some found)))
          exact reactiveHandle_call accepted

private theorem environment_completed (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (quiet : SilentRecall control.execution) (next : app.Execution) (command : app.Command)
    (allowed : Allowed command)
    (reached : next ∈ (control.execution.environmentStep app command).support) :
    bobBindEvent ∈ next.application.config.cut.completed ↔
      bobBindEvent ∈ control.execution.application.config.cut.completed := by
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
      exact include_completed weight nonnegative control trace quiet id
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      change updated ∈ ((environmentStep LateOpeningRuntimeService.runtime
        control.execution.application command).map _).support at supported
      rw [PMF.support_map] at supported
      obtain ⟨physical, supported, rfl⟩ := supported
      cases command with
      | advanceClock =>
          cases (PMF.mem_support_pure_iff _ _).mp supported
          rfl
      | executeSample event => cases allowed
      | expire event =>
          change event = aliceEvent at allowed
          subst event
          rcases environmentStep_expire_config_eq_or_mem_step LateOpeningRuntimeService.runtime
            control.execution.application physical aliceEvent supported with same | stepped
          · rw [same]
          · obtain ⟨ready, action, member⟩ := stepped
            rw [EventGraph.Config.step_cut _ _ ready action _ member, EventOrder.Cut.mem_complete]
            simp only [show bobBindEvent ≠ aliceEvent by decide, false_or]

private structure QuietPhase (execution : app.Execution) : Prop where
  quiet : SilentRecall execution
  unfinished : bobBindEvent ∉ execution.application.config.cut.completed
  floor : ∀ entered, execution.application.activatedAt bobBindEvent = some entered → 1 ≤ entered

private theorem quiet_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (position : 5 ≤ control.execution.environmentRecall.length)
    (early : control.execution.environmentRecall.length < 11)
    (phase : QuietPhase control.execution) (next : app.Execution)
    (reached : next ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players control.execution).support) : QuietPhase next := by
  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, supported, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have allowed := allowed_before_binding weight nonnegative control.execution position early
    command selected
  have excluded := allowed_actor command allowed
  have envCompleted := environment_completed weight nonnegative control trace phase.quiet
    middle command allowed supported
  have bobRecord : next.recall bob = control.execution.recall bob := by
    have prior := app.environmentStep_recall control.execution middle command supported
    cases actor : command.actor? app with
    | none =>
        rw [actor] at resumed
        cases (PMF.mem_support_pure_iff _ _).mp resumed
        exact congrFun prior bob
    | some who =>
        have different : bob ≠ who := by intro same; subst who; exact excluded actor
        rw [actor] at resumed
        obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
        rw [app.respond_recall_other middle who bob different response, prior]
  have unfinished : bobBindEvent ∉ next.application.config.cut.completed := by
    have envUnfinished : bobBindEvent ∉ middle.application.config.cut.completed := by
      rw [envCompleted]
      exact phase.unfinished
    cases actor : command.actor? app with
    | none =>
        rw [actor] at resumed
        cases (PMF.mem_support_pure_iff _ _).mp resumed
        exact envUnfinished
    | some who =>
        rw [actor] at resumed
        obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
        rw [(LateOpeningRuntimeService.runtime.reactive_respond_application
          leaks middle who response).1]
        exact envUnfinished
  have lifecycle := completion_phase_history weight nonnegative control trace
  obtain ⟨inputs, valid⟩ := lifecycle.invariant
  have origin := LateOpeningRuntimeService.runtime.reactive_dispatch_activationOrigin leaks
    inputs players control.execution next command valid moved
  have clock : 1 ≤ control.execution.application.clock := by
    rw [clock_history weight nonnegative control trace]
    generalize control.execution.environmentRecall.length = cursor at position early ⊢
    interval_cases cursor <;> decide
  refine ⟨?_, unfinished, ?_⟩
  · intro entry member
    rw [bobRecord] at member
    exact phase.quiet entry member
  · intro entered activated
    rcases origin bobBindEvent entered activated unfinished with kept | born
    · exact phase.floor entered kept
    · exact clock.trans born

private theorem quiet_initial (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, none, execution⟩))
    (unfinished : aliceEvent ∉ execution.application.config.cut.completed)
    (quiet : SilentRecall execution) : QuietPhase execution := by
  have predecessor : aliceEvent ∈ nativeGraph.order.predecessors bobBindEvent := by decide
  have bindingUnfinished : bobBindEvent ∉ execution.application.config.cut.completed := by
    intro done
    exact unfinished (execution.application.config.cut.predecessor_closed done predecessor)
  have lifecycle := completion_phase_history weight nonnegative ⟨21, none, execution⟩ trace
  obtain ⟨inputs, valid⟩ := lifecycle.invariant
  refine ⟨quiet, bindingUnfinished, ?_⟩
  intro entered activated
  have ready := ((valid.activated_iff bobBindEvent).mp (by rw [activated]; rfl)).1
  exact (unfinished (ready.2 predecessor)).elim

private theorem quiet_continue (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (count remaining : Nat) (execution next : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining + count, none, execution⟩))
    (position : 5 ≤ execution.environmentRecall.length)
    (early : execution.environmentRecall.length + count ≤ 11) (phase : QuietPhase execution)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players count execution).support) : QuietPhase next := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact phase
  | succ count ih =>
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have sourceTrace : (app.protocol initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
            (some ⟨remaining + count + 1, none, execution⟩) := by
        simpa only [Nat.add_assoc] using trace
      have middlePhase := quiet_round weight nonnegative players
        ⟨remaining + count + 1, none, execution⟩ sourceTrace position
          (by change execution.environmentRecall.length < 11; omega) phase middle moved
      obtain ⟨middleTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) players (remaining + count)
          execution middle sourceTrace moved
      have length := app.round_environmentRecall_length
        (LateOpeningRuntimeService.scheduler weight nonnegative) players execution middle moved
      exact ih middle middleTrace (by omega) (by omega) middlePhase continued

/-- Every supported continuation from quiet early Bob reaches the binding
boundary with a ready, timely and untouched first answer commitment. Alice's
future policy and every late lottery outcome remain unrestricted. -/
theorem before_binding (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (execution next : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, none, execution⟩))
    (cursor : execution.environmentRecall.length = 5)
    (unfinished : aliceEvent ∉ execution.application.config.cut.completed)
    (quiet : SilentRecall execution)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 6 execution).support) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some ⟨15, none, next⟩)) ∧
      SilentRecall next ∧ next.application.config.cut.Ready bobBindEvent ∧
        next.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent ∧
          next.application.clock = 3 ∧ next.environmentRecall.length = 11 := by
  have preserved := quiet_continue weight nonnegative players 6 15 execution next trace
    (by omega) (by omega) (quiet_initial weight nonnegative execution trace unfinished quiet)
      reached
  obtain ⟨nextTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 15 6 execution next trace
      reached
  have nextCursor : next.environmentRecall.length = 11 := by
    rw [app.runRounds_environmentRecall_length (LateOpeningRuntimeService.scheduler
      weight nonnegative) players 6 execution next reached, cursor]
  have nextClock : next.application.clock = 3 := by
    rw [clock_history weight nonnegative ⟨15, none, next⟩ nextTrace, nextCursor]
    decide
  have lifecycle := completion_phase_history weight nonnegative ⟨15, none, next⟩ nextTrace
  have aliceDone := (lifecycle.afterAlice nextCursor.ge).1
  have ready : next.application.config.cut.Ready bobBindEvent := by
    refine ⟨preserved.unfinished, ?_⟩
    change ({aliceEvent} : Finset nativeGraph.EventId) ⊆ next.application.config.cut.completed
    exact Finset.singleton_subset_iff.mpr aliceDone
  obtain ⟨inputs, valid⟩ := lifecycle.invariant
  obtain ⟨entered, activated⟩ := valid.activatedAt_eq_some_of_ready_actor bobBindEvent ready rfl
  have lower := preserved.floor entered activated
  have timely : next.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent := by
    unfold State.WithinDeadline
    rw [activated]
    change next.application.clock - entered < 3
    rw [nextClock]
    omega
  exact ⟨⟨nextTrace⟩, preserved.quiet, ready, timely, nextClock, nextCursor⟩

/-- The actual clock-three Bob activation inherits this opportunity at every
supported private sample. Its bounded fuel and raw trace are proved. -/
theorem binding_activation (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (execution before observed : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, none, execution⟩))
    (cursor : execution.environmentRecall.length = 5)
    (unfinished : aliceEvent ∉ execution.application.config.cut.completed)
    (quiet : SilentRecall execution)
    (reached : before ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 6 execution).support)
    (sampled : observed ∈ (before.environmentStep app (.activate bob)).support) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, observed⟩)) ∧
      SilentRecall observed ∧ observed.application.config.cut.Ready bobBindEvent ∧
        observed.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent ∧
          observed.application.clock = 3 ∧ observed.environmentRecall.length = 12 := by
  obtain ⟨⟨beforeTrace⟩, beforeQuiet, ready, timely, clock, position⟩ := before_binding weight
    nonnegative players execution before trace cursor unfinished quiet reached
  have selected : (.activate bob : app.Command) ∈ (LateOpeningRuntimeService.scheduler weight
      nonnegative before.environmentRecall (before.observeEnvironment app)).support := by
    change _ ∈ (stageChoice weight nonnegative before.environmentRecall.length _).support
    rw [position]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨observedTrace⟩ := app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 before observed (.activate bob)
      beforeTrace selected sampled
  have sameRecord := app.environmentStep_recall before observed (.activate bob) sampled
  have samePhysical : observed.application = before.application := by
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ sampled
    obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
    rfl
  refine ⟨⟨observedTrace⟩, ?_, samePhysical ▸ ready, samePhysical ▸ timely,
    samePhysical ▸ clock, ?_⟩
  · intro entry member
    rw [sameRecord] at member
    exact beforeQuiet entry member
  · obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ sampled
    change (before.environmentRecall ++ [_]).length = 12
    rw [List.length_append, List.length_singleton, position]

end Vegas.Examples.LateOpeningRuntimeBobQuietPrefix
