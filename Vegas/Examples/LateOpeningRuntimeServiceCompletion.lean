/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeServiceClock
import Vegas.Pending.ReactiveStateInvariant

/-! # The padded public scheduler completes every raw execution

Expiry forces Alice's publication by clock three, Bob's binding by clock six,
and Bob's publication by clock ten. Earlier accepted calls can only advance
these milestones. The proof allows arbitrary raw player submissions throughout.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeService

open SourceProgram EventGraph EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource

private theorem alice_ready (state : EventGraphRuntime.State nativeGraph)
    (unfinished : aliceEvent ∉ state.config.cut.completed) : state.config.cut.Ready aliceEvent := by
  refine ⟨unfinished, ?_⟩
  change ∅ ⊆ state.config.cut.completed
  exact Finset.empty_subset _

private theorem binding_ready (state : EventGraphRuntime.State nativeGraph)
    (aliceDone : aliceEvent ∈ state.config.cut.completed)
    (unfinished : bobBindEvent ∉ state.config.cut.completed) :
    state.config.cut.Ready bobBindEvent := by
  refine ⟨unfinished, ?_⟩
  intro predecessor earlier
  fin_cases predecessor
  · exact aliceDone
  · exact ((by decide : (1 : Fin 3) ∉ nativeGraph.order.predecessors bobBindEvent) earlier).elim
  · exact ((by decide : (2 : Fin 3) ∉ nativeGraph.order.predecessors bobBindEvent) earlier).elim

private theorem answer_ready (state : EventGraphRuntime.State nativeGraph)
    (aliceDone : aliceEvent ∈ state.config.cut.completed)
    (bindingDone : bobBindEvent ∈ state.config.cut.completed)
    (unfinished : bobRevealEvent ∉ state.config.cut.completed) :
    state.config.cut.Ready bobRevealEvent := by
  refine ⟨unfinished, ?_⟩
  intro predecessor earlier
  fin_cases predecessor
  · exact aliceDone
  · exact bindingDone
  · exact ((by decide : (2 : Fin 3) ∉ nativeGraph.order.predecessors bobRevealEvent) earlier).elim

private theorem application_support (execution next : app.Execution)
    (command : EnvironmentCommand nativeGraph)
    (reached : next ∈ (execution.environmentStep app (.application command)).support) :
    next.application ∈ (environmentStep runtime execution.application command).support := by
  rw [ReactiveApplication.Execution.environmentStep, PMF.support_map] at reached
  obtain ⟨updated, supported, rfl⟩ := reached
  change updated ∈ ((environmentStep runtime execution.application command).map
    (fun state => { execution with application := state })).support at supported
  rw [PMF.support_map] at supported
  obtain ⟨state, supported, rfl⟩ := supported
  exact supported

private theorem recall_append (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] := by
  obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ reached
  rfl

structure CompletedPhase (execution : app.Execution) : Prop where
  invariant : ∃ inputs, execution.application.Invariant inputs
  clocked : Clocked execution
  aliceTimer : ∀ entered, execution.application.activatedAt aliceEvent = some entered → entered = 0
  afterAlice : 11 ≤ execution.environmentRecall.length →
    aliceEvent ∈ execution.application.config.cut.completed ∧
      ∀ entered, execution.application.activatedAt bobBindEvent = some entered → entered ≤ 3
  afterBinding : 19 ≤ execution.environmentRecall.length →
    bobBindEvent ∈ execution.application.config.cut.completed ∧
      ∀ entered, execution.application.activatedAt bobRevealEvent = some entered → entered ≤ 6
  afterAnswer : 26 ≤ execution.environmentRecall.length →
    bobRevealEvent ∈ execution.application.config.cut.completed

private theorem timer_bound_retained {inputs : nativeGraph.Inputs}
    {before after : EventGraphRuntime.State nativeGraph} {ticks : Nat}
    (progress : State.ServiceProgress inputs ticks before after)
    (invariant : before.Invariant inputs) (event : nativeGraph.EventId)
    (ready : before.config.cut.Ready event) (strategic : (nativeGraph.actor? event).isSome = true)
    {cap : Nat} (bound : ∀ entered, before.activatedAt event = some entered → entered ≤ cap)
    (entered : Nat) (activated : after.activatedAt event = some entered) : entered ≤ cap := by
  obtain ⟨prior, earlier⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready strategic
  have afterReady := ((progress.invariant.activated_iff event).mp (by rw [activated]; rfl)).1
  have kept := progress.activated event prior earlier afterReady.1
  have same := Option.some.inj (kept.symm.trans activated)
  exact same ▸ bound prior earlier

theorem completion_invariant (weight : ℝ) (nonnegative : 0 ≤ weight) :
    app.ServiceInvariant (scheduler weight nonnegative) CompletedPhase where
  respond execution who action valid := by
    obtain ⟨inputs, invariant⟩ := valid.invariant
    have progress := runtime.reactive_respond_progress leaks inputs execution who action invariant
    obtain ⟨config, visible⟩ := runtime.reactive_respond_application leaks execution who action
    have timers := congrArg PublicView.activatedAt visible
    change (execution.respond app who action).application.activatedAt =
      execution.application.activatedAt at timers
    refine ⟨⟨inputs, progress.invariant⟩,
      (clock_invariant weight nonnegative).respond execution who action valid.clocked,
      ?_, ?_, ?_, ?_⟩
    · rw [timers]
      exact valid.aliceTimer
    · rw [app.respond_environmentRecall, config, timers]
      exact valid.afterAlice
    · rw [app.respond_environmentRecall, config, timers]
      exact valid.afterBinding
    · rw [app.respond_environmentRecall, config]
      exact valid.afterAnswer
  environment execution next command valid selected reached := by
    obtain ⟨inputs, invariant⟩ := valid.invariant
    have progress := runtime.reactive_environment_progress leaks inputs execution next command
      invariant reached
    have clocked := (clock_invariant weight nonnegative).environment execution next command
      valid.clocked selected reached
    have length : next.environmentRecall.length = execution.environmentRecall.length + 1 := by
      rw [recall_append execution next command reached, List.length_append, List.length_singleton]
    have afterClock : next.application.clock = clockAt (execution.environmentRecall.length + 1) :=
      clocked.trans (congrArg clockAt length)
    have beforeClock : execution.application.clock = clockAt execution.environmentRecall.length :=
      valid.clocked
    have beforeUnfinished (event : nativeGraph.EventId) (entered : Nat)
        (activated : next.application.activatedAt event = some entered) :
        event ∉ execution.application.config.cut.completed := by
      have ready := ((progress.invariant.activated_iff event).mp (by rw [activated]; rfl)).1
      exact fun done => ready.1 (progress.completed done)
    have aliceTimer : ∀ entered, next.application.activatedAt aliceEvent = some entered →
        entered = 0 := by
      intro entered activated
      have ready := alice_ready execution.application
        (beforeUnfinished aliceEvent entered activated)
      have cap := timer_bound_retained progress invariant aliceEvent ready rfl
        (fun prior earlier => (valid.aliceTimer prior earlier).le) entered activated
      omega
    have afterAlice : 11 ≤ next.environmentRecall.length →
        aliceEvent ∈ next.application.config.cut.completed ∧
          ∀ entered, next.application.activatedAt bobBindEvent = some entered → entered ≤ 3 := by
      intro late
      by_cases prior : 11 ≤ execution.environmentRecall.length
      · obtain ⟨done, cap⟩ := valid.afterAlice prior
        refine ⟨progress.completed done, ?_⟩
        intro entered activated
        exact timer_bound_retained progress invariant bobBindEvent
          (binding_ready execution.application done
            (beforeUnfinished bobBindEvent entered activated))
          rfl cap entered activated
      · have position : execution.environmentRecall.length = 10 := by omega
        have expireCommand : command = .application (.expire aliceEvent) := by
          change command ∈ (stageChoice weight nonnegative
            execution.environmentRecall.length
            (execution.observeEnvironment app)).support at selected
          rw [position] at selected
          exact (PMF.mem_support_pure_iff _ _).mp selected
        have done : aliceEvent ∈ next.application.config.cut.completed := by
          by_cases finished : aliceEvent ∈ execution.application.config.cut.completed
          · exact progress.completed finished
          · obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor aliceEvent
              (alice_ready execution.application finished) rfl
            have zero := valid.aliceTimer entered activated
            have clock : execution.application.clock = 3 := by
              simpa only [position, show clockAt 10 = 3 by decide] using beforeClock
            exact environmentStep_expire_complete runtime execution.application next.application
              aliceEvent (alice_ready execution.application finished) rfl entered activated
              (by change 3 ≤ execution.application.clock - entered; omega)
              (application_support execution next _ (expireCommand ▸ reached))
        refine ⟨done, ?_⟩
        intro entered activated
        have clock : next.application.clock = 3 := by
          simpa [position, show clockAt 11 = 3 by decide] using afterClock
        exact (progress.invariant.activated_le bobBindEvent entered activated).trans clock.le
    have afterBinding : 19 ≤ next.environmentRecall.length →
        bobBindEvent ∈ next.application.config.cut.completed ∧
          ∀ entered, next.application.activatedAt bobRevealEvent = some entered → entered ≤ 6 := by
      intro late
      by_cases prior : 19 ≤ execution.environmentRecall.length
      · obtain ⟨done, cap⟩ := valid.afterBinding prior
        have aliceDone := (valid.afterAlice (by omega)).1
        refine ⟨progress.completed done, ?_⟩
        intro entered activated
        exact timer_bound_retained progress invariant bobRevealEvent
          (answer_ready execution.application aliceDone done
            (beforeUnfinished bobRevealEvent entered activated)) rfl cap entered activated
      · have position : execution.environmentRecall.length = 18 := by omega
        obtain ⟨aliceDone, cap⟩ := valid.afterAlice (by omega)
        have expireCommand : command = .application (.expire bobBindEvent) := by
          change command ∈ (stageChoice weight nonnegative
            execution.environmentRecall.length
            (execution.observeEnvironment app)).support at selected
          rw [position] at selected
          exact (PMF.mem_support_pure_iff _ _).mp selected
        have done : bobBindEvent ∈ next.application.config.cut.completed := by
          by_cases finished : bobBindEvent ∈ execution.application.config.cut.completed
          · exact progress.completed finished
          · have ready := binding_ready execution.application aliceDone finished
            obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor bobBindEvent
              ready rfl
            have upper := cap entered activated
            have clock : execution.application.clock = 6 := by
              simpa only [position, show clockAt 18 = 6 by decide] using beforeClock
            exact environmentStep_expire_complete runtime execution.application next.application
              bobBindEvent ready rfl entered activated
              (by change 3 ≤ execution.application.clock - entered; omega)
              (application_support execution next _ (expireCommand ▸ reached))
        refine ⟨done, ?_⟩
        intro entered activated
        have clock : next.application.clock = 6 := by
          simpa [position, show clockAt 19 = 6 by decide] using afterClock
        exact (progress.invariant.activated_le bobRevealEvent entered activated).trans clock.le
    refine ⟨⟨inputs, progress.invariant⟩, clocked, aliceTimer, afterAlice, afterBinding, ?_⟩
    intro late
    by_cases prior : 26 ≤ execution.environmentRecall.length
    · exact progress.completed (valid.afterAnswer prior)
    · have position : execution.environmentRecall.length = 25 := by omega
      have aliceDone := (valid.afterAlice (by omega)).1
      obtain ⟨bindingDone, cap⟩ := valid.afterBinding (by omega)
      have expireCommand : command = .application (.expire bobRevealEvent) := by
        change command ∈ (stageChoice weight nonnegative
          execution.environmentRecall.length (execution.observeEnvironment app)).support at selected
        rw [position] at selected
        exact (PMF.mem_support_pure_iff _ _).mp selected
      by_cases finished : bobRevealEvent ∈ execution.application.config.cut.completed
      · exact progress.completed finished
      · have ready := answer_ready execution.application aliceDone bindingDone finished
        obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor bobRevealEvent
          ready rfl
        have upper := cap entered activated
        have clock : execution.application.clock = 10 := by
          simpa only [position, show clockAt 25 = 10 by decide] using beforeClock
        exact environmentStep_expire_complete runtime execution.application next.application
          bobRevealEvent ready rfl entered activated
          (by change 4 ≤ execution.application.clock - entered; omega)
          (application_support execution next _ (expireCommand ▸ reached))

private theorem phase_initial (state : app.State) (supported : state ∈ initial.support) :
    CompletedPhase (ReactiveApplication.Execution.initial app state) := by
  obtain ⟨source, _, rfl⟩ := PMF.support_map .. ▸ supported
  refine ⟨⟨setup.eventInputs source, State.initial_invariant _⟩, rfl, ?_, ?_, ?_, ?_⟩
  · intro entered activated
    change some 0 = some entered at activated
    exact (Option.some.inj activated).symm
  all_goals intro impossible; change _ ≤ 0 at impossible; omega

theorem completion_phase_history (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace (some control)) :
    CompletedPhase control.execution :=
  (completion_invariant weight nonnegative).history initial horizon phase_initial trace

private def CommandBudget : app.ProtocolState → Prop
  | none => True
  | some control => control.remaining + control.execution.environmentRecall.length = horizon

private theorem command_budget_history (weight : ℝ) (nonnegative : 0 ≤ weight) :
    ∀ {state} (_trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace state),
      CommandBudget state
  | _, .start => trivial
  | _, @ExecutionProtocol.Trace.extend _ _ source target prior joint legal reached => by
      have counted := command_budget_history weight nonnegative prior
      change target ∈ (app.transition initial horizon (scheduler weight nonnegative)
        source joint).support at reached
      cases source with
      | none =>
          obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
          rfl
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              simpa only [CommandBudget, app.respond_environmentRecall] using counted
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have length : next.environmentRecall.length =
                      execution.environmentRecall.length + 1 := by
                    rw [recall_append execution next command supported,
                      List.length_append, List.length_singleton]
                  change remaining + next.environmentRecall.length = horizon
                  change remaining + 1 + execution.environmentRecall.length = horizon at counted
                  omega

theorem command_budget (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial horizon (scheduler weight nonnegative)).Trace (some control)) :
    control.remaining + control.execution.environmentRecall.length = horizon :=
  command_budget_history weight nonnegative trace

/-- Every legal terminal execution has completed all three events, even when
the players submit arbitrary malformed calls, duplicates or private material. -/
theorem completes (weight : ℝ) (nonnegative : 0 ≤ weight) :
    runtime.CompletesPlay leaks initial horizon (scheduler weight nonnegative) := by
  intro control trace stopped
  have phase := completion_phase_history weight nonnegative control trace
  have budget := command_budget weight nonnegative control trace
  change control.remaining = 0 ∧ control.actor = none at stopped
  rw [stopped.1, Nat.zero_add] at budget
  change control.execution.environmentRecall.length = 26 at budget
  have aliceDone := (phase.afterAlice (by omega)).1
  have bindingDone := (phase.afterBinding (by omega)).1
  have answerDone := phase.afterAnswer (by omega)
  apply Finset.eq_univ_iff_forall.mpr
  intro event
  change Fin 3 at event
  fin_cases event
  · exact aliceDone
  · exact bindingDone
  · exact answerDone

end Vegas.Examples.LateOpeningRuntimeService
