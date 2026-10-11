/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingService
import Vegas.Pending.ReactiveServiceOpportunity
import Interaction.ReactiveResponseAccounting

/-! # The actual first ready Bob binding's activation time -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeProtectedBobTiming

open Interaction SourceProgram Vegas Vegas.EventGraph Vegas.EventGraphRuntime
open GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem early_timer_invariant :
    app.ServiceInvariant (LateOpeningRuntimeService.scheduler weight nonnegative)
      (fun execution => Clocked execution ∧
        (execution.environmentRecall.length ≤ 5 →
          ∀ entered, execution.application.activatedAt bobBindEvent = some entered →
            entered = 0)) := by
  constructor
  · intro execution who response valid
    have visible := (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
      execution who response).2
    have timers := congrArg PublicView.activatedAt visible
    change (execution.respond app who response).application.activatedAt =
      execution.application.activatedAt at timers
    refine ⟨(clock_invariant weight nonnegative).respond execution who response valid.1, ?_⟩
    rw [app.respond_environmentRecall]
    rw [timers]
    exact valid.2
  · intro execution next command valid selected moved
    refine ⟨(clock_invariant weight nonnegative).environment execution next command
      valid.1 selected moved, ?_⟩
    have length := app.environmentStep_environmentRecall execution next command moved
    have size : next.environmentRecall.length = execution.environmentRecall.length + 1 := by
      rw [length, List.length_append, List.length_singleton]
    intro early entered activated
    have priorEarly : execution.environmentRecall.length ≤ 4 := by omega
    by_cases beforeTick : execution.environmentRecall.length ≤ 2
    · have clock : execution.application.clock = 0 := by
        rw [valid.1]
        generalize positionEq : execution.environmentRecall.length = position at beforeTick ⊢
        interval_cases position <;> decide
      rcases (LateOpeningRuntimeService.runtime.reactiveActivationStart leaks).environmentStep
        execution next command moved bobBindEvent entered activated with prior | started
      · exact valid.2 (by omega) entered prior
      · exact started.2.trans clock
    · have passive : command = .activate alice ∨ command = .activate bob := by
        change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
          (execution.observeEnvironment app)).support at selected
        have positions : execution.environmentRecall.length = 3 ∨
            execution.environmentRecall.length = 4 := by omega
        rcases positions with position | position
        · rw [position] at selected
          exact Or.inl ((PMF.mem_support_pure_iff _ _).mp selected)
        · rw [position] at selected
          exact Or.inr ((PMF.mem_support_pure_iff _ _).mp selected)
      have physical : next.application = execution.application := by
        rcases passive with rfl | rfl
        all_goals
          obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
          obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
          rfl
      rw [physical] at activated
      exact valid.2 (by omega) entered activated

private theorem early_timer_initial (state : app.State) (supported : state ∈ initial.support) :
    Clocked (ReactiveApplication.Execution.initial app state) ∧
      ((ReactiveApplication.Execution.initial app state).environmentRecall.length ≤ 5 →
        ∀ entered, state.activatedAt bobBindEvent = some entered → entered = 0) := by
  obtain ⟨source, _, rfl⟩ := PMF.support_map .. ▸ supported
  refine ⟨rfl, ?_⟩
  intro _ entered activated
  change (none : Option Nat) = some entered at activated
  cases activated

/-- Actual initialized legal traces at the first Bob callback force time zero
for a ready binding; no assumed activation or successful-source-history premise. -/
theorem early_binding_timer (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent) :
    execution.application.activatedAt bobBindEvent = some 0 := by
  have phase := (early_timer_invariant weight nonnegative).history initial
    LateOpeningRuntimeService.horizon early_timer_initial trace
  have count := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  have cursor : execution.environmentRecall.length = 5 := by
    change execution.environmentRecall.length + 21 = 26 at count
    omega
  obtain ⟨bit, label, valid⟩ := LateOpeningRuntimeReadout.history_initial_invariant
    LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨21, some bob, execution⟩ trace
  obtain ⟨entered, activated⟩ := valid.activatedAt_eq_some_of_ready_actor bobBindEvent ready rfl
  have early : execution.environmentRecall.length ≤ 5 := by rw [cursor]
  rw [phase.2 early entered activated] at activated
  exact activated

end Vegas.Examples.LateOpeningRuntimeProtectedBobTiming
