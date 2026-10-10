/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobFreshBinding
import Vegas.Examples.LateOpeningRuntimeBobBindingInformation

/-! # Full native information fibers at the first receiver binding

Every compatible legal history has the same own recall and native view and
remains at the same ready binding callback. Earlier receiver responses are
unrestricted, including at histories assigned zero belief.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingFiber

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
open LateOpeningRuntimeBobBindingInformation
  (alice_result_same_view ready_same_view timely_same_view)

/-- Every compatible history is at the actual first binding callback,
including histories with earlier non-silent receiver responses. -/
theorem binding_history_same_information (weight : ℝ) (nonnegative : 0 ≤ weight)
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (current : representative.1.state = some ⟨14, some bob, execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ∃ other : app.Execution,
      history.1.state = some ⟨14, some bob, other⟩ ∧
      execution.recall bob = other.recall bob ∧
        execution.observe app bob = other.observe app bob := by
  classical
  have active := InformationModel.InformationSite.active _ site history
  obtain ⟨control, stateEq, actor⟩ := app.control_of_active initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawHistory _ _ _ history.1) bob active
  change history.1.state = some control at stateEq
  have rawTrace := stateEq ▸ rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) history.1.trace
  have information := representative.2.trans history.2.symm
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace =
    (rawMenu.signals _ _ _).infoOf bob history.1.trace at information
  rw [rawMenu.info, rawMenu.info] at information
  change app.observe bob representative.1.state = app.observe bob history.1.state at information
  rw [current, stateEq] at information
  simp only [ReactiveApplication.observe, actor, ↓reduceIte] at information
  have sameRecall := congrArg Prod.fst (Option.some.inj information)
  have sameView := congrArg Prod.snd (Option.some.inj information)
  change execution.recall bob = control.execution.recall bob at sameRecall
  change execution.observe app bob = control.execution.observe app bob at sameView
  have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change execution.environmentRecall.length + 14 = 26 at counted
  have cursor : execution.environmentRecall.length = 12 := by omega
  have clock : execution.application.clock = 3 := by
    rw [LateOpeningRuntimeService.clock_history weight nonnegative _ trace, cursor]
    decide
  have otherReady := ready_same_view _ _ sameView ready
  have sameClock := congrArg (fun view : app.PlayerView => view.application.publicView.clock)
    sameView
  change execution.application.clock = control.execution.application.clock at sameClock
  have actualClock : LateOpeningRuntimeService.clockAt
      control.execution.environmentRecall.length = 3 :=
    (LateOpeningRuntimeService.clock_history weight nonnegative control rawTrace).symm.trans
      (sameClock.symm.trans clock)
  have slot := LateOpeningRuntimeService.active_cursor weight nonnegative control rawTrace
    bob actor
  have remaining : control.remaining = 14 := by
    rcases slot with ⟨impossible, _⟩ | ⟨_, positions | ⟨position, completed⟩⟩
    · cases impossible
    · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
      rcases positions with position | position | position
      · rw [position] at actualClock
        exact ((by decide : LateOpeningRuntimeService.clockAt 5 ≠ 3) actualClock).elim
      · have budget := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) rawTrace
        change control.execution.environmentRecall.length + control.remaining = 26 at budget
        omega
      · rw [position] at actualClock
        exact ((by decide : LateOpeningRuntimeService.clockAt 20 ≠ 3) actualClock).elim
    · exact (otherReady.1
        ((control.execution.application.config.history_exact bobBindEvent).mp completed)).elim
  have sameControl : control = ⟨14, some bob, control.execution⟩ := by
    cases control
    simp only [ReactiveApplication.Control.mk.injEq] at actor remaining ⊢
    exact ⟨remaining, actor, trivial⟩
  exact ⟨control.execution, stateEq.trans (congrArg some sameControl), sameRecall, sameView⟩

end Vegas.Examples.LateOpeningRuntimeBobBindingFiber
