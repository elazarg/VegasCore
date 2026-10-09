/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeEarlyBobAudit
import Vegas.Examples.LateOpeningRuntimeBobBindingService

/-! # Actual information classes at Bob's first unresolved callback

Empty own recall, the public clock and Alice's unresolved event identify every
hidden history of this native information site. All these histories have the
same twenty-one remaining scheduler rounds and no earlier Bob submissions.
No restriction on Alice's packets or on the assessment's belief is imposed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEarlyBobInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

structure DecisionHistory where
  execution : app.Execution
  trace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨21, some bob, execution⟩)
  emptyRecall : execution.recall bob = []
  unresolved : aliceEvent ∉ execution.application.config.cut.completed

theorem DecisionHistory.quiet (history : DecisionHistory weight nonnegative) :
    SilentRecall history.execution := by
  intro entry member
  rw [history.emptyRecall] at member
  cases member

theorem DecisionHistory.clock (history : DecisionHistory weight nonnegative) :
    history.execution.application.clock = 1 := by
  have budget := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) history.trace
  have cursor : history.execution.environmentRecall.length = 5 := by
    change history.execution.environmentRecall.length + 21 = 26 at budget
    omega
  rw [clock_history weight nonnegative _ history.trace, cursor]
  decide

theorem unresolved_same_view (first second : app.Execution)
    (same : first.observe app bob = second.observe app bob)
    (unresolved : aliceEvent ∉ first.application.config.cut.completed) :
    aliceEvent ∉ second.application.config.cut.completed := by
  have equal : first.application.publicView.observation.completionOrder =
      second.application.publicView.observation.completionOrder :=
    congrArg (fun view : app.PlayerView => view.application.publicView.observation.completionOrder)
      same
  intro completed
  apply unresolved
  apply (first.application.config.history_exact aliceEvent).mp
  change aliceEvent ∈ first.application.publicView.observation.completionOrder
  rw [equal]
  exact (second.application.config.history_exact aliceEvent).mpr completed

theorem first_remaining_same_view (decision : DecisionHistory weight nonnegative)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (sameView : decision.execution.observe app bob = control.execution.observe app bob) :
    control.remaining = 21 := by
  have sameClock := congrArg (fun view : app.PlayerView => view.application.publicView.clock)
    sameView
  change decision.execution.application.clock = control.execution.application.clock at sameClock
  have actualClock : LateOpeningRuntimeService.clockAt
      control.execution.environmentRecall.length = 1 :=
    (clock_history weight nonnegative control trace).symm.trans
      (sameClock.symm.trans (decision.clock weight nonnegative))
  have slot := active_cursor weight nonnegative control trace bob active
  rcases slot with ⟨impossible, _⟩ | ⟨_, positions | ⟨position, _⟩⟩
  · cases impossible
  · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
    rcases positions with position | position | position
    · have budget := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) trace
      change control.execution.environmentRecall.length + control.remaining = 26 at budget
      omega
    · rw [position] at actualClock
      exact ((by decide : LateOpeningRuntimeService.clockAt 12 ≠ 1) actualClock).elim
    · rw [position] at actualClock
      exact ((by decide : LateOpeningRuntimeService.clockAt 20 ≠ 1) actualClock).elim
  · rw [position] at actualClock
    exact ((by decide : LateOpeningRuntimeService.clockAt 14 ≠ 1) actualClock).elim

/-- A single actual first-callback representative classifies every hidden
history in its bounded raw information class, including zero-reach histories. -/
theorem decision_of_information
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨21, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ∃ result : DecisionHistory weight nonnegative,
      history.1.state = some ⟨21, some bob, result.execution⟩ ∧
      decision.execution.observe app bob = result.execution.observe app bob := by
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
  have remaining := first_remaining_same_view weight nonnegative decision control rawTrace
    actor sameView
  have sameControl : control = ⟨21, some bob, control.execution⟩ := by
    cases control
    simp only [ReactiveApplication.Control.mk.injEq] at actor remaining ⊢
    exact ⟨remaining, actor, trivial⟩
  let result : DecisionHistory weight nonnegative :=
    ⟨control.execution, sameControl ▸ rawTrace, sameRecall.symm.trans decision.emptyRecall,
      unresolved_same_view _ _ sameView decision.unresolved⟩
  exact ⟨result, stateEq.trans (congrArg some sameControl), sameView⟩

def decisionOfInformation
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨21, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :=
  (decision_of_information weight nonnegative site representative decision current history).choose

theorem decisionOfInformation_spec
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨21, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    let result :=
      decisionOfInformation weight nonnegative site representative decision current history
    history.1.state = some ⟨21, some bob, result.execution⟩ ∧
      decision.execution.observe app bob = result.execution.observe app bob :=
  (decision_of_information weight nonnegative site representative decision current
    history).choose_spec

end Vegas.Examples.LateOpeningRuntimeEarlyBobInformation
