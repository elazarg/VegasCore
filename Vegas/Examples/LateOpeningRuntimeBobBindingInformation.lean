/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobQuietPrefix
import Vegas.Examples.LateOpeningRuntimeNash

/-! # Bob's first binding information after Alice's publication failure

An actual clock-three first-binding representative with silent earlier Bob
responses determines the operational conditions throughout its information
class. Compatible histories retain the same own recall and current view,
including every pending Alice envelope Bob has sampled. Alice's immutable bit
and private label are not assigned a posterior distribution here.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeBobBindingService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

structure DecisionHistory where
  execution : app.Execution
  trace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨14, some bob, execution⟩)
  quiet : SilentRecall execution
  failed : execution.application.config.store (.inr aliceEvent) =
    some (.failure : PublicationResult Bool)
  ready : execution.application.config.cut.Ready bobBindEvent
  timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent

theorem DecisionHistory.clock (history : DecisionHistory weight nonnegative) :
    history.execution.application.clock = 3 := by
  have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) history.trace
  change history.execution.environmentRecall.length + 14 = 26 at counted
  have cursor : history.execution.environmentRecall.length = 12 := by omega
  rw [clock_history weight nonnegative _ history.trace, cursor]
  decide

theorem alice_result_same_view (first second : app.Execution)
    (same : first.observe app bob = second.observe app bob) :
    first.application.config.store (.inr aliceEvent) =
      second.application.config.store (.inr aliceEvent) := by
  have localView : first.application.playerView bob = second.application.playerView bob :=
    congrArg ReactiveApplication.PlayerView.application same
  have stores : nativeGraph.playerStore bob first.application.config.store =
      nativeGraph.playerStore bob second.application.config.store :=
    congrArg (fun view : PlayerView nativeGraph => view.observation.store) localView
  have visible : nativeGraph.fieldVisibleTo bob (.inr aliceEvent) := by decide
  simpa only [nativeGraph.playerStore_of_visible bob _ _ visible] using
    congrFun stores (.inr aliceEvent)

theorem ready_same_view (first second : app.Execution)
    (same : first.observe app bob = second.observe app bob)
    (ready : first.application.config.cut.Ready bobBindEvent) :
    second.application.config.cut.Ready bobBindEvent := by
  have publicViewEq : first.application.publicView = second.application.publicView :=
    congrArg (fun view : app.PlayerView => view.application.publicView) same
  apply (second.application.publicView_eventReady bobBindEvent).mp
  rw [← publicViewEq]
  exact (first.application.publicView_eventReady bobBindEvent).mpr ready

theorem timely_same_view (first second : app.Execution)
    (same : first.observe app bob = second.observe app bob)
    (timely : first.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent) :
    second.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent := by
  have publicViewEq : first.application.publicView = second.application.publicView :=
    congrArg (fun view : app.PlayerView => view.application.publicView) same
  change second.application.publicView.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent
  rw [← publicViewEq]
  exact timely

theorem binding_remaining_same_view (decision : DecisionHistory weight nonnegative)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (sameView : decision.execution.observe app bob = control.execution.observe app bob) :
    control.remaining = 14 := by
  have ready := ready_same_view _ _ sameView decision.ready
  have sameClock := congrArg (fun view : app.PlayerView => view.application.publicView.clock)
    sameView
  change decision.execution.application.clock = control.execution.application.clock at sameClock
  have actualClock : LateOpeningRuntimeService.clockAt
      control.execution.environmentRecall.length = 3 :=
    (clock_history weight nonnegative control trace).symm.trans
      (sameClock.symm.trans (decision.clock weight nonnegative))
  have slot := active_cursor weight nonnegative control trace bob active
  rcases slot with ⟨impossible, _⟩ | ⟨_, positions | ⟨position, completed⟩⟩
  · cases impossible
  · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
    rcases positions with position | position | position
    · rw [position] at actualClock
      exact ((by decide : LateOpeningRuntimeService.clockAt 5 ≠ 3) actualClock).elim
    · have budget := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) trace
      change control.execution.environmentRecall.length + control.remaining = 26 at budget
      omega
    · rw [position] at actualClock
      exact ((by decide : LateOpeningRuntimeService.clockAt 20 ≠ 3) actualClock).elim
  · exact (ready.1
      ((control.execution.application.config.history_exact bobBindEvent).mp completed)).elim

/-- Every legal hidden history of this actual binding information class has
the same failed Alice publication, unused timely binding, and silent own
responses. The complete sampled network view is preserved without a posterior
assumption about Alice's inputs. -/
theorem decision_of_information
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ∃ result : DecisionHistory weight nonnegative,
      history.1.state = some ⟨14, some bob, result.execution⟩ ∧
        decision.execution.recall bob = result.execution.recall bob ∧
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
  change decision.execution.recall bob = control.execution.recall bob at sameRecall
  change decision.execution.observe app bob = control.execution.observe app bob at sameView
  have remaining := binding_remaining_same_view weight nonnegative decision control rawTrace
    actor sameView
  have sameControl : control = ⟨14, some bob, control.execution⟩ := by
    cases control
    simp only [ReactiveApplication.Control.mk.injEq] at actor remaining ⊢
    exact ⟨remaining, actor, trivial⟩
  have quiet : SilentRecall control.execution := by
    intro entry member
    rw [← sameRecall] at member
    exact decision.quiet entry member
  let result : DecisionHistory weight nonnegative :=
    ⟨control.execution, sameControl ▸ rawTrace, quiet,
      (alice_result_same_view _ _ sameView).symm.trans decision.failed,
      ready_same_view _ _ sameView decision.ready, timely_same_view _ _ sameView decision.timely⟩
  exact ⟨result, stateEq.trans (congrArg some sameControl), sameRecall, sameView⟩

def decisionOfInformation
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :=
  (decision_of_information weight nonnegative site representative decision current history).choose

theorem decisionOfInformation_spec
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    let result :=
      decisionOfInformation weight nonnegative site representative decision current history
    history.1.state = some ⟨14, some bob, result.execution⟩ ∧
      decision.execution.recall bob = result.execution.recall bob ∧
        decision.execution.observe app bob = result.execution.observe app bob :=
  (decision_of_information weight nonnegative site representative decision current
    history).choose_spec

/-- All six intended answer commitments are available in the actual bounded
raw menu, at every compatible representative satisfying these conditions. -/
theorem canonical_available (history : DecisionHistory weight nonnegative) (answer : Answer) :
    LateOpeningRuntimeBobSuffix.binding answer ∈ rawMenu.actions bob
      (history.execution.recall bob) (history.execution.observe app bob) := by
  have available := canonical_binding_available weight nonnegative
    ⟨14, some bob, history.execution⟩ history.trace history.quiet history.ready answer
  rwa [canonical_binding weight nonnegative ⟨14, some bob, history.execution⟩ history.trace
    history.quiet history.ready answer] at available

end Vegas.Examples.LateOpeningRuntimeBobBindingInformation
