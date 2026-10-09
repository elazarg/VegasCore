/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobIncentive
import Vegas.Pending.ReactiveFiniteCompiler

/-! # Information classes at the final native Bob callback

One clean, ready and timely actual representative determines these properties
throughout Bob's information class. Own recall reconstructs all Bob envelopes;
the current observation includes their receipts and his immutable binding.
The canonical opening belongs to the actual bounded raw action menu.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobService
  LateOpeningRuntimeBobAudit LateOpeningRuntimeBobIncentive

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private theorem initial_law_eq :
    (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
  rw [PMF.map_comp]
  rfl

theorem output_values_covered : bounds.CoversOutputValues := by
  intro event
  change Fin 3 at event
  fin_cases event
  · exact bool_covered
  · intro value
    exact binding_values_covered bobBindEvent value
  · intro value
    exact binding_values_covered bobBindEvent value

/-- Normalized truthful final disclosure is among the actual bounded raw
responses, including at histories produced by arbitrary earlier deviations. -/
theorem canonical_available
    (history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History)
    (decision : DecisionHistory weight nonnegative)
    (current : history.state = some ⟨6, some bob, decision.execution⟩) :
    canonical weight nonnegative decision ∈ rawMenu.actions bob
      (decision.execution.recall bob) (decision.execution.observe app bob) := by
  have inputTrace : (rawMenu.protocol
      ((setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)))
      LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨6, some bob, decision.execution⟩) := by
    rw [initial_law_eq]
    exact current ▸ history.trace
  have handles := bounds.executionHandles_raw_history LateOpeningRuntimeService.runtime leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) inputTrace
  obtain ⟨serial, small, selected⟩ :=
    LateOpeningRuntimeService.runtime.reactiveFreshSlot_lt_horizon leaks
      (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨6, some bob, decision.execution⟩
      (rawMenu.toRawTrace _ _ _ inputTrace) bob rfl
  apply bounds.menu_in_raw LateOpeningRuntimeService.runtime leaks
  apply bounds.canonicalServiceDecision_available LateOpeningRuntimeService.runtime leaks
  rw [LateOpeningRuntimeService.runtime.canonicalReactiveDecision_eq_of_not_bind leaks bob
    bobRevealEvent true _ (by
      intro owner payload outputEq _codeEq _same
      have wrong : (EventField.publication (.range 0 5) : EventField Player simpleExpr) =
          .binding owner payload := outputEq
      cases wrong)]
  apply bounds.reactiveDecision_available LateOpeningRuntimeService.runtime leaks bob
    (decision.execution.recall bob) (decision.execution.observe app bob) output_values_covered
  · intro field candidate found
    exact handles.1 field candidate found
  · intro chosen found
    have same := Option.some.inj (found.symm.trans selected)
    change chosen < 26
    change serial < 26 at small
    omega

theorem clean_same_information (first second : app.Execution)
    (firstRecall : first.InputRecall app) (secondRecall : second.InputRecall app)
    (sameRecall : first.recall bob = second.recall bob)
    (sameView : first.observe app bob = second.observe app bob)
    (clean : CleanBindings first) : CleanBindings second := by
  have authored : second.network.inputs.filter (fun message => message.sender = bob) =
      first.network.inputs.filter (fun message => message.sender = bob) :=
    (secondRecall bob).trans ((congrArg app.outputs sameRecall.symm).trans
      (firstRecall bob).symm)
  have receipts : second.receipts = first.receipts :=
    (congrArg ReactiveApplication.PlayerView.receipts sameView).symm
  intro message member owned
  have filtered : message ∈ first.network.inputs.filter
      (fun message => message.sender = bob) := by
    rw [← authored]
    exact List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using owned⟩
  obtain ⟨token, shape, accepted⟩ := clean message (List.mem_filter.mp filtered).1 owned
  exact ⟨token, shape, receipts ▸ accepted⟩

theorem bound_same_view (first second : app.Execution)
    (sameView : first.observe app bob = second.observe app bob) :
    first.application.config.store (.inr bobBindEvent) =
      second.application.config.store (.inr bobBindEvent) := by
  have localView : first.application.playerView bob = second.application.playerView bob :=
    congrArg ReactiveApplication.PlayerView.application sameView
  have stores : nativeGraph.playerStore bob first.application.config.store =
      nativeGraph.playerStore bob second.application.config.store := by
    have same := congrArg (fun view : PlayerView nativeGraph => view.observation.store) localView
    exact same
  have visible : nativeGraph.fieldVisibleTo bob (.inr bobBindEvent) := rfl
  simpa only [nativeGraph.playerStore_of_visible bob _ _ visible] using
    congrFun stores (.inr bobBindEvent)

theorem ready_same_view (first second : app.Execution)
    (sameView : first.observe app bob = second.observe app bob)
    (ready : first.application.config.cut.Ready bobRevealEvent) :
    second.application.config.cut.Ready bobRevealEvent := by
  have publicViewEq : first.application.publicView = second.application.publicView :=
    congrArg (fun view : app.PlayerView => view.application.publicView) sameView
  apply (second.application.publicView_eventReady bobRevealEvent).mp
  rw [← publicViewEq]
  exact (first.application.publicView_eventReady bobRevealEvent).mpr ready

theorem timely_same_view (first second : app.Execution)
    (sameView : first.observe app bob = second.observe app bob)
    (timely : first.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent) :
    second.application.WithinDeadline LateOpeningRuntimeService.runtime bobRevealEvent := by
  have publicViewEq : first.application.publicView = second.application.publicView :=
    congrArg (fun view : app.PlayerView => view.application.publicView) sameView
  change second.application.publicView.WithinDeadline
    LateOpeningRuntimeService.runtime bobRevealEvent
  rw [← publicViewEq]
  exact timely

/-- Equal final Bob observations identify the actual final callback and the
six remaining scheduler rounds, rather than merely postulating common depth. -/
theorem final_remaining_same_view (decision : DecisionHistory weight nonnegative)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (sameView : decision.execution.observe app bob = control.execution.observe app bob) :
    control.remaining = 6 := by
  have clock : decision.execution.application.clock = 6 := by
    rw [clock_history weight nonnegative _ decision.trace,
      final_cursor weight nonnegative _ decision.trace]
    decide
  have sameClock := congrArg (fun view : app.PlayerView => view.application.publicView.clock)
    sameView
  change decision.execution.application.clock = control.execution.application.clock at sameClock
  have clocked := clock_history weight nonnegative control trace
  have actualClock : LateOpeningRuntimeService.clockAt control.execution.environmentRecall.length =
      6 := clocked.symm.trans (sameClock.symm.trans clock)
  have slot := active_cursor weight nonnegative control trace bob active
  rcases slot with ⟨impossible, _⟩ | ⟨_, positions | ⟨position, _⟩⟩
  · cases impossible
  · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
    rcases positions with position | position | position
    all_goals rw [position] at actualClock
    · exact ((by decide : LateOpeningRuntimeService.clockAt 5 ≠ 6) actualClock).elim
    · exact ((by decide : LateOpeningRuntimeService.clockAt 12 ≠ 6) actualClock).elim
    · have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) trace
      change control.execution.environmentRecall.length + control.remaining = 26 at accounted
      omega
  · rw [position] at actualClock
    exact ((by decide : LateOpeningRuntimeService.clockAt 14 ≠ 6) actualClock).elim

/-- Every legal hidden history of one actual final Bob information site has
the clean, immutable, ready and timely binding of its representative. -/
theorem decision_of_information
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨6, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ∃ result : DecisionHistory weight nonnegative,
      history.1.state = some ⟨6, some bob, result.execution⟩ ∧
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
  have remaining := final_remaining_same_view weight nonnegative decision control rawTrace
    actor sameView
  have sameControl : control = ⟨6, some bob, control.execution⟩ := by
    cases control
    simp only [ReactiveApplication.Control.mk.injEq] at actor remaining ⊢
    exact ⟨remaining, actor, trivial⟩
  have finalTrace := sameControl ▸ rawTrace
  let result : DecisionHistory weight nonnegative :=
    ⟨control.execution, finalTrace, decision.answer,
    (bound_same_view _ _ sameView).symm.trans decision.bound,
    ready_same_view _ _ sameView decision.ready,
    timely_same_view _ _ sameView decision.timely,
    clean_same_information _ _
      (app.history_inputRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace)
      (app.history_inputRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) rawTrace)
      sameRecall sameView decision.clean⟩
  exact ⟨result, stateEq.trans (congrArg some sameControl), sameRecall, sameView⟩

/-- Recover the actual final disclosure history in an information fiber. -/
def decisionOfInformation
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨6, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :=
  (decision_of_information weight nonnegative site representative decision current history).choose

theorem decisionOfInformation_spec
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨6, some bob, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    let result :=
      decisionOfInformation weight nonnegative site representative decision current history
    history.1.state = some ⟨6, some bob, result.execution⟩ ∧
      decision.execution.recall bob = result.execution.recall bob ∧
      decision.execution.observe app bob = result.execution.observe app bob :=
  (decision_of_information weight nonnegative site representative decision current
    history).choose_spec

end Vegas.Examples.LateOpeningRuntimeBobInformation
