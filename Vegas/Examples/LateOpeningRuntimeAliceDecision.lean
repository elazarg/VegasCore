/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceInformation

/-! # Genuine first-opening histories throughout an Alice information class

The interface consists of operational facts of an actual initialized raw
history. It retains the entire execution, including Alice's submission syntax
and both players' private recall. Equal Alice observations transfer the
immutable binding, its candidate and readiness; public receipts exclude hidden
Bob traffic. No belief support or posterior is postulated.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceDecision

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeAliceInformation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- A legal final Alice callback with one genuine initialized opening pending.
The previous private submission syntax is unrestricted. -/
structure DecisionHistory where
  execution : app.Execution
  trace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨18, some alice, execution⟩)
  bit : Bool
  inputs : execution.network.inputs = [openingMessage bit]
  pending : execution.network.pending = [openingMessage bit]
  receipts : execution.receipts = []
  ledger : execution.network.ledger = []
  ready : execution.application.config.cut.Ready aliceEvent
  timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime aliceEvent
  bound : aliceBinding.get? execution.application.config.store = some (.success bit)
  associated : execution.application.accepted aliceBinding.field = some aliceCandidate
  fixed : execution.application.candidates.lookup aliceCandidate = .openable ⟨.bool, bit⟩

theorem decision_cursor (decision : DecisionHistory weight nonnegative) :
    decision.execution.environmentRecall.length = 8 := by
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace
  change decision.execution.environmentRecall.length + 18 = 26 at accounted
  omega

theorem decision_clock (decision : DecisionHistory weight nonnegative) :
    decision.execution.application.clock = 2 := by
  rw [clock_history weight nonnegative _ decision.trace,
    decision_cursor weight nonnegative decision]
  decide

theorem bound_same_view (first second : app.Execution)
    (sameView : first.observe app alice = second.observe app alice) :
    aliceBinding.get? first.application.config.store =
      aliceBinding.get? second.application.config.store := by
  have stores := congrArg (fun view : app.PlayerView => view.application.observation.store) sameView
  change nativeGraph.playerStore alice first.application.config.store =
    nativeGraph.playerStore alice second.application.config.store at stores
  change first.application.config.store (.inl aliceInput) =
    second.application.config.store (.inl aliceInput)
  have visible : nativeGraph.fieldVisibleTo alice (.inl aliceInput) := rfl
  simpa only [nativeGraph.playerStore_of_visible alice _ _ visible] using
    congrFun stores (.inl aliceInput)

/-- A single actual representative supplies the operational interface at
every hidden history of the same full native Alice information class. -/
theorem decision_of_information
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨18, some alice, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :
    ∃ result : DecisionHistory weight nonnegative,
      history.1.state = some ⟨18, some alice, result.execution⟩ ∧
      decision.execution.recall alice = result.execution.recall alice ∧
      decision.execution.observe app alice = result.execution.observe app alice ∧
      decision.bit = result.bit := by
  classical
  have active := InformationModel.InformationSite.active _ site history
  obtain ⟨control, stateEq, actor⟩ := app.control_of_active initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      (rawMenu.toRawHistory _ _ _ history.1) alice active
  change history.1.state = some control at stateEq
  have trace := stateEq ▸ rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) history.1.trace
  have information := representative.2.trans history.2.symm
  change (rawMenu.signals _ _ _).infoOf alice representative.1.trace =
    (rawMenu.signals _ _ _).infoOf alice history.1.trace at information
  rw [rawMenu.info, rawMenu.info] at information
  change app.observe alice representative.1.state = app.observe alice history.1.state at information
  rw [current, stateEq] at information
  simp only [ReactiveApplication.observe, actor, ↓reduceIte] at information
  have sameRecall := congrArg Prod.fst (Option.some.inj information)
  have sameView := congrArg Prod.snd (Option.some.inj information)
  change decision.execution.recall alice = control.execution.recall alice at sameRecall
  change decision.execution.observe app alice = control.execution.observe app alice at sameView
  have receipts : control.execution.receipts = [] :=
    (congrArg ReactiveApplication.PlayerView.receipts sameView).symm.trans decision.receipts
  have ledger : control.execution.network.ledger = [] :=
    (congrArg (fun view : app.PlayerView => view.messages.ledger) sameView).symm.trans
      decision.ledger
  have samePublic := congrArg (fun view : app.PlayerView => view.application.publicView) sameView
  change decision.execution.application.publicView = control.execution.application.publicView
    at samePublic
  have clock : control.execution.application.clock = 2 :=
    (congrArg (fun view : app.PlayerView => view.application.publicView.clock) sameView).symm.trans
      (decision_clock weight nonnegative decision)
  have cursor := last_alice_cursor weight nonnegative control trace actor clock
  have own := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace
  change decision.execution.InputRecall app at own
  have ownOutputs : app.outputs (control.execution.recall alice) =
      [openingMessage decision.bit] := by
    rw [← sameRecall, ← own alice, decision.inputs]
    rfl
  have inputs := first_opening_inputs weight nonnegative control trace
    (by rw [actor]; simp) receipts decision.bit ownOutputs
  have pending := singleton_input_pending weight nonnegative control trace _ inputs ledger
  have ready : control.execution.application.config.cut.Ready aliceEvent := by
    apply (control.execution.application.publicView_eventReady aliceEvent).mp
    rw [← samePublic]
    exact (decision.execution.application.publicView_eventReady aliceEvent).mpr decision.ready
  have timely : control.execution.application.WithinDeadline
      LateOpeningRuntimeService.runtime aliceEvent := by
    change control.execution.application.publicView.WithinDeadline
      LateOpeningRuntimeService.runtime aliceEvent
    rw [← samePublic]
    exact decision.timely
  have associated : control.execution.application.accepted aliceBinding.field =
      some aliceCandidate :=
    (congrArg (fun view : app.PlayerView => view.application.publicView.accepted aliceBinding.field)
      sameView).symm.trans decision.associated
  have fixed : control.execution.application.candidates.lookup aliceCandidate =
      .openable ⟨.bool, decision.bit⟩ :=
    (congrArg (fun view : app.PlayerView => view.application.candidates (.initial aliceInput))
      sameView).symm.trans decision.fixed
  have sameControl : control = ⟨18, some alice, control.execution⟩ := by
    cases control
    simp only [ReactiveApplication.Control.mk.injEq] at actor cursor ⊢
    exact ⟨cursor.2, actor, trivial⟩
  let result : DecisionHistory weight nonnegative :=
    ⟨control.execution, sameControl ▸ trace, decision.bit, inputs, pending, receipts, ledger,
      ready, timely, (bound_same_view _ _ sameView).symm.trans decision.bound, associated, fixed⟩
  exact ⟨result, stateEq.trans (congrArg some sameControl), sameRecall, sameView, rfl⟩

def decisionOfInformation
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨18, some alice, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :=
  (decision_of_information weight nonnegative site representative decision current history).choose

theorem decisionOfInformation_spec
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨18, some alice, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :
    let result :=
      decisionOfInformation weight nonnegative site representative decision current history
    history.1.state = some ⟨18, some alice, result.execution⟩ ∧
      decision.execution.recall alice = result.execution.recall alice ∧
      decision.execution.observe app alice = result.execution.observe app alice ∧
      decision.bit = result.bit :=
  (decision_of_information weight nonnegative site representative decision current
    history).choose_spec

end Vegas.Examples.LateOpeningRuntimeAliceDecision
