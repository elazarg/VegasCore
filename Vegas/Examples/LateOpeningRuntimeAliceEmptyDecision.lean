/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceDecision
import Interaction.ReactiveReceiptIdentity
import Interaction.ReactiveEmissionOrder

/-! # Alice's final callback after sending no packet

Own recall identifies the absence of prior Alice traffic. Every earlier Bob
packet has its protected public receipt, including rejected calls, so none can
still compete in the pending pool at an active Alice callback. This conclusion
does not restrict Bob's private preparation or submission syntax. The full
native information class retains the initialized opening and its readiness.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeAliceInformation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem no_alice_inputs (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (quiet : app.outputs (control.execution.recall alice) = []) :
    ∀ message ∈ control.execution.network.inputs, message.sender ≠ alice := by
  have recalled := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change control.execution.InputRecall app at recalled
  intro message member owned
  have filtered : message ∈ control.execution.network.inputs.filter
      (fun packet => packet.sender = alice) :=
    List.mem_filter.mpr ⟨member, decide_eq_true owned⟩
  rw [recalled alice, quiet] at filtered
  exact List.not_mem_nil filtered

/-- Protected author receipts empty the foreign pool regardless of acceptance. -/
theorem quiet_pending_empty (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor ≠ none)
    (quiet : app.outputs (control.execution.recall alice) = []) :
    control.execution.network.pending = [] := by
  have origins := app.history_provenance initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change control.execution.Provenance app at origins
  have recalled := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change control.execution.InputRecall app at recalled
  have noAlice := no_alice_inputs weight nonnegative control trace quiet
  have identities := app.receipt_identifiers_history initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) control trace
  have distinct := app.idsDistinct_history (LateOpeningRuntimeService.scheduler weight nonnegative)
    initial LateOpeningRuntimeService.horizon trace
  change control.execution.network.IdsDistinct at distinct
  unfold MessageNetwork.IdsDistinct at distinct
  rw [List.map_append] at distinct
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro message pending
  obtain ⟨entry, member, _material, _action, emitted, _packet⟩ := origins.pending message pending
  have output : message ∈ app.outputs (control.execution.recall message.sender) :=
    List.mem_filterMap.mpr ⟨entry, member, emitted⟩
  rw [← recalled message.sender] at output
  have different := noAlice message (List.mem_filter.mp output).1
  have owner : message.sender = bob := by
    rcases message with ⟨⟨who, serial⟩, payload⟩
    fin_cases who
    · exact (different rfl).elim
    · rfl
  rw [owner] at member
  obtain ⟨accepted, receipt⟩ := protected_submission_receipt_of_active weight nonnegative
    control trace bob entry member message emitted (Or.inl rfl) active
  have published : message.id ∈ control.execution.network.ledger.map Message.id := by
    rw [← identities]
    exact List.mem_map.mpr ⟨(message.id, accepted), receipt, rfl⟩
  exact (List.nodup_append.mp distinct).2.2 message.id
    (List.mem_map.mpr ⟨message, pending, rfl⟩) message.id published rfl

/-- A legal last Alice response with her immutable initial opening still ready. -/
structure DecisionHistory where
  execution : app.Execution
  trace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨18, some alice, execution⟩)
  bit : Bool
  quiet : app.outputs (execution.recall alice) = []
  pending : execution.network.pending = []
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

theorem decision_serial (decision : DecisionHistory weight nonnegative) :
    decision.execution.network.nextSerial alice = 0 := by
  have emissions := app.emissionOrder_history
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    initial LateOpeningRuntimeService.horizon decision.trace
  change decision.execution.EmissionOrder app at emissions
  have lengths := congrArg List.length (emissions alice)
  rw [decision.quiet] at lengths
  simpa using lengths.symm

/-- Actual observation equality transports this interface through the whole
information fiber, including arbitrary hidden Bob packets and candidates. -/
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
  have quiet : app.outputs (control.execution.recall alice) = [] := by
    rw [← sameRecall, decision.quiet]
  have pending := quiet_pending_empty weight nonnegative control trace
    (by rw [actor]; simp) quiet
  have samePublic := congrArg (fun view : app.PlayerView => view.application.publicView) sameView
  change decision.execution.application.publicView = control.execution.application.publicView
    at samePublic
  have clock : control.execution.application.clock = 2 :=
    (congrArg (fun view : app.PlayerView => view.application.publicView.clock) sameView).symm.trans
      (decision_clock weight nonnegative decision)
  have cursor := last_alice_cursor weight nonnegative control trace actor clock
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
    ⟨control.execution, sameControl ▸ trace, decision.bit, quiet, pending, ready, timely,
      (LateOpeningRuntimeAliceDecision.bound_same_view _ _ sameView).symm.trans decision.bound,
      associated, fixed⟩
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

end Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision
