/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision

/-! # Alice's first late callback with no prior transmission

The actual protected response is silent. Clock and full own recall identify
this first late opportunity, while the initialized binding and its opening
remain ready. These operational conditions transfer to every actual hidden
history of its information class without assigning posterior weights.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFirstDecision

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeAliceInformation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem first_alice_cursor (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some alice) (clock : control.execution.application.clock = 1) :
    control.execution.environmentRecall.length = 4 ∧ control.remaining = 22 := by
  have cursor := active_cursor weight nonnegative control trace alice active
  have displayed := clock_history weight nonnegative control trace
  rw [clock] at displayed
  rcases cursor with ⟨_, positions⟩ | ⟨impossible, _⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at positions
    rcases positions with position | position | position
    · rw [position] at displayed
      exact ((by decide : (1 : Nat) ≠ LateOpeningRuntimeService.clockAt 1) displayed).elim
    · have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) trace
      change control.execution.environmentRecall.length + control.remaining = 26 at accounted
      exact ⟨position, by omega⟩
    · rw [position] at displayed
      exact ((by decide : (1 : Nat) ≠ LateOpeningRuntimeService.clockAt 8) displayed).elim
  · cases impossible

/-- A genuine first late callback after the protected Alice response emitted no packet. -/
structure DecisionHistory where
  execution : app.Execution
  trace : (app.protocol initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨22, some alice, execution⟩)
  bit : Bool
  quiet : app.outputs (execution.recall alice) = []
  pending : execution.network.pending = []
  ready : execution.application.config.cut.Ready aliceEvent
  timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime aliceEvent
  bound : aliceBinding.get? execution.application.config.store = some (.success bit)
  associated : execution.application.accepted aliceBinding.field = some aliceCandidate
  fixed : execution.application.candidates.lookup aliceCandidate = .openable ⟨.bool, bit⟩

theorem decision_cursor (decision : DecisionHistory weight nonnegative) :
    decision.execution.environmentRecall.length = 4 := by
  have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace
  change decision.execution.environmentRecall.length + 22 = 26 at accounted
  omega

theorem decision_clock (decision : DecisionHistory weight nonnegative) :
    decision.execution.application.clock = 1 := by
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

/-- Full own recall and view transport this interface through every actual
hidden history of the first late information class. -/
theorem decision_of_information
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨22, some alice, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :
    ∃ result : DecisionHistory weight nonnegative,
      history.1.state = some ⟨22, some alice, result.execution⟩ ∧
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
  have pending := LateOpeningRuntimeAliceEmptyDecision.quiet_pending_empty weight nonnegative
    control trace (by rw [actor]; simp) quiet
  have samePublic := congrArg (fun view : app.PlayerView => view.application.publicView) sameView
  change decision.execution.application.publicView = control.execution.application.publicView
    at samePublic
  have clock : control.execution.application.clock = 1 :=
    (congrArg (fun view : app.PlayerView => view.application.publicView.clock) sameView).symm.trans
      (decision_clock weight nonnegative decision)
  have cursor := first_alice_cursor weight nonnegative control trace actor clock
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
  have sameControl : control = ⟨22, some alice, control.execution⟩ := by
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
    (current : representative.1.state = some ⟨22, some alice, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :=
  (decision_of_information weight nonnegative site representative decision current history).choose

theorem decisionOfInformation_spec
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1)
    (decision : DecisionHistory weight nonnegative)
    (current : representative.1.state = some ⟨22, some alice, decision.execution⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :
    let result :=
      decisionOfInformation weight nonnegative site representative decision current history
    history.1.state = some ⟨22, some alice, result.execution⟩ ∧
      decision.execution.recall alice = result.execution.recall alice ∧
      decision.execution.observe app alice = result.execution.observe app alice ∧
      decision.bit = result.bit :=
  (decision_of_information weight nonnegative site representative decision current
    history).choose_spec

/-- The whole permitted public envelope, including its certificate and
readiness token; private raw submission syntax is unrestricted. -/
def EmitsOpening (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) : Prop :=
  app.packet (app.submit decision.execution.application alice submission) alice
    (decision.execution.network.known alice) submission =
      (LateOpeningRuntimeLatePrefix.openingMessage decision.bit).payload

theorem opening_submission_unchanged (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission) (genuine : EmitsOpening weight nonnegative decision submission) :
    app.submit decision.execution.application alice submission =
      decision.execution.application := by
  have call := congrArg WitnessedPacket.call genuine
  change submission.call.packet = .opening aliceEvent aliceCandidate ⟨.bool, decision.bit⟩ at call
  rcases submission with ⟨⟨packet, material⟩, evidence⟩
  dsimp only at call
  subst packet
  cases material <;> rfl

end Vegas.Examples.LateOpeningRuntimeAliceFirstDecision
