/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPrivateCalendar
import Vegas.Pending.PhaseCountedBindingSubmission

/-! # Actual counted binding acceptance at the selected service slots -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem tail_binding_callback_timely (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt) (event : graph.EventId)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩) :
    execution.application.current.native.WithinDeadline runtime event := by
  let coordinate : CommitAttemptEvent graph := ⟨execution.application.attempt, event⟩
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have valid := raw_native_valid (family seeds) _ raw
  have clocks := tail_service_clocks countedMenu (PhaseCount.silence_onePacket runtime leaks bounds)
    seeds _ trace owner rfl coordinate retired request
  have currentClock : (PhaseSeedScheduler.informationInput runtime leaks coordinate owner
      (execution.recall owner) (execution.observe app owner)).elapsed ∈
      PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner (execution.recall owner)
        (execution.observe app owner) := List.mem_append_right _ (List.mem_singleton_self _)
  rw [clocks] at currentClock
  have ageZero := List.mem_singleton.mp currentClock
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  change execution.application.current.native.activatedAt event = some entered at stamp
  rw [State.WithinDeadline, stamp]
  change execution.application.current.native.clock - entered < 6
  change execution.application.current.native.clock -
    (execution.application.current.native.activatedAt event).getD
      execution.application.current.native.clock = 0 at ageZero
  rw [stamp, Option.getD_some] at ageZero
  omega

/-- Every counted binding declaration at a genuine continuation callback is
accepted by the immediately following actual include. Unopenable private
preparations and arbitrary evidence requests are retained literally. -/
theorem tail_counted_binding_submission_accepted (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (event : graph.EventId) (binding : graph.outputLayout event = .binding owner .bool)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner
        (execution.recall owner) (execution.observe app owner))
    (next : app.Execution)
    (moved : next ∈ ((execution.respond app owner ⟨some material⟩).environmentStep app
      (choose seeds (execution.respond app owner ⟨some material⟩).environmentRecall
        ((execution.respond app owner ⟨some material⟩).observeEnvironment app))).support) :
    PhaseService.BindingAccepted runtime leaks
      ⟨execution.application.attempt, event⟩ owner next := by
  classical
  let after := execution.respond app owner ⟨some material⟩
  let message : Message Player app.Payload :=
    ⟨(owner, execution.network.nextSerial owner),
      app.packet (app.submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have timely := tail_binding_callback_timely seeds remaining execution owner trace retired event
    request
  have submitted := PhaseCount.submitted_binding_accepted (Player := Player) (L := simpleExpr)
    (graph := graph) runtime leaks
    bounds plan (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (setup.initialLaw.map encodeInputs) horizon (family seeds) remaining owner execution trace event
      .bool binding request timely material offered
  change message ∈ after.network.inputs ∧
    message.payload.packet.call.event? graph = some event ∧
      ∃ target, app.handle after.application message = some target at submitted
  obtain ⟨input, named, target, phaseHandled⟩ := submitted
  have tag : message.payload.attempt = execution.application.attempt := rfl
  have authored : message.sender = owner := rfl
  obtain ⟨chosen, past, view, recalled, sourceSerial⟩ :=
    tail_response_command seeds raw owner rfl retired ⟨some material⟩
  rw [chosen, app.respond_environmentRecall, recalled,
    responseCommand_transmission execution owner past ⟨view, .activate owner⟩ rfl sourceSerial
      material] at moved
  have serials := app.serialsBeforeNext_history (family seeds) initial horizon raw
  have lookup := serials.lookup_submit owner
    (app.packet (app.submit execution.application owner material) owner
      (execution.network.known owner) material)
  change after.network.lookup message.id = some message at lookup
  change next ∈ (after.environmentStep app (.include message.id)).support at moved
  have inputNext : message ∈ next.network.inputs := by
    rw [app.environmentStep_inputs after next (.include message.id) moved]
    exact input
  have included := moved
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.mem_support_pure_iff] at included
  have receipts := congrArg (fun result : app.Execution => result.receipts) included
  change next.receipts = (after.includePending app message.id).receipts at receipts
  refine ⟨message, inputNext, authored, tag, named, ?_⟩
  rw [receipts]
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, lookup,
    phaseHandled, Option.isSome_some]
  exact List.mem_append_right _ (List.mem_singleton_self _)
end Vegas.Examples.CommitSeedSignalling
