/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastTailSuccess
import Interaction.ReactiveProvenance

/-! # Exact resolved continuation binding success on the original counted word -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem idle_bindingAccepted_emitted (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks coordinate owner execution) :
    PhaseService.bindingEmissionClocks runtime leaks coordinate owner execution ≠ [] := by
  intro empty
  have unsent := unsent_of_empty_emissions seeds remaining execution trace coordinate owner empty
  obtain ⟨message, input, authored, stamp, named, _receipt⟩ := accepted
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have output : message ∈ app.outputs (execution.recall owner) := by
    rw [← app.history_inputRecall initial horizon (family seeds) raw owner]
    exact List.mem_filter.mpr ⟨input, decide_eq_true authored⟩
  apply unsent message output
  simp only [PhaseCount.event?, named, stamp, Option.map_some]

private theorem tail_idle_bindingAccepted_of_emitted (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (binding : graph.outputLayout coordinate.event = .binding owner .bool)
    (resolved : coordinate.Resolved execution.application)
    (nonempty : PhaseService.bindingEmissionClocks runtime leaks coordinate owner execution ≠ []) :
    PhaseService.BindingAccepted runtime leaks coordinate owner execution := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seeds) remaining execution trace
  have recalled := app.history_inputRecall initial horizon (family seeds) raw
  have emitted : ∃ clock message, (clock, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions := by
    cases packets : (PhaseSeedScheduler.localInput runtime leaks coordinate owner
        execution.environmentRecall (execution.observeEnvironment app)).emissions with
    | nil => exact (nonempty (by simp only [PhaseService.bindingEmissionClocks, packets,
        List.map_nil])).elim
    | cons pair rest => exact ⟨pair.1, pair.2, List.mem_cons_self⟩
  obtain ⟨clock, message, emitted⟩ := emitted
  obtain ⟨input, authored, stamp, named⟩ := PhaseSeedScheduler.localInput_emission_authentic
    runtime leaks execution coordinate owner words recalled clock message emitted
  obtain ⟨entry, member, material, transmitted, issued, state, known, packet⟩ :=
    (app.history_provenance initial horizon (family seeds) raw).inputs message input
  rw [authored] at member
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  obtain ⟨actual, request, actualStamp, actualNamed⟩ := PhaseCount.recorded_material_request
    runtime leaks bounds plan (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
      (setup.initialLaw.map encodeInputs) horizon (family seeds) _ compiledTrace owner entry member
        material transmitted
  have exactCall := phase_emit_call state message.sender known material
  change state.emit message.sender known material = message.payload at packet
  have callEq : material.call.packet = message.payload.packet.call :=
    exactCall.symm.trans (congrArg (fun output => output.packet.call) packet)
  have issuedStamp := phase_recalled_emission_attempt runtime leaks initial horizon (family seeds)
    raw owner entry member message issued
  have sameStamp : actual.attempt = coordinate.attempt :=
    actualStamp.trans (issuedStamp.symm.trans stamp)
  have sameEvent : actual.event = coordinate.event := Option.some.inj
    (actualNamed.symm.trans ((congrArg (Payload.event? graph) callEq).trans named))
  have same : actual = coordinate := by
    cases actual
    cases coordinate
    cases sameStamp
    cases sameEvent
    rfl
  rw [same] at request
  exact tail_recorded_binding_resolved_accepted seeds _ trace coordinate owner retired binding
    entry member request material transmitted resolved

/-- On every resolved counted continuation binding, success is exactly the
presence of an original service emission. This holds at arbitrary active or
idle endpoints and retains receipts through rollback and exhausted restore. -/
theorem tail_binding_accepted_iff_emitted (seeds : Seeds) (current : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (binding : graph.outputLayout coordinate.event = .binding owner .bool)
    (resolved : coordinate.Resolved current.execution.application) :
    PhaseService.BindingAccepted runtime leaks coordinate owner current.execution ↔
      PhaseService.bindingEmissionClocks runtime leaks coordinate owner current.execution ≠ [] := by
  rcases current with ⟨remaining, active, execution⟩
  cases active with
  | none => exact ⟨idle_bindingAccepted_emitted seeds remaining execution trace coordinate owner,
      tail_idle_bindingAccepted_of_emitted seeds remaining execution trace coordinate owner
        retired binding resolved⟩
  | some actor =>
      obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seeds) remaining
        execution actor ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds actor _ _)
      have accepted := idle_bindingAccepted_emitted seeds remaining
        (execution.respond app actor ⟨none⟩) responded coordinate owner
      have emitted := tail_idle_bindingAccepted_of_emitted seeds remaining
        (execution.respond app actor ⟨none⟩) responded coordinate owner retired binding resolved
      exact ⟨accepted, emitted⟩

end Vegas.Examples.CommitSeedBroadcast
