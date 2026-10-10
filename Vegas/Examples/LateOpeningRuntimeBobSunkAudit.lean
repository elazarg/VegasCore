/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeEarlyBobAudit

/-! # The receiver charge after an early rejected native response

The first early non-silent response already incurs the entire one-time receiver
charge in every physical continuation. Later binding and opening choices cannot
increase this sunk charge.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSunkAudit

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeEarlyBobAudit

/-- The actual rejected early envelope fixes the terminal full-audit charge,
independently of every player's later native responses. -/
theorem early_submission_continuation_full_charge (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, some bob, execution⟩))
    (submission : app.Submission)
    (unresolved : aliceEvent ∉ execution.application.config.cut.completed)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 21 (execution.respond app bob ⟨some submission⟩)).support) :
    TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some ⟨0, none, final⟩) bob = 1 := by
  obtain ⟨submittedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 execution bob
      ⟨some submission⟩ trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 21 _ final
      submittedTrace reached
  let message : Message Player app.Payload :=
    ⟨(bob, execution.network.nextSerial bob),
      app.packet (app.submit execution.application bob submission) bob
        (execution.network.known bob) submission⟩
  have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) submittedTrace
  change (app.executionTraffic (execution.respond app bob ⟨some submission⟩)).map
    ReactiveApplication.TrafficRecord.envelope = execution.network.inputs ++ [message] at inputs
  have presentMessage : message ∈
      (app.executionTraffic (execution.respond app bob ⟨some submission⟩)).map
        ReactiveApplication.TrafficRecord.envelope := by
    rw [inputs]
    simp
  obtain ⟨traffic, present, same⟩ := List.mem_map.mp presentMessage
  have retained := (app.executionTraffic_runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 21 _ final reached).subset
      present
  have firstStep := reached
  rw [ReactiveApplication.runRounds] at firstStep
  obtain ⟨next, moved, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ firstStep)
  have receipt := early_submission_round_false_receipt weight nonnegative 21 execution trace
    submission unresolved players next moved
  have rejected := (app.receipt_policyInvariant players (message.id, false)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 20 next final receipt continued
  apply le_antisymm
  · exact (TerminalAudit.charge_mem_Icc _ _ _ _).2
  · apply rejected_envelope_full_charge weight nonnegative ⟨0, none, final⟩ finalTrace
      (by simp [ReactiveApplication.terminal]) bob traffic retained
    · rw [same]
      rfl
    · rw [same]
      exact rejected

end Vegas.Examples.LateOpeningRuntimeBobSunkAudit
