/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeEarlyBobAudit
import Vegas.Pending.ReactiveAcceptanceUniqueness
import Interaction.ReactiveReceiptIdentity
import Interaction.ReactiveTrafficIdentity

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

/-- Readiness of the first binding rules out every earlier accepting Bob
receipt, even when Alice published before Bob's earlier callback. -/
theorem no_accepting_receipt_before_binding (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (ready : control.execution.application.config.cut.Ready bobBindEvent)
    (serial : Nat) : ((bob, serial), true) ∉ control.execution.receipts := by
  intro accepted
  obtain ⟨event, _, owned, completed⟩ :=
    LateOpeningRuntimeService.runtime.accepting_receipt_has_owned_event leaks initial
      LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) control trace
      (bob, serial) accepted
  change Fin 3 at event
  fin_cases event
  · change (some alice : Option Player) = some bob at owned
    norm_num [alice, bob] at owned
  · exact ready.1 completed
  · exact ready.1 (control.execution.application.config.cut.predecessor_closed completed
      (by decide : bobBindEvent ∈ nativeGraph.order.predecessors bobRevealEvent))

/-- A rejected authored envelope already in the actual prefix fixes the full
receiver charge for every current response and arbitrary further opponents. -/
theorem rejected_prefix_full_charge (weight : ℝ) (nonnegative : 0 ≤ weight)
    (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic execution)
    (owner : traffic.envelope.sender = bob)
    (rejected : (traffic.envelope.id, false) ∈ execution.receipts)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players remaining
      (execution.respond app bob response)).support) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some ⟨0, none, final⟩) bob = 1 := by
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) remaining execution bob response trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 remaining _ final
      (by simpa only [Nat.zero_add] using respondedTrace) reached
  have respondedPresent : traffic ∈ app.executionTraffic (execution.respond app bob response) := by
    have appended := app.stateTraffic_transition initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨some ⟨remaining, some bob, execution⟩, trace⟩
      (fun who => if who = bob then some response else none)
      (some ⟨remaining, none, execution.respond app bob response⟩) (by
        change _ ∈ (PMF.pure _).support
        simp only [↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff])
    change app.executionTraffic (execution.respond app bob response) =
      app.executionTraffic execution ++ _ at appended
    rw [appended]
    exact List.mem_append_left _ present
  have retained := (app.executionTraffic_runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    players remaining _ final reached).subset respondedPresent
  have respondedRejected : (traffic.envelope.id, false) ∈
      (execution.respond app bob response).receipts := rejected
  have finalRejected :=
    (app.receipt_policyInvariant players (traffic.envelope.id, false)).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) remaining _ final
      respondedRejected reached
  apply le_antisymm
  · exact (TerminalAudit.charge_mem_Icc _ _ _ _).2
  · exact rejected_envelope_full_charge weight nonnegative ⟨0, none, final⟩ finalTrace
      (by simp [ReactiveApplication.terminal]) bob traffic retained owner finalRejected


/-- An actual rejected receiver identifier already certifies the authored
traffic needed for the permanent full audit deduction. -/
theorem rejected_identifier_continuation_full_charge (weight : ℝ) (nonnegative : 0 ≤ weight)
    (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (serial : Nat) (rejected : ((bob, serial), false) ∈ execution.receipts)
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players remaining (execution.respond app bob response)).support) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some ⟨0, none, final⟩) bob = 1 := by
  have receiptIds := app.receipt_identifiers_history initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨remaining, some bob, execution⟩ trace
  have published : (bob, serial) ∈ execution.network.ledger.map Message.id := by
    rw [← receiptIds]
    exact List.mem_map.mpr ⟨((bob, serial), false), rejected, rfl⟩
  obtain ⟨message, ledgerMember, identified⟩ := List.mem_map.mp published
  have authored := app.ledger_subset_inputs_history initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨remaining, some bob, execution⟩ trace
      ledgerMember
  have inputIds := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.envelope =
    execution.network.inputs at inputIds
  rw [← inputIds] at authored
  obtain ⟨traffic, present, envelopeEq⟩ := List.mem_map.mp authored
  have owner : traffic.envelope.sender = bob := by
    change traffic.envelope.id.1 = bob
    rw [envelopeEq, identified]
  have receipt : (traffic.envelope.id, false) ∈ execution.receipts := by
    rw [envelopeEq, identified]
    exact rejected
  exact rejected_prefix_full_charge weight nonnegative remaining execution trace traffic present
    owner receipt response players final reached

/-- The sunk receiver charge depends on a public rejected receipt, so it
persists across every same-view legal disclosure history. -/
theorem rejected_identifier_same_view_full_charge (weight : ℝ) (nonnegative : 0 ≤ weight)
    (remaining : Nat) (first second : app.Execution)
    (sameView : first.observe app bob = second.observe app bob)
    (serial : Nat) (rejected : ((bob, serial), false) ∈ first.receipts)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, second⟩))
    (response : app.Action) (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players remaining (second.respond app bob response)).support) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some ⟨0, none, final⟩) bob = 1 := by
  have receipts := congrArg ReactiveApplication.PlayerView.receipts sameView
  change first.receipts = second.receipts at receipts
  exact rejected_identifier_continuation_full_charge weight nonnegative remaining second trace
    serial (receipts ▸ rejected) response players final reached

end Vegas.Examples.LateOpeningRuntimeBobSunkAudit
