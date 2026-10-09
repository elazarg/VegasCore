/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeRetryAudit
import Vegas.Examples.LateOpeningRuntimeServiceReceipt
import Vegas.Examples.LateOpeningRuntimeNash
import Interaction.ReactiveReceiptIdentity
import Interaction.ReactiveTrafficContinuation

/-! # Early Bob submissions are permanently rejected and charged

While Alice's publication remains unresolved, no Bob-authored raw call can be
accepted. A packet addressing Alice can carry her readiness token but fails
the sender check; Bob's own events are not ready. The actual author service
immediately publishes every submitted packet and records its rejection.
Full traffic auditing charges such an envelope at every terminal continuation.
These are operational and utility bounds, not a sequential-equilibrium claim.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEarlyBobAudit

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeUtility

/-- Sender authentication rejects even a Bob packet addressing Alice's
currently ready publication. No assumption about opaque pending packets is used. -/
theorem bob_handler_rejects (physical : EventGraphRuntime.State nativeGraph)
    (unresolved : aliceEvent ∉ physical.config.cut.completed)
    (message : Message Player app.Payload) (owner : message.sender = bob) :
    app.handle physical message = none := by
  apply reactiveHandle_none
  cases handled : LateOpeningRuntimeService.runtime.handle physical
      ⟨message.id, message.payload.call⟩ with
  | none => rfl
  | some next =>
      obtain ⟨event, named, ready, _, _⟩ :=
        handle_config_mem_step LateOpeningRuntimeService.runtime physical next
          ⟨message.id, message.payload.call⟩ handled
      have aliceReady : physical.config.cut.Ready aliceEvent :=
        ⟨unresolved, show ∅ ⊆ physical.config.cut.completed from Finset.empty_subset _⟩
      have same := setup.eventGraph.sequentialize_barrierOrdered.ready_public_unique
        physical.config.cut (show (nativeGraph.outputLayout aliceEvent).IsPublic from trivial)
          aliceReady ready
      obtain ⟨ownedEvent, namedOwned, actor⟩ := handle_event_actor
        LateOpeningRuntimeService.runtime physical next
          ⟨message.id, message.payload.call⟩ handled
      have identified : ownedEvent = event := Option.some.inj (namedOwned.symm.trans named)
      rw [identified, same] at actor
      change some alice = some message.sender at actor
      rw [owner] at actor
      exact ((by decide : alice ≠ bob) (Option.some.inj actor)).elim

/-- A protected author receipt records rejection for every early Bob raw
submission, independently of its payload, identifier request or event address. -/
theorem early_submission_false_receipt (execution next : app.Execution)
    (submission : app.Submission) (serials : execution.network.SerialsBeforeNext)
    (unresolved : aliceEvent ∉ execution.application.config.cut.completed)
    (reached : next ∈ ((execution.respond app bob ⟨some submission⟩).environmentStep app
      (latestAuthor bob
        ((execution.respond app bob ⟨some submission⟩).observeEnvironment app))).support) :
    ((bob, execution.network.nextSerial bob), false) ∈ next.receipts := by
  rw [latestAuthor_after_submit execution bob submission serials] at reached
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  let message : Message Player app.Payload :=
    ⟨(bob, execution.network.nextSerial bob),
      app.packet (app.submit execution.application bob submission) bob
        (execution.network.known bob) submission⟩
  have unchanged := (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
    execution bob ⟨some submission⟩).1
  have unavailable : aliceEvent ∉
      (execution.respond app bob ⟨some submission⟩).application.config.cut.completed := by
    rw [unchanged]
    exact unresolved
  have rejected := bob_handler_rejects
    (execution.respond app bob ⟨some submission⟩).application unavailable message rfl
  have lookup := serials.lookup_submit bob
    (app.packet (app.submit execution.application bob submission) bob
      (execution.network.known bob) submission)
  change (execution.respond app bob ⟨some submission⟩).network.lookup
    (bob, execution.network.nextSerial bob) = some message at lookup
  change ((bob, execution.network.nextSerial bob), false) ∈
    ((execution.respond app bob ⟨some submission⟩).includePending app
      (bob, execution.network.nextSerial bob)).receipts
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [lookup]
  change ((bob, execution.network.nextSerial bob), false) ∈
    (execution.respond app bob ⟨some submission⟩).receipts ++
      [((bob, execution.network.nextSerial bob), (app.handle _ message).isSome)]
  rw [rejected]
  simp

/-- At an actual Bob callback, the next physical scheduler round is the
author receipt turn. This specializes the receipt fact to the actual service. -/
theorem early_submission_round_false_receipt (weight : ℝ) (nonnegative : 0 ≤ weight)
    (remaining : Nat) (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (submission : app.Submission)
    (unresolved : aliceEvent ∉ execution.application.config.cut.completed)
    (players : Player → app.Policy) (next : app.Execution)
    (reached : next ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players (execution.respond app bob ⟨some submission⟩)).support) :
    ((bob, execution.network.nextSerial bob), false) ∈ next.receipts := by
  have selected := protected_response_scheduler weight nonnegative
    ⟨remaining, some bob, execution⟩ trace bob rfl ⟨some submission⟩ (Or.inl rfl)
  rw [ReactiveApplication.round, selected, PMF.pure_bind,
    ReactiveApplication.dispatch] at reached
  have passive := (latestAuthor_passive bob
    ((execution.respond app bob ⟨some submission⟩).observeEnvironment app)).1
  simp only [passive] at reached
  change next ∈ (((execution.respond app bob ⟨some submission⟩).environmentStep app
    (latestAuthor bob
      ((execution.respond app bob ⟨some submission⟩).observeEnvironment app))).bind
        (fun result => PMF.pure result)).support at reached
  rw [PMF.bind_pure] at reached
  exact early_submission_false_receipt execution next submission
    (app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler weight nonnegative)
      initial LateOpeningRuntimeService.horizon trace) unresolved reached

/-- Any actually recorded rejection is forbidden once all source events have
settled. The conclusion quantifies the full native raw history. -/
theorem rejected_envelope_forbidden (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (message : Message Player app.Payload)
    (rejected : (message.id, false) ∈ control.execution.receipts) :
    (LateOpeningRuntimeService.runtime.settledRecord leaks control.execution).permits message =
      false := by
  exact LateOpeningRuntimeRetryAudit.terminal_unaccepted_envelope_forbidden
    weight nonnegative control trace terminal message
      (app.rejected_identifier_not_accepted initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) control trace message.id rejected)

/-- Full authentic observation of actual traffic charges every player with a
recorded rejected envelope. Further accepted packets cannot undo the charge. -/
theorem rejected_envelope_full_charge (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (who : Player)
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = who)
    (rejected : (traffic.envelope.id, false) ∈ control.execution.receipts) :
    1 ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
        (fun actual => PMF.pure actual)) (some control) who := by
  classical
  apply LateOpeningRuntimeService.runtime.serviceAudit_charge_from_record leaks
    (fun record traffic => ((record, traffic.envelope) : SettledEvidence setup .sequential))
    (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
    (fun actual => PMF.pure actual) who 1 _ control traffic present owner
      (rejected_envelope_forbidden weight nonnegative control trace terminal traffic.envelope
        rejected)
  intro actual evidence member _ _
  rw [PMF.toOuterMeasure_pure_apply]
  rw [ite_eq_left (show actual ∈ {observed | evidence ∈ observed} from member)]
  norm_num

/-- Bob's net utility after a rejected envelope is at most one minus his
deposit, for every actual terminal raw history and nonnegative forfeit. -/
theorem bob_rejected_envelope_utility_bound {reward forfeit : ℝ}
    (forfeitNonnegative : 0 ≤ forfeit) (deposit : Player → ℝ)
    (depositNonnegative : 0 ≤ deposit bob) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (traffic : app.TrafficRecord)
    (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = bob)
    (rejected : (traffic.envelope.id, false) ∈ control.execution.receipts) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
      (some control) bob ≤ 1 - deposit bob := by
  have completed := LateOpeningRuntimeService.completes weight nonnegative control trace terminal
  obtain ⟨bit, label, aliceResult, binding, answer, decoded⟩ := nativeReadout_complete
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      control trace completed
  have base := nativeBaseUtility_of_readout reward forfeit (some control) _ decoded bob
  have upper := (sourceUtility_bob_bounds forfeitNonnegative reward
    (terminalStateOf bit label aliceResult binding answer)).2
  have charged := rejected_envelope_full_charge weight nonnegative control trace terminal bob
    traffic present owner rejected
  have penalty := mul_le_mul_of_nonneg_right charged depositNonnegative
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [base]
  linarith

/-- Any non-silent response at the actual first Bob callback has terminal
utility at most one minus his deposit, against arbitrary future policies of
both players. All traffic, completion and receipt premises are derived from
the actual initialized raw history and physical continuation. -/
theorem early_submission_continuation_utility_bound {reward forfeit : ℝ}
    (forfeitNonnegative : 0 ≤ forfeit) (deposit : Player → ℝ)
    (depositNonnegative : 0 ≤ deposit bob) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, some bob, execution⟩))
    (submission : app.Submission)
    (unresolved : aliceEvent ∉ execution.application.config.cut.completed)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 21 (execution.respond app bob ⟨some submission⟩)).support) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
      (some ⟨0, none, final⟩) bob ≤ 1 - deposit bob := by
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
  apply bob_rejected_envelope_utility_bound forfeitNonnegative deposit depositNonnegative
    weight nonnegative ⟨0, none, final⟩ finalTrace
      (by simp [ReactiveApplication.terminal]) traffic retained
  · rw [same]
    rfl
  · rw [same]
    exact rejected

end Vegas.Examples.LateOpeningRuntimeEarlyBobAudit
