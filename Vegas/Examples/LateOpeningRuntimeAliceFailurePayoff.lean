/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDisclosurePublication
import Vegas.Examples.LateOpeningRuntimeBindingObservationWitness
import Vegas.Examples.LateOpeningRuntimeAliceContinuation
import Vegas.Examples.LateOpeningRuntimeTerminalReceipt
import Vegas.Examples.LateOpeningRuntimeSettlementContinuation

/-! # Exact sender payoff after an omitted genuine opening

The genuine Alice-zero envelope persists in the actual input traffic even
when its inclusion lottery omits it. The accepting receipt remains absent
through every later raw policy, and full settled auditing charges Alice
exactly once. Successful receiver publication then gives the source's exact
label-dependent reward, minus the publication forfeit and Alice's audit
deposit. These statements retain the original runtime's complete audit.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFailurePayoff

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeUtility LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
  LateOpeningRuntimeBindingObservation LateOpeningRuntimeSettlementContinuation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- A genuine opening present in the actual traffic is fully charged when
its identifier has no accepting receipt at completed settlement. -/
theorem unaccepted_opening_charge (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (bit : Bool)
    (present : openingMessage bit ∈ control.execution.network.inputs)
    (unaccepted : ¬ ((alice, 0), true) ∈ control.execution.receipts) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some control) alice = 1 := by
  classical
  have inputs := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change (app.executionTraffic control.execution).map ReactiveApplication.TrafficRecord.envelope =
    control.execution.network.inputs at inputs
  rw [← inputs] at present
  obtain ⟨traffic, member, envelope⟩ := List.mem_map.mp present
  let record := LateOpeningRuntimeService.runtime.settledRecord leaks control.execution
  have completed := LateOpeningRuntimeService.completes weight nonnegative control trace terminal
  have finished : aliceEvent ∈ control.execution.application.config.cut.completed := by
    rw [completed]
    exact Finset.mem_univ _
  have settled : aliceEvent ∈ record.view.observation.completionOrder :=
    (control.execution.application.config.history_exact aliceEvent).mpr finished
  have forbidden : record.permits traffic.envelope = false := by
    rw [envelope]
    exact SettledRecord.permits_eq_false_of_settled record (openingMessage bit) aliceEvent
      rfl settled (fun accepted => unaccepted accepted.1)
  have charged : 1 ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some control) alice := by
    apply LateOpeningRuntimeService.runtime.serviceAudit_charge_from_record leaks
      (fun settled traffic => ((settled, traffic.envelope) : SettledEvidence setup .sequential))
      (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
      (fun actual => PMF.pure actual) alice 1 _ control traffic member
      (by rw [envelope]; rfl) forbidden
    intro actual evidence selected _ _
    rw [PMF.toOuterMeasure_pure_apply]
    rw [ite_eq_left (show actual ∈ {observed | evidence ∈ observed} from selected)]
    norm_num
  exact le_antisymm (TerminalAudit.charge_mem_Icc _ _ _ _).2 charged

theorem failed_inputs (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) :
    (failedAnswerDecision bit label slot earlySeen finalSeen).application.config.inputs =
      setup.eventInputs (sourceInitial bit label) := by
  rw [failedAnswerDecision_physical]
  rfl

theorem failed_opening_present (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) :
    openingMessage bit ∈ (failedAnswerDecision bit label slot earlySeen finalSeen).network.inputs :=
  by
    fin_cases slot
    · change openingMessage bit ∈ (beforeBob bit label 0).network.inputs
      rw [beforeBob_first_network]
      exact List.mem_singleton.mpr rfl
    · change openingMessage bit ∈
        [⟨(alice, 0), app.packet (secondLateDecision bit label 1 earlySeen).application alice []
          (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩))⟩]
      rw [secondLate_opening_packet]
      exact List.mem_singleton.mpr rfl

include weight nonnegative in
private theorem failed_valid (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) (samplePossible : slot = 0 ∨ earlySeen = false) :
    EventGraphRuntime.State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label))
        (failedAnswerDecision bit label slot earlySeen finalSeen).application := by
  obtain ⟨bounded⟩ := LateOpeningRuntimeBindingObservationWitness.failedAnswerDecision_trace
    weight nonnegative bit label slot earlySeen finalSeen samplePossible
  have trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bounded
  obtain ⟨storedBit, storedLabel, valid⟩ := history_initial_invariant
    LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)
        ⟨14, some bob, failedAnswerDecision bit label slot earlySeen finalSeen⟩ trace
  have same : setup.eventInputs (sourceInitial storedBit storedLabel) =
      setup.eventInputs (sourceInitial bit label) :=
    valid.reachable.inputs_eq.symm.trans (failed_inputs bit label slot earlySeen finalSeen)
  rwa [same] at valid

/-- Omission has an exact audit cost on every raw receiver continuation;
neither an additional packet nor a later private response can clear it. -/
theorem failed_completion_charge (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (earlySeen finalSeen : Bool)
    (samplePossible : slot = 0 ∨ earlySeen = false) (final : app.Execution)
    (reached : final ∈ (receiverCompletion weight nonnegative players
      (failedAnswerDecision bit label slot earlySeen finalSeen)).support) :
    TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (app.finished final) alice = 1 := by
  unfold receiverCompletion at reached
  obtain ⟨middle, selected, suffix⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨response, responseSelected, rfl⟩ := PMF.support_map .. ▸ selected
  obtain ⟨bounded⟩ := LateOpeningRuntimeBindingObservationWitness.failedAnswerDecision_trace
    weight nonnegative bit label slot earlySeen finalSeen samplePossible
  have trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bounded
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ bob response trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final responded suffix
  have retained := (LateOpeningRuntimeAliceContinuation.input_persists players
    (openingMessage bit)).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) 14
      _ final ((LateOpeningRuntimeAliceContinuation.input_persists players
        (openingMessage bit)).respond _ bob response
          (failed_opening_present bit label slot earlySeen finalSeen) responseSelected) suffix
  have receipt := LateOpeningRuntimeTerminalReceipt.continuation_preserves_receipt weight
    nonnegative players 14 _ final (by
      rw [app.respond_environmentRecall]
      change 9 ≤ 12
      omega) suffix
  have unaccepted : ¬ ((alice, 0), true) ∈ final.receipts := by
    have none : LateOpeningRuntimeReliability.accepted final = false := by
      rw [receipt.2]
      unfold LateOpeningRuntimeReliability.accepted
      rw [app.respond_receipts, failedAnswerDecision_receipts]
      rfl
    exact of_decide_eq_false none
  exact unaccepted_opening_charge weight nonnegative ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
    bit retained unaccepted

/-- Successful receiver publication exposes the exact source reward event
on each actual failed-opening branch, with both sender deductions retained. -/
theorem failed_completion_payoff (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (earlySeen finalSeen : Bool)
    (samplePossible : slot = 0 ∨ earlySeen = false) (final : app.Execution)
    (reached : final ∈ (receiverCompletion weight nonnegative players
      (failedAnswerDecision bit label slot earlySeen finalSeen)).support)
    (answer : Answer)
    (published : final.application.config.store (.inr bobRevealEvent) = some (.success answer))
    (reward forfeit : ℝ) (deposit : Player → ℝ) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
      (app.finished final) alice =
        (if (label.val = 0 ∧ answer.val = 5) ∨ (label.val = 1 ∧ answer.val = 4)
          then reward else 0) - forfeit - deposit alice := by
  have charged := failed_completion_charge weight nonnegative players bit label slot earlySeen
    finalSeen samplePossible final reached
  unfold receiverCompletion at reached
  obtain ⟨middle, selected, suffix⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ selected
  have valid := failed_valid weight nonnegative bit label slot earlySeen finalSeen samplePossible
  have invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have finalValid := (ReactiveApplication.Invariant.policyInvariant app invariant players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (invariant.respond _ bob response valid) suffix
  have failedInvariant := LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks
    (.inr aliceEvent) (.failure : PublicationResult Bool)
  have failed := (ReactiveApplication.Invariant.policyInvariant app failedInvariant
    players).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ final
      (failedInvariant.respond _ bob response
        (failedAnswerDecision_publication bit label slot earlySeen finalSeen)) suffix
  obtain ⟨bounded⟩ := LateOpeningRuntimeBindingObservationWitness.failedAnswerDecision_trace
    weight nonnegative bit label slot earlySeen finalSeen samplePossible
  have trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) bounded
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 _ bob response trace
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 14 _ final responded suffix
  have complete := LateOpeningRuntimeService.completes weight nonnegative ⟨0, none, final⟩
    finalTrace ⟨rfl, rfl⟩
  have binding := bob_success_from_binding final.application _ finalValid.reachable answer published
  have decoded := decode_terminalStateOf final.application bit label .failure (.success answer)
    (.success answer) finalValid.reachable.inputs_eq failed binding published
  have readout : serviceSourceReadout setup .sequential deadline leaks (app.finished final) =
      some (terminalStateOf bit label .failure (.success answer) (.success answer)) := by
    change (if final.application.config.cut.Terminal then
      decodeState? (terminalRefs program) final.application.config.store else none) = _
    rw [ite_eq_left complete]
    exact decoded
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [charged, one_mul, nativeBaseUtility_of_readout reward forfeit _ _ readout alice,
    sourceUtility_alice_failure]

end Vegas.Examples.LateOpeningRuntimeAliceFailurePayoff
