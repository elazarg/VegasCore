/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveAcceptanceUniqueness
import Vegas.Examples.LateOpeningRuntimeUtility
import Vegas.Examples.LateOpeningRuntimeServiceCompletion

/-! # Additional Alice envelopes cannot remain clean after an accepted opening

Alice owns one event. At every actual terminal history, an accepted identifier
therefore rules out an accepting receipt for every other Alice identifier.
Each additional Alice envelope is forbidden by the existing settled verdict,
even if its call was a well-formed retry. Authentic auditing collects according
to its declared coverage; full traffic auditing collects with certainty.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeRetryAudit

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
open LateOpeningRuntimeUtility

private theorem alice_owned_event (event : nativeGraph.EventId)
    (owned : nativeGraph.actor? event = some alice) : event = aliceEvent := by
  change Fin 3 at event
  fin_cases event
  · rfl
  all_goals
    change (some bob : Option Player) = some alice at owned
    exact ((by decide : bob ≠ alice) (Option.some.inj owned)).elim

/-- Among all accepting receipts of an actual execution, Alice has at most
one accepted identifier. Bob's two distinct source events remain unrestricted. -/
theorem alice_accepting_receipts_unique (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (first second : MessageId Player) (firstOwner : first.1 = alice)
    (secondOwner : second.1 = alice) (one : (first, true) ∈ control.execution.receipts)
    (two : (second, true) ∈ control.execution.receipts) : first = second := by
  obtain ⟨eventOne, acceptedOne, ownedOne, _⟩ :=
    LateOpeningRuntimeService.runtime.accepting_receipt_has_owned_event leaks initial
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
        control trace first one
  obtain ⟨eventTwo, acceptedTwo, ownedTwo, _⟩ :=
    LateOpeningRuntimeService.runtime.accepting_receipt_has_owned_event leaks initial
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
        control trace second two
  rw [firstOwner] at ownedOne
  rw [secondOwner] at ownedTwo
  have eventOneEq := alice_owned_event eventOne ownedOne
  have eventTwoEq := alice_owned_event eventTwo ownedTwo
  subst eventOne
  subst eventTwo
  exact LateOpeningRuntimeService.runtime.accepting_identifiers_unique leaks initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      control trace aliceEvent first second acceptedOne acceptedTwo

/-- At an actual terminal history, every different Alice identifier is
forbidden once an Alice opening was accepted, whatever its raw call contains. -/
theorem alice_extra_envelope_forbidden (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control))
    (acceptedId : MessageId Player) (acceptedOwner : acceptedId.1 = alice)
    (accepted : (acceptedId, true) ∈ control.execution.receipts)
    (message : Message Player app.Payload) (owner : message.sender = alice)
    (different : message.id ≠ acceptedId) :
    (LateOpeningRuntimeService.runtime.settledRecord leaks control.execution).permits message =
      false := by
  let record := LateOpeningRuntimeService.runtime.settledRecord leaks control.execution
  have unaccepted : ¬ record.Accepts message.id := by
    intro receipt
    exact different (alice_accepting_receipts_unique weight nonnegative control trace
      message.id acceptedId owner acceptedOwner receipt accepted)
  cases named : message.payload.call.event? nativeGraph with
  | none => exact SettledRecord.permits_eq_false_of_none record message named
  | some event =>
      have completed :=
        LateOpeningRuntimeService.completes weight nonnegative control trace terminal
      have finished : event ∈ control.execution.application.config.cut.completed := by
        rw [completed]
        exact Finset.mem_univ _
      have settled : event ∈ record.view.observation.completionOrder :=
        (control.execution.application.config.history_exact event).mpr finished
      exact SettledRecord.permits_eq_false_of_settled record message event named settled
        (fun permitted => unaccepted permitted.1)

/-- The extra envelope is detected by the actual settled audit with at least
the sample's coverage probability. No independence assumption is required. -/
theorem alice_extra_envelope_charge
    (weight : ℝ) (nonnegative : 0 ≤ weight)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (rate : ℝ)
    (coverage : ∀ actual evidence, evidence ∈ actual → evidence.2.sender = alice →
      evidence.1.permits evidence.2 = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | evidence ∈ observed}).toReal)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control))
    (acceptedId : MessageId Player) (acceptedOwner : acceptedId.1 = alice)
    (accepted : (acceptedId, true) ∈ control.execution.receipts)
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = alice) (different : traffic.envelope.id ≠ acceptedId) :
    rate ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks sample)
      (some control) alice := by
  exact LateOpeningRuntimeService.runtime.serviceAudit_charge_from_record leaks
    (fun record traffic => ((record, traffic.envelope) : SettledEvidence setup .sequential))
    (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
    sample alice rate coverage control traffic present owner
    (alice_extra_envelope_forbidden weight nonnegative control trace terminal
      acceptedId acceptedOwner accepted traffic.envelope owner different)

/-- Reading all actual traffic detects an extra Alice envelope with certainty.
This is one authentic audit instance; partial auditing uses the previous bound. -/
theorem alice_extra_envelope_full_charge
    (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control))
    (acceptedId : MessageId Player) (acceptedOwner : acceptedId.1 = alice)
    (accepted : (acceptedId, true) ∈ control.execution.receipts)
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = alice) (different : traffic.envelope.id ≠ acceptedId) :
    1 ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
        (fun actual => PMF.pure actual)) (some control) alice := by
  classical
  apply alice_extra_envelope_charge weight nonnegative (fun actual => PMF.pure actual) 1
    _ control trace terminal acceptedId acceptedOwner accepted traffic present owner different
  intro actual evidence member _ _
  rw [PMF.toOuterMeasure_pure_apply]
  rw [ite_eq_left (show actual ∈ {observed | evidence ∈ observed} from member)]
  norm_num

/-- Every unaccepted envelope is forbidden once this actual service has
finished the source program. This also covers packets naming no event. -/
theorem terminal_unaccepted_envelope_forbidden (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (message : Message Player app.Payload)
    (unaccepted : (message.id, true) ∉ control.execution.receipts) :
    (LateOpeningRuntimeService.runtime.settledRecord leaks control.execution).permits message =
      false := by
  let record := LateOpeningRuntimeService.runtime.settledRecord leaks control.execution
  cases named : message.payload.call.event? nativeGraph with
  | none => exact SettledRecord.permits_eq_false_of_none record message named
  | some event =>
      have completed :=
        LateOpeningRuntimeService.completes weight nonnegative control trace terminal
      have finished : event ∈ control.execution.application.config.cut.completed := by
        rw [completed]
        exact Finset.mem_univ _
      have settled : event ∈ record.view.observation.completionOrder :=
        (control.execution.application.config.history_exact event).mpr finished
      exact SettledRecord.permits_eq_false_of_settled record message event named settled
        (fun permitted => unaccepted permitted.1)

/-- Two distinct Alice identifiers in actual traffic force a breach whether
or not the lottery accepted either of them. A canonical retry is included. -/
theorem alice_two_envelopes_charge
    (weight : ℝ) (nonnegative : 0 ≤ weight)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (rate : ℝ)
    (coverage : ∀ actual evidence, evidence ∈ actual → evidence.2.sender = alice →
      evidence.1.permits evidence.2 = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | evidence ∈ observed}).toReal)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control))
    (first second : app.TrafficRecord)
    (firstPresent : first ∈ app.executionTraffic control.execution)
    (secondPresent : second ∈ app.executionTraffic control.execution)
    (firstOwner : first.envelope.sender = alice) (secondOwner : second.envelope.sender = alice)
    (different : first.envelope.id ≠ second.envelope.id) :
    rate ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks sample)
      (some control) alice := by
  by_cases accepted : (first.envelope.id, true) ∈ control.execution.receipts
  · exact alice_extra_envelope_charge weight nonnegative sample rate coverage control trace
      terminal first.envelope.id firstOwner accepted second secondPresent secondOwner different.symm
  · exact LateOpeningRuntimeService.runtime.serviceAudit_charge_from_record leaks
      (fun record traffic => ((record, traffic.envelope) : SettledEvidence setup .sequential))
      (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
      sample alice rate coverage control first firstPresent firstOwner
      (terminal_unaccepted_envelope_forbidden weight nonnegative control trace terminal
        first.envelope accepted)

theorem alice_two_envelopes_full_charge
    (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control))
    (first second : app.TrafficRecord)
    (firstPresent : first ∈ app.executionTraffic control.execution)
    (secondPresent : second ∈ app.executionTraffic control.execution)
    (firstOwner : first.envelope.sender = alice) (secondOwner : second.envelope.sender = alice)
    (different : first.envelope.id ≠ second.envelope.id) :
    1 ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
        (fun actual => PMF.pure actual)) (some control) alice := by
  classical
  apply alice_two_envelopes_charge weight nonnegative (fun actual => PMF.pure actual) 1
    _ control trace terminal first second firstPresent secondPresent
      firstOwner secondOwner different
  intro actual evidence member _ _
  rw [PMF.toOuterMeasure_pure_apply]
  rw [ite_eq_left (show actual ∈ {observed | evidence ∈ observed} from member)]
  norm_num

/-- Under full traffic auditing, a second Alice packet has terminal utility
at most the gross reward range minus her deposit, under every raw continuation. -/
theorem alice_two_envelopes_utility_bound
    {reward forfeit : ℝ} (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control))
    (first second : app.TrafficRecord)
    (firstPresent : first ∈ app.executionTraffic control.execution)
    (secondPresent : second ∈ app.executionTraffic control.execution)
    (firstOwner : first.envelope.sender = alice) (secondOwner : second.envelope.sender = alice)
    (different : first.envelope.id ≠ second.envelope.id) :
    TerminalAudit.utility (nativeBaseUtility reward forfeit)
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
        (fun actual => PMF.pure actual)) deposit (some control) alice ≤
          reward - deposit alice := by
  have completed := LateOpeningRuntimeService.completes weight nonnegative control trace terminal
  obtain ⟨bit, label, aliceResult, binding, answer, decoded⟩ := nativeReadout_complete
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      control trace completed
  have base := nativeBaseUtility_of_readout reward forfeit (some control) _ decoded alice
  have bound := (sourceUtility_alice_bounds rewardNonnegative forfeitNonnegative
    (terminalStateOf bit label aliceResult binding answer)).2
  have charged := alice_two_envelopes_full_charge weight nonnegative control trace terminal
    first second firstPresent secondPresent firstOwner secondOwner different
  have penalty := mul_le_mul_of_nonneg_right charged depositNonnegative
  unfold TerminalAudit.utility
  rw [base]
  linarith

end Vegas.Examples.LateOpeningRuntimeRetryAudit
