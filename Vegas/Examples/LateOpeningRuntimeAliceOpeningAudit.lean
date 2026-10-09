/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeRetryAudit
import Vegas.Examples.LateOpeningRuntimeLatePrefix
import Vegas.Examples.LateOpeningRuntimeNash
import Vegas.Pending.ReactiveAssociationPersistence
import Interaction.ReactiveReceipts
import Interaction.ReactiveTrafficIdentity

/-! # Actual permitted Alice packets identify the immutable opening

An accepting identifier alone does not certify a synthetic envelope carrying
that identifier. The statements here concern the actual emitted envelope in
the native traffic. At terminal settlement every permitted Alice envelope is
the certified opening of her initialized binding. Accepted envelopes without
the required certificate remain forbidden by the existing audit.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
open LateOpeningRuntimeLatePrefix LateOpeningRuntimeUtility

private def AliceReceiptPayload (packet : WitnessedPacket nativeGraph) : Prop :=
  packet.tokenValid = true ∧
    (∀ candidate, packet.call ≠ .commitment aliceEvent candidate) ∧
    (∀ candidate raw, packet.call = .opening aliceEvent candidate raw →
      candidate = aliceCandidate)

private theorem accepted_payload (state next : app.State)
    (associated : state.accepted aliceBinding.field = some aliceCandidate)
    (message : Message Player app.Payload)
    (accepted : app.handle state message = some next) :
    AliceReceiptPayload message.payload := by
  change EventGraphRuntime.State nativeGraph at state next
  change Message Player (WitnessedPacket nativeGraph) at message
  have checked := reactiveApplication_handle_eq_some
    LateOpeningRuntimeService.runtime leaks state next message accepted
  refine ⟨checked.1, ?_, ?_⟩
  · intro candidate call
    have raw := checked.2
    rw [call] at raw
    have node : nodeView nativeGraph aliceEvent =
        .resolve alice .bool aliceBinding [] rfl rfl := rfl
    unfold EventGraphRuntime.handle at raw
    dsimp only at raw
    rw [node] at raw
    simp at raw
  · intro candidate raw call
    have handled := checked.2
    rw [call] at handled
    have linked : state.accepted aliceBinding.field = some candidate := by
      by_contra absent
      have node : nodeView nativeGraph aliceEvent =
          .resolve alice .bool aliceBinding [] rfl rfl := rfl
      unfold EventGraphRuntime.handle at handled
      dsimp only at handled
      rw [node] at handled
      simp only [Fin.zero_eta, Fin.isValue, withMode_inputCount, withMode_eventCount,
        dite_eq_ite, Option.dite_none_right_eq_some, Option.ite_none_right_eq_some,
        exists_and_left] at handled
      exact absent handled.2.2.2.1
    exact Option.some.inj (linked.symm.trans associated)

private theorem alice_receipts (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    control.execution.application.BindingInvariant ∧
      control.execution.application.accepted aliceBinding.field = some aliceCandidate ∧
      control.execution.ReceiptsSound app AliceReceiptPayload := by
  let preserved := app.receiptServiceInvariant
    (fun state => state.BindingInvariant ∧
      state.accepted aliceBinding.field = some aliceCandidate)
    AliceReceiptPayload
    (LateOpeningRuntimeService.runtime.reactiveAssociationInvariant
      leaks aliceBinding.field aliceCandidate)
    (fun state message next valid accepted => accepted_payload state next valid.2 message accepted)
    scheduler
  have sound := preserved.history initial horizon (by
    intro state supported
    change state ∈ (setup.initialLaw.map (fun source =>
      EventGraphRuntime.State.initial (graph := nativeGraph)
        (setup.eventInputs source))).support at supported
    obtain ⟨source, selected, rfl⟩ := PMF.support_map .. ▸ supported
    obtain ⟨bit, label, rfl⟩ := (initialLaw_support source).mp selected
    exact ⟨⟨EventGraphRuntime.State.initial_bindingInvariant _, rfl⟩,
      app.receiptsSound_initial AliceReceiptPayload _⟩) trace
  exact ⟨sound.1.1, sound.1.2, sound.2⟩

/-- A certified actual accepting receipt for Alice's event fixes the complete
public opening body, under every scheduler and arbitrary raw responses. -/
theorem certified_alice_receipt_payload (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control) (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (bit : Bool)
    (bound : aliceBinding.get? control.execution.application.config.store = some (.success bit))
    (message : Message Player app.Payload)
    (accepted : (message, (message.id, true)) ∈
      control.execution.network.ledger.zip control.execution.receipts)
    (named : message.payload.call.event? nativeGraph = some aliceEvent)
    (certified : certifiedOpening message.payload = true) :
    message.payload = (openingMessage bit).payload := by
  obtain ⟨valid, associated, sound⟩ := alice_receipts horizon scheduler control trace
  have checked := sound.certifies app AliceReceiptPayload control.execution message
    message.id accepted
  obtain ⟨event, candidate, raw, token, packet⟩ := (certifiedOpening_iff _).mp certified
  have eventEq : event = aliceEvent := by
    rw [packet] at named
    exact Option.some.inj named
  subst event
  have candidateEq : candidate = aliceCandidate := checked.2.2 candidate raw (by rw [packet])
  subst candidate
  obtain ⟨handle, linked, _, fixed⟩ := valid.success_provenance aliceBinding bit bound
  have handleEq : handle = aliceCandidate := Option.some.inj (linked.symm.trans associated)
  subst handle
  have evidenceSound := (LateOpeningRuntimeService.runtime.packetEvidence leaks).history_sound
    initial horizon scheduler trace
  have published : message ∈ control.execution.network.ledger :=
    (List.of_mem_zip accepted).1
  have verified : control.execution.application.candidates.lookup aliceCandidate =
      .openable raw := by
    apply evidenceSound.ledger message published ⟨aliceCandidate, raw⟩
    change (⟨aliceCandidate, raw⟩ : OpeningFact nativeGraph) ∈ message.payload.evidence.toList
    rw [packet]
    simp
  have rawEq : raw = (⟨.bool, bit⟩ : Raw simpleExpr) :=
    CommitmentCandidate.openable.inj (verified.symm.trans fixed)
  subst raw
  obtain ⟨namedEvent, namedCall, validToken⟩ :=
    (WitnessedPacket.tokenValid_iff _).mp checked.1
  have namedEventEq : namedEvent = aliceEvent :=
    Option.some.inj (namedCall.symm.trans named)
  subst namedEvent
  rw [packet] at validToken
  change token = some ⟨aliceEvent⟩ at validToken
  rw [packet, validToken]
  rfl

private theorem alice_owned_event (event : nativeGraph.EventId)
    (owned : nativeGraph.actor? event = some alice) : event = aliceEvent := by
  change Fin 3 at event
  fin_cases event
  · rfl
  all_goals
    change (some bob : Option Player) = some alice at owned
    exact ((by decide : bob ≠ alice) (Option.some.inj owned)).elim

/-- A permitted actual Alice traffic record at terminal settlement contains
the genuine opening, including its certificate and readiness token. -/
theorem permitted_alice_payload (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (bit : Bool)
    (bound : aliceBinding.get? control.execution.application.config.store = some (.success bit))
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = alice)
    (permitted : (LateOpeningRuntimeService.runtime.settledRecord leaks
      control.execution).permits traffic.envelope = true) :
    traffic.envelope.payload = (openingMessage bit).payload := by
  let record := LateOpeningRuntimeService.runtime.settledRecord leaks control.execution
  have permission := (record.permits_eq_true_iff traffic.envelope).mp permitted
  have settled : record.Accepts traffic.envelope.id ∧ record.SettledContent traffic.envelope := by
    cases named : traffic.envelope.payload.call.event? nativeGraph with
    | none => simp only [SettledRecord.Permits, named] at permission
    | some event =>
        simp only [SettledRecord.Permits, named] at permission
        rcases permission with unfinished | settled
        · have complete := LateOpeningRuntimeService.completes weight nonnegative
            control trace terminal
          have member : event ∈ control.execution.application.config.cut.completed := by
            rw [complete]
            exact Finset.mem_univ _
          exact (unfinished
            ((control.execution.application.config.history_exact event).mpr member)).elim
        · exact settled
  obtain ⟨event, acceptedFor, owned, _⟩ :=
    LateOpeningRuntimeService.runtime.accepting_receipt_has_owned_event leaks initial
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      control trace traffic.envelope.id settled.1
  change nativeGraph.actor? event = some traffic.envelope.sender at owned
  rw [owner] at owned
  have sameEvent := alice_owned_event event owned
  subst event
  obtain ⟨published, paired, named⟩ := acceptedFor
  have sound := (alice_receipts LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) control trace).2.2
  have sameId := (List.forall₂_zip sound paired).1
  have actual := app.traffic_envelope_eq_ledger_of_id_eq initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
    control trace traffic present published (List.of_mem_zip paired).1 sameId
  rw [← actual] at paired named
  have checked := sound.certifies app AliceReceiptPayload control.execution traffic.envelope
    traffic.envelope.id paired
  have certified : certifiedOpening traffic.envelope.payload = true := by
    cases call : traffic.envelope.payload.call with
    | commitment event candidate =>
        have eventEq : event = aliceEvent := by
          simpa only [call, Payload.event?, Option.some.injEq] using named
        subst event
        exact (checked.2.1 candidate call).elim
    | opening event candidate raw =>
        have content := settled.2
        simp only [SettledRecord.SettledContent, call] at content
        exact content.1
    | malformed raw => simp only [call, Payload.event?, reduceCtorEq] at named
  exact certified_alice_receipt_payload LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) control trace bit bound
    traffic.envelope paired named certified

/-- Every actual nongenuine Alice envelope is forbidden at terminal settlement,
even if the raw handler accepted its identifier. -/
theorem nongenuine_alice_envelope_forbidden (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (bit : Bool)
    (bound : aliceBinding.get? control.execution.application.config.store = some (.success bit))
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = alice)
    (nongenuine : traffic.envelope.payload ≠ (openingMessage bit).payload) :
    (LateOpeningRuntimeService.runtime.settledRecord leaks control.execution).permits
      traffic.envelope = false := by
  apply Bool.eq_false_iff.mpr
  intro permitted
  exact nongenuine (permitted_alice_payload weight nonnegative control trace terminal bit
    bound traffic present owner permitted)

/-- Full authentic auditing charges a nongenuine actual Alice envelope with
certainty; a later accepted opening cannot erase the charge. -/
theorem nongenuine_envelope_full_charge (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (bit : Bool)
    (bound : aliceBinding.get? control.execution.application.config.store = some (.success bit))
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = alice)
    (nongenuine : traffic.envelope.payload ≠ (openingMessage bit).payload) :
    1 ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential LateOpeningRuntimeService.deadline leaks
        (fun actual => PMF.pure actual)) (some control) alice := by
  classical
  apply LateOpeningRuntimeService.runtime.serviceAudit_charge_from_record leaks
    (fun record traffic => ((record, traffic.envelope) : SettledEvidence setup .sequential))
    (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
    (fun actual => PMF.pure actual) alice 1 _ control traffic present owner
      (nongenuine_alice_envelope_forbidden weight nonnegative control trace terminal bit
        bound traffic present owner nongenuine)
  intro actual evidence member _ _
  rw [PMF.toOuterMeasure_pure_apply]
  rw [ite_eq_left (show actual ∈ {observed | evidence ∈ observed} from member)]
  norm_num

/-- Every nongenuine packet has utility at most the gross reward range minus
Alice's deposit under arbitrary actual terminal raw behavior. -/
theorem nongenuine_envelope_utility_bound {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (terminal : app.terminal (some control)) (bit : Bool)
    (bound : aliceBinding.get? control.execution.application.config.store = some (.success bit))
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = alice)
    (nongenuine : traffic.envelope.payload ≠ (openingMessage bit).payload) :
    LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual) deposit
      (some control) alice ≤ reward - deposit alice := by
  have completed := LateOpeningRuntimeService.completes weight nonnegative control trace terminal
  obtain ⟨initialBit, label, aliceResult, binding, answer, decoded⟩ := nativeReadout_complete
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      control trace completed
  have base := nativeBaseUtility_of_readout reward forfeit (some control) _ decoded alice
  have upper := (sourceUtility_alice_bounds rewardNonnegative forfeitNonnegative
    (terminalStateOf initialBit label aliceResult binding answer)).2
  have charged := nongenuine_envelope_full_charge weight nonnegative control trace terminal bit
    bound traffic present owner nongenuine
  have penalty := mul_le_mul_of_nonneg_right charged depositNonnegative
  unfold LateOpeningRuntimeNash.payoff TerminalAudit.utility
  rw [base]
  linarith

end Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit
