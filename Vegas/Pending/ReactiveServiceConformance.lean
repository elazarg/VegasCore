/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveGuardConformance
import Vegas.Pending.ReactiveBindingClassification
import Vegas.Pending.ReactiveSubmissionSerial

/-! # Public conformance for binding and guarded disclosure phases

The checker reads the public view, its prior ledger and a signed envelope. It
admits, for a ready event within its deadline, the first canonical opaque
binding regardless of hidden opening material, and one certified opening whose
public guards succeed. Authorization is readiness: no service cursor is
consulted, so conformance does not depend on how an order serves ready events.
Already published envelopes and copies of the current pending envelope remain
permitted. Serial evidence detects another fresh envelope without requiring
the auditor to have sampled the earlier one; it counts distinct identifiers,
so a chain that includes a copy of a published envelope again does not shift
any author's expected serial. Omitted binding obligations are
handled separately by actual deadline evidence.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)

/-- Packet conformance uses no private candidate value or source strategy. -/
def freshServiceEnvelope (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  match message.payload.call with
  | .commitment _event candidate =>
      view.BindingIncludable runtime ⟨message.id, message.payload.call⟩ ∧
      candidate = (message.sender, .prepared (view.bindingCount message.sender)) ∧
      message.payload.evidence = none
  | .opening event candidate raw =>
      view.EventReady event ∧
      (match view.activatedAt event with
        | none => False
        | some entered => view.clock - entered < runtime.deadline event) ∧
      certifiedOpening message.payload = true ∧
      view.openingGuardsAccepted message.payload = true ∧
      (match nodeView graph event with
        | .resolve owner payload binding _ _ _ =>
            message.sender = owner ∧ candidate.1 = owner ∧
            view.accepted binding.field = some candidate ∧ raw.ty = payload
        | .bind .. | .sample .. => False)
  | .withhold .. | .malformed .. => False

open Classical in
/-- A replay carries its original author's serial. The checker does not
attribute a fresh violation to that author merely because someone rebroadcasts.
A fresh envelope's serial must equal the number of distinct identifiers of its
author already on the ledger (`Interaction.Message.distinctAuthoredCount`), the
number of the author's calls the contract has processed; repeated inclusions of
one envelope do not advance it. -/
def permittedServiceEnvelope (view : PublicView graph)
    (ledger : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph)) : Bool :=
  decide (message.id ∈ ledger.map Message.id ∨
    (message.id.2 = Message.distinctAuthoredCount ledger message.sender ∧
      runtime.freshServiceEnvelope view message))

theorem permittedServiceEnvelope_iff (view : PublicView graph)
    (ledger : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph)) :
    runtime.permittedServiceEnvelope view ledger message = true ↔
      message.id ∈ ledger.map Message.id ∨
        (message.id.2 = Message.distinctAuthoredCount ledger message.sender ∧
          runtime.freshServiceEnvelope view message) := by
  classical
  simp only [permittedServiceEnvelope, decide_eq_true_eq]

theorem permittedServiceEnvelope_published (view : PublicView graph)
    (ledger : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph))
    (published : message.id ∈ ledger.map Message.id) :
    runtime.permittedServiceEnvelope view ledger message = true :=
  (runtime.permittedServiceEnvelope_iff view ledger message).mpr (Or.inl published)

theorem permittedServiceEnvelope_unpublished_iff (view : PublicView graph)
    (ledger : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph))
    (unpublished : message.id ∉ ledger.map Message.id) :
    runtime.permittedServiceEnvelope view ledger message = true ↔
      message.id.2 = Message.distinctAuthoredCount ledger message.sender ∧
        runtime.freshServiceEnvelope view message := by
  rw [runtime.permittedServiceEnvelope_iff]
  simp only [unpublished, false_or]

theorem permittedServiceEnvelope_wrong_serial (view : PublicView graph)
    (ledger : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph))
    (unpublished : message.id ∉ ledger.map Message.id)
    (wrong : message.id.2 ≠ Message.distinctAuthoredCount ledger message.sender) :
    runtime.permittedServiceEnvelope view ledger message = false := by
  classical
  simp only [permittedServiceEnvelope, unpublished, wrong, false_and, or_self, decide_false]

theorem freshServiceEnvelope_binding_iff (view : PublicView graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) :
    runtime.freshServiceEnvelope view ⟨id, ⟨.commitment event candidate, evidence⟩⟩ ↔
      view.BindingIncludable runtime ⟨id, .commitment event candidate⟩ ∧
      candidate = (id.1, .prepared (view.bindingCount id.1)) ∧ evidence = none := Iff.rfl

/-- Every conforming fresh commitment has one fixed public packet. Private
material is intentionally unrestricted and remains the repair proof's concern. -/
theorem freshServiceEnvelope_binding_packet
    (view : PublicView graph) (id : MessageId Player) (event : graph.EventId)
    (candidate : Handle graph) (evidence : Option (OpeningFact graph))
    (permitted : runtime.freshServiceEnvelope view
      ⟨id, ⟨.commitment event candidate, evidence⟩⟩) :
    (⟨.commitment event candidate, evidence⟩ : WitnessedPacket graph) =
      ⟨.commitment event (id.1, .prepared (view.bindingCount id.1)), none⟩ := by
  obtain ⟨_, allocated, empty⟩ :=
    (runtime.freshServiceEnvelope_binding_iff view id event candidate evidence).mp permitted
  rw [allocated, empty]

/-- Every conforming fresh call names a publicly ready event. -/
theorem freshServiceEnvelope_ready (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph))
    (permitted : runtime.freshServiceEnvelope view message) :
    ∃ event, message.payload.call.event? graph = some event ∧ view.EventReady event := by
  cases call : message.payload.call with
  | commitment event candidate =>
      simp only [freshServiceEnvelope, call, PublicView.BindingIncludable] at permitted
      exact ⟨event, rfl, permitted.1.1⟩
  | opening event candidate raw =>
      simp only [freshServiceEnvelope, call] at permitted
      exact ⟨event, rfl, permitted.1⟩
  | withhold event | malformed =>
      simp only [freshServiceEnvelope, call] at permitted

/-- Every conforming fresh call names a ready event whose actor is its sender. -/
theorem freshServiceEnvelope_owned (view : PublicView graph)
    (message : Message Player (WitnessedPacket graph))
    (permitted : runtime.freshServiceEnvelope view message) :
    ∃ event, message.payload.call.event? graph = some event ∧ view.EventReady event ∧
      graph.actor? event = some message.sender := by
  cases call : message.payload.call with
  | commitment event candidate =>
      simp only [freshServiceEnvelope, call] at permitted
      have bound := permitted.1
      simp only [PublicView.BindingIncludable] at bound
      cases node : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          simp only [node] at bound
          have authored : message.sender = owner := bound.2.2.1
          have actor := congrArg EventCode.actor codeEq
          rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
          exact ⟨event, rfl, bound.1, authored ▸ actor⟩
      | sample payload kernel outputEq codeEq =>
          simp only [node, and_false] at bound
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [node, and_false] at bound
  | opening event candidate raw =>
      simp only [freshServiceEnvelope, call] at permitted
      cases node : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          simp only [node, and_false] at permitted
      | sample payload kernel outputEq codeEq =>
          simp only [node, and_false] at permitted
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [node] at permitted
          have authored : message.sender = owner := permitted.2.2.2.2.1
          have actor := congrArg EventCode.actor codeEq
          rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
          exact ⟨event, rfl, permitted.1, authored ▸ actor⟩
  | withhold event | malformed =>
      simp only [freshServiceEnvelope, call] at permitted

/-- While one event is the only ready event, every conforming fresh call names
it, whoever sends it. -/
theorem freshServiceEnvelope_event_of_sole (view : PublicView graph) (event : graph.EventId)
    (sole : view.SoleReady event) (message : Message Player (WitnessedPacket graph))
    (permitted : runtime.freshServiceEnvelope view message) :
    message.payload.call.event? graph = some event := by
  obtain ⟨named, addressed, ready⟩ := runtime.freshServiceEnvelope_ready view message permitted
  rw [addressed, sole.2 named ready]

/-- When one event is the only ready event owned by the sender, every
conforming fresh call names it. Under the barrier order each player owns at
most one ready event, and a ready public event is the only ready event. -/
theorem freshServiceEnvelope_event_of_owned_unique (view : PublicView graph)
    (event : graph.EventId) (message : Message Player (WitnessedPacket graph))
    (unique : ∀ other, view.EventReady other → graph.actor? other = some message.sender →
      other = event)
    (permitted : runtime.freshServiceEnvelope view message) :
    message.payload.call.event? graph = some event := by
  obtain ⟨named, addressed, ready, actor⟩ := runtime.freshServiceEnvelope_owned view message
    permitted
  rw [addressed, unique named ready actor]

/-- For a call addressed to a binding node, the public checker determines the
entire emitted packet and its author, without an assumed packet-shape premise. -/
theorem freshServiceEnvelope_binding_shape
    (view : PublicView graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (message : Message Player (WitnessedPacket graph))
    (named : message.payload.call.event? graph = some event)
    (permitted : runtime.freshServiceEnvelope view message) :
    message.sender = owner ∧ message.payload =
      ⟨.commitment event (owner, .prepared (view.bindingCount owner)), none⟩ := by
  rcases message with ⟨id, ⟨packet, evidence⟩⟩
  cases packet with
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      have allowed := (runtime.freshServiceEnvelope_binding_iff view id event candidate
        evidence).mp permitted
      have includable := allowed.1
      simp only [PublicView.BindingIncludable, node] at includable
      have authored : id.1 = owner := includable.2.2.1
      refine ⟨authored, ?_⟩
      have canonical := runtime.freshServiceEnvelope_binding_packet view id event candidate
        evidence permitted
      simpa only [authored] using canonical
  | opening actual candidate raw =>
      change some actual = some event at named
      cases Option.some.inj named
      simp only [freshServiceEnvelope, node, and_false] at permitted
  | withhold actual | malformed =>
      simp only [freshServiceEnvelope] at permitted

/-- A public canonical binding remains acceptable for every private opening
that emits this packet, including missing or mistyped material. -/
theorem permittedServiceEnvelope_binding
    (state : State graph) (who : Player) (event : graph.EventId)
    (ledger : List (Message Player (WitnessedPacket graph))) (serial : Nat)
    (includable : state.publicView.BindingIncludable runtime
      ⟨(who, serial), .commitment event (who, .prepared (state.publicView.bindingCount who))⟩)
    (counted : serial = Message.distinctAuthoredCount ledger who) :
    runtime.permittedServiceEnvelope state.publicView ledger
      ⟨(who, serial),
        ⟨.commitment event (who, .prepared (state.publicView.bindingCount who)), none⟩⟩ = true :=
  (runtime.permittedServiceEnvelope_iff _ _ _).mpr
    (Or.inr ⟨counted, includable, rfl, rfl⟩)

/-- The opening branch exposes exactly the phase, association, certificate and
public-guard facts used by the existing guarded-response classification. -/
theorem freshServiceEnvelope_opening_iff
    (view : PublicView graph) (id : MessageId Player) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (raw : Raw L) (evidence : Option (OpeningFact graph)) :
    runtime.freshServiceEnvelope view ⟨id, ⟨.opening event candidate raw, evidence⟩⟩ ↔
      view.EventReady event ∧
      (match view.activatedAt event with
        | none => False
        | some entered => view.clock - entered < runtime.deadline event) ∧
      certifiedOpening (⟨.opening event candidate raw, evidence⟩ : WitnessedPacket graph) = true ∧
      view.openingGuardsAccepted ⟨.opening event candidate raw, evidence⟩ = true ∧
      id.1 = owner ∧ candidate.1 = owner ∧
      view.accepted binding.field = some candidate ∧ raw.ty = payload := by
  simp only [freshServiceEnvelope, node, Message.sender]

/-- A conforming packet at a resolve phase is necessarily the currently
associated, certified, publicly validated opening. -/
theorem freshServiceEnvelope_resolution_shape
    (view : PublicView graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (message : Message Player (WitnessedPacket graph))
    (named : message.payload.call.event? graph = some event)
    (permitted : runtime.freshServiceEnvelope view message) :
    ∃ candidate raw, message.sender = owner ∧ candidate.1 = owner ∧
      view.accepted binding.field = some candidate ∧ raw.ty = payload ∧
      message.payload = ⟨.opening event candidate raw, some ⟨candidate, raw⟩⟩ ∧
      view.openingGuardsAccepted message.payload = true := by
  rcases message with ⟨id, ⟨packet, evidence⟩⟩
  cases packet with
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      simp only [freshServiceEnvelope, PublicView.BindingIncludable, node, and_false,
        false_and] at permitted
  | opening actual candidate raw =>
      change some actual = some event at named
      cases Option.some.inj named
      obtain ⟨_, _, certified, guards, authored, owned, associated, typed⟩ :=
        (runtime.freshServiceEnvelope_opening_iff view id event owner payload binding checks
          outputEq codeEq node candidate raw evidence).mp permitted
      have evidenceEq : evidence = some ⟨candidate, raw⟩ := by
        cases evidence with
        | none => simp only [certifiedOpening, Bool.false_eq_true] at certified
        | some fact =>
            simp only [certifiedOpening, decide_eq_true_eq] at certified
            exact congrArg some certified
      refine ⟨candidate, raw, authored, owned, associated, typed, ?_, guards⟩
      rw [evidenceEq]
  | withhold actual | malformed =>
      simp only [freshServiceEnvelope] at permitted

/-- Submission normalization cannot hide another public evidence choice under
a conforming first commitment packet. -/
theorem normalize_binding_at_servicePhase
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq) (serial : Nat)
    (fresh : state.candidates.lookup (who, .prepared (state.publicView.bindingCount who)) = .fresh)
    (named : (submission.emit ((runtime.reactiveApplication leaks).submit state who submission)
      who known).call.event? graph = some event)
    (permitted : runtime.freshServiceEnvelope state.publicView
      ⟨(who, serial), submission.emit
        ((runtime.reactiveApplication leaks).submit state who submission) who known⟩) :
    submission.normalizeReactive who
        ((runtime.reactiveApplication leaks).observePlayer state who) known =
      ⟨⟨.commitment event (who, .prepared (state.publicView.bindingCount who)),
        submission.call.opening⟩, .none⟩ := by
  apply runtime.normalize_binding_of_canonical_packet leaks state who known submission event
    (state.publicView.bindingCount who) fresh
  exact (runtime.freshServiceEnvelope_binding_shape state.publicView who event payload outputEq
    codeEq node _ named permitted).2

end Vegas.EventGraphRuntime
