/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy
import Vegas.Pending.ReactiveOpeningEvidence
import Vegas.Pending.EventBindingInvariant

/-! # Canonical certified opening packets

The public format admits only an opening with its exactly matching certificate.
Accepted packets in this format identify the current binding's fixed value.
Owned and forwarded requests for that certificate have the same semantic normal
form, without assuming an empty known-packet list or a particular value type.

This is a packet-format theorem. Readiness, deadlines and source conformance
remain separate obligations. In particular, a truthful opening can still yield
guard-rejected publication failure; identifying it with a source opening requires
guard-free code or a proof that the publication checks succeed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The packet admits neither missing/mismatching evidence nor another call kind.
It does not inspect a private expected value, event phase, or source strategy. -/
def certifiedOpening (packet : WitnessedPacket graph) : Bool :=
  match packet.call, packet.evidence with
  | .opening _ candidate raw, some fact => decide (fact = ⟨candidate, raw⟩)
  | _, _ => false

theorem certifiedOpening_iff (packet : WitnessedPacket graph) :
    certifiedOpening packet = true ↔
      ∃ event candidate raw token, packet =
        ⟨.opening event candidate raw, some ⟨candidate, raw⟩, token⟩ := by
  constructor
  · intro conforming
    rcases packet with ⟨call, evidence, token⟩
    cases call <;> cases evidence <;>
      simp only [certifiedOpening, Bool.false_eq_true, decide_eq_true_eq] at conforming
    rename_i event candidate raw fact
    subst fact
    exact ⟨event, candidate, raw, token, rfl⟩
  · rintro ⟨event, candidate, raw, token, rfl⟩
    simp only [certifiedOpening, decide_true]

theorem disclosureSubmission_certified (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (owned : candidate.1 = who)
    (fixed : state.candidates.lookup candidate = .openable raw) :
    certifiedOpening ((disclosureSubmission (.opening event candidate raw)).emit
      state who known) = true := by
  have verified := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr fixed
  simp only [disclosureSubmission, WitnessedSubmission.emit, owned, verified,
    and_self, ↓reduceIte, certifiedOpening, decide_true]

private theorem opening_submit_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player) (submission : WitnessedSubmission graph)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (opening : submission.call.packet = .opening event candidate raw) :
    (runtime.reactiveApplication leaks).submit state who submission = state := by
  rcases submission with ⟨⟨packet, material⟩, evidence⟩
  dsimp only at opening
  subst packet
  cases material <;> rfl

/-- Honest owned emission remains certified after semantic normalization, even
when the representative is a forwarding request for a previously known fact. -/
theorem normalized_disclosureSubmission_certified (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (owned : candidate.1 = who)
    (fixed : state.candidates.lookup candidate = .openable raw) :
    certifiedOpening
      (((disclosureSubmission (.opening event candidate raw)).normalizeReactive who
        ((runtime.reactiveApplication leaks).observePlayer state who) known).emit
          state who known) = true := by
  have packet := WitnessedSubmission.normalizeReactive_emit runtime leaks state who known
    (disclosureSubmission (.opening event candidate raw))
  have unchanged := opening_submit_eq runtime leaks state who
    (disclosureSubmission (.opening event candidate raw)) event candidate raw rfl
  change (runtime.reactiveApplication leaks).submit state who
    (disclosureSubmission (.opening event candidate raw)) = state at unchanged
  change ((disclosureSubmission (.opening event candidate raw)).normalizeReactive who
      ((runtime.reactiveApplication leaks).observePlayer state who) known).emit
      ((runtime.reactiveApplication leaks).submit state who
        (disclosureSubmission (.opening event candidate raw))) who known = _ at packet
  rw [unchanged] at packet
  rw [packet]
  exact disclosureSubmission_certified state who known event candidate raw owned fixed

/-- An accepted opening at this resolve node must use its accepted handle and
that handle's fixed meaning. Values, owners and handle slots are unrestricted. -/
theorem accepted_opening_identifies (runtime : EventGraphRuntime graph)
    (state next : State graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (raw : Raw L)
    (associated : state.accepted binding.field = some candidate)
    (fixed : state.candidates.lookup candidate = .openable raw)
    (id : MessageId Player) (submitted : Handle graph) (claimed : Raw L)
    (accepted : runtime.handle state ⟨id, .opening event submitted claimed⟩ = some next) :
    submitted = candidate ∧ claimed = raw := by
  have linked : state.accepted binding.field = some submitted := by
    by_contra absent
    simp [handle, node, absent] at accepted
  have same : submitted = candidate := Option.some.inj (linked.symm.trans associated)
  subst submitted
  have verified := runtime.handle_opening_verified state next id event candidate claimed accepted
  exact ⟨rfl, CommitmentCandidate.openable.inj (verified.symm.trans fixed)⟩

private theorem normalize_opening_of_matching_packet
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (token : Option (ReadinessToken graph))
    (emitted : submission.emit state who known =
      ⟨.opening event candidate raw, some ⟨candidate, raw⟩, token⟩)
    (owned : candidate.1 = who) (fixed : state.candidates.lookup candidate = .openable raw) :
    submission.normalizeReactive who ((runtime.reactiveApplication leaks).observePlayer state who)
        known =
      (disclosureSubmission (.opening event candidate raw)).normalizeReactive who
        ((runtime.reactiveApplication leaks).observePlayer state who) known := by
  have call := congrArg WitnessedPacket.call emitted
  change submission.call.packet = .opening event candidate raw at call
  rcases submission with ⟨⟨packet, material⟩, evidence⟩
  dsimp only at call
  subst packet
  have evidenceEq := congrArg WitnessedPacket.evidence emitted
  rw [WitnessedSubmission.emit_eq_resolve] at evidenceEq
  change evidence.resolve who (fun slot => state.candidates.lookup (who, slot)) known =
    some ⟨candidate, raw⟩ at evidenceEq
  have localFixed : state.candidates.lookup (who, candidate.2) = .openable raw := by
    simpa only [← owned] using fixed
  simp only [WitnessedSubmission.normalizeReactive, Submission.normalizeReactive,
    openingEffective, ↓reduceIte, Submission.candidateAfter_opening, disclosureSubmission]
  congr 1
  apply (EvidenceRequest.normalize_eq_iff_resolve_eq ..).mpr
  change evidence.resolve who (fun slot => state.candidates.lookup (who, slot)) known =
    (EvidenceRequest.owned ⟨candidate, raw⟩).resolve who
      (fun slot => state.candidates.lookup (who, slot)) known
  rw [evidenceEq]
  simp only [EvidenceRequest.resolve, owned, localFixed, and_self, ↓reduceIte]

/-- Every accepted, certified current opening has the canonical normalized
submission, whether its certificate request used ownership or forwarding.
The original submission need not already be normalized. -/
theorem accepted_certified_opening_normalization
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state next : State graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (raw : Raw L)
    (associated : state.accepted binding.field = some candidate) (owned : candidate.1 = owner)
    (fixed : state.candidates.lookup candidate = .openable raw)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (serial : Nat)
    (addressed : submission.call.packet.event? graph = some event)
    (conforming : certifiedOpening (submission.emit
      ((runtime.reactiveApplication leaks).submit state owner submission) owner known) = true)
    (accepted : (runtime.reactiveApplication leaks).handle
      ((runtime.reactiveApplication leaks).submit state owner submission)
      ⟨(owner, serial), submission.emit
        ((runtime.reactiveApplication leaks).submit state owner submission) owner known⟩ =
      some next) :
    submission.normalizeReactive owner
        ((runtime.reactiveApplication leaks).observePlayer state owner) known =
      (disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
        ((runtime.reactiveApplication leaks).observePlayer state owner) known := by
  obtain ⟨actual, submitted, claimed, token, emitted⟩ := (certifiedOpening_iff _).mp conforming
  have call := congrArg WitnessedPacket.call emitted
  change submission.call.packet = .opening actual submitted claimed at call
  rw [call] at addressed
  have eventEq : actual = event := Option.some.inj addressed
  subst actual
  have unchanged := opening_submit_eq runtime leaks state owner submission event submitted
    claimed call
  rw [unchanged] at emitted accepted
  rw [emitted] at accepted
  have identifiers := runtime.accepted_opening_identifies state next owner event payload
    binding checks outputEq codeEq node candidate raw associated fixed (owner, serial)
      submitted claimed (reactiveHandle_call accepted)
  rcases identifiers with ⟨sameHandle, sameRaw⟩
  subst submitted
  subst claimed
  exact normalize_opening_of_matching_packet runtime leaks state owner known submission event
    candidate raw token emitted owned fixed

/-- Successful initialized or earlier source bindings supply the expected
handle and value through the existing runtime binding invariant. -/
theorem accepted_certified_opening_of_binding_success
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state next : State graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (invariant : state.BindingInvariant) (value : L.Val payload)
    (stored : binding.get? state.config.store = some (.success value))
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (serial : Nat)
    (addressed : submission.call.packet.event? graph = some event)
    (conforming : certifiedOpening (submission.emit
      ((runtime.reactiveApplication leaks).submit state owner submission) owner known) = true)
    (accepted : (runtime.reactiveApplication leaks).handle
      ((runtime.reactiveApplication leaks).submit state owner submission)
      ⟨(owner, serial), submission.emit
        ((runtime.reactiveApplication leaks).submit state owner submission) owner known⟩ =
      some next) :
    ∃ candidate, state.accepted binding.field = some candidate ∧ candidate.1 = owner ∧
      submission.normalizeReactive owner
          ((runtime.reactiveApplication leaks).observePlayer state owner) known =
        (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive owner
          ((runtime.reactiveApplication leaks).observePlayer state owner) known := by
  obtain ⟨candidate, associated, owned, fixed⟩ := invariant.success_provenance binding value stored
  exact ⟨candidate, associated, owned,
    runtime.accepted_certified_opening_normalization leaks state next owner event payload
      binding checks outputEq codeEq node candidate ⟨payload, value⟩ associated owned fixed
      known submission serial addressed conforming accepted⟩

/-- Evidence-free withholding has one semantic normal form, regardless of
private material or whether an unsuccessful certificate request was made. -/
theorem withhold_normalization_of_empty_evidence
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (event : graph.EventId)
    (withheld : submission.call.packet = .withhold event)
    (empty : (submission.emit
      ((runtime.reactiveApplication leaks).submit state who submission) who known).evidence =
        none) :
    submission.normalizeReactive who ((runtime.reactiveApplication leaks).observePlayer state who)
        known = disclosureSubmission (.withhold event) := by
  rcases submission with ⟨⟨packet, material⟩, evidence⟩
  dsimp only at withheld
  subst packet
  rw [WitnessedSubmission.emit_eq_resolve] at empty
  change evidence.resolve who (fun slot => state.candidates.lookup (who, slot)) known = none
    at empty
  simp only [WitnessedSubmission.normalizeReactive, Submission.normalizeReactive,
    openingEffective, ↓reduceIte, disclosureSubmission]
  congr 1
  change evidence.normalize who (fun slot => state.candidates.lookup (who, slot)) known =
    EvidenceRequest.none
  rw [← EvidenceRequest.normalize_none who (fun slot => state.candidates.lookup (who, slot))
    known]
  exact (EvidenceRequest.normalize_eq_iff_resolve_eq ..).mpr empty

/-- Exhaustive classification of a newly submitted current-event packet.
An extra semantic normal form either yields a rejected call or violates the
static public format. No restriction is imposed on raw certificate requests,
private material, value types, or the sender's known packets. -/
theorem current_opening_submission_cases
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (raw : Raw L)
    (associated : state.accepted binding.field = some candidate) (owned : candidate.1 = owner)
    (fixed : state.candidates.lookup candidate = .openable raw)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (serial : Nat)
    (addressed : submission.call.packet.event? graph = some event) :
    submission.normalizeReactive owner
        ((runtime.reactiveApplication leaks).observePlayer state owner) known =
      (disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
        ((runtime.reactiveApplication leaks).observePlayer state owner) known ∨
    (runtime.reactiveApplication leaks).handle
      ((runtime.reactiveApplication leaks).submit state owner submission)
      ⟨(owner, serial), submission.emit
        ((runtime.reactiveApplication leaks).submit state owner submission) owner known⟩ = none ∨
    certifiedOpening (submission.emit
      ((runtime.reactiveApplication leaks).submit state owner submission) owner known) = false := by
  cases conforming : certifiedOpening (submission.emit
      ((runtime.reactiveApplication leaks).submit state owner submission) owner known) with
  | false => exact Or.inr (Or.inr rfl)
  | true =>
      cases accepted : (runtime.reactiveApplication leaks).handle
          ((runtime.reactiveApplication leaks).submit state owner submission)
          ⟨(owner, serial), submission.emit
            ((runtime.reactiveApplication leaks).submit state owner submission) owner known⟩ with
      | none => exact Or.inr (Or.inl rfl)
      | some next =>
          exact Or.inl (runtime.accepted_certified_opening_normalization leaks state next owner
            event payload binding checks outputEq codeEq node candidate raw associated owned fixed
            known submission serial addressed conforming accepted)

end Vegas.EventGraphRuntime
