/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.OpeningEvidence

/-! # Canonical requests for the certificate actually disclosed

Successful requests first use an available forwarding reference, falling back
to owned issuance. Forwarding is resolved by the network's first-match lookup,
including on inconsistent lists that are not reachable network observations.
Choosing a known reference keeps normalization inside every bounded raw menu.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.EvidenceRequest

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def forwardedEvidence (known : List (Message Player (WitnessedPacket graph)))
    (id : MessageId Player) : Option (OpeningFact graph) :=
  (known.find? fun message => message.id = id).bind fun message => message.payload.evidence

open Classical in
def resolve (who : Player) (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) :
    EvidenceRequest graph → Option (OpeningFact graph)
  | .none => Option.none
  | .owned fact =>
      if fact.handle.1 = who ∧ candidates fact.handle.2 = .openable fact.raw then some fact
      else Option.none
  | .forward id => forwardedEvidence known id

open Classical in
def forwardingPacket (known : List (Message Player (WitnessedPacket graph)))
    (fact : OpeningFact graph) : Option (Message Player (WitnessedPacket graph)) :=
  known.find? fun message => forwardedEvidence known message.id = some fact

def canonical (known : List (Message Player (WitnessedPacket graph))) :
    Option (OpeningFact graph) → EvidenceRequest graph
  | .none => .none
  | some fact => match forwardingPacket known fact with
    | some message => .forward message.id
    | .none => .owned fact

def normalize (who : Player) (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (request : EvidenceRequest graph) :
    EvidenceRequest graph := canonical known (request.resolve who candidates known)

theorem forwardingPacket_mem (known : List (Message Player (WitnessedPacket graph)))
    (fact : OpeningFact graph) (message : Message Player (WitnessedPacket graph))
    (found : forwardingPacket known fact = some message) : message ∈ known :=
  List.mem_of_find?_eq_some found

theorem forwardingPacket_resolves (known : List (Message Player (WitnessedPacket graph)))
    (fact : OpeningFact graph) (message : Message Player (WitnessedPacket graph))
    (found : forwardingPacket known fact = some message) :
    forwardedEvidence known message.id = some fact := by
  have selected := List.find?_some found
  exact of_decide_eq_true selected

theorem forwardingPacket_exists (known : List (Message Player (WitnessedPacket graph)))
    (id : MessageId Player) (fact : OpeningFact graph)
    (available : forwardedEvidence known id = some fact) :
    ∃ message, forwardingPacket known fact = some message := by
  classical
  cases found : known.find? (fun message => message.id = id) with
  | none => simp [forwardedEvidence, found] at available
  | some message =>
      have selected := List.find?_some found
      have identified : message.id = id := of_decide_eq_true selected
      cases selected : forwardingPacket known fact with
      | some chosen => exact ⟨chosen, rfl⟩
      | none =>
          have excluded := List.find?_eq_none.mp selected message (List.mem_of_find?_eq_some found)
          simp only [identified, available, decide_true] at excluded
          contradiction

theorem resolve_owned_of_no_forward (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (request : EvidenceRequest graph)
    (fact : OpeningFact graph) (resolved : request.resolve who candidates known = some fact)
    (absent : forwardingPacket known fact = Option.none) :
    request = .owned fact ∧ fact.handle.1 = who ∧
      candidates fact.handle.2 = .openable fact.raw := by
  classical
  cases request with
  | none => cases resolved
  | owned selected =>
      simp only [resolve] at resolved
      split at resolved
      · cases Option.some.inj resolved
        exact ⟨rfl, by assumption⟩
      · cases resolved
  | forward id =>
      obtain ⟨message, found⟩ := forwardingPacket_exists known id fact resolved
      rw [absent] at found
      cases found

theorem resolve_normalize (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (request : EvidenceRequest graph) :
    (request.normalize who candidates known).resolve who candidates known =
      request.resolve who candidates known := by
  classical
  change (canonical known (request.resolve who candidates known)).resolve who candidates known = _
  cases resolved : request.resolve who candidates known with
  | none => rfl
  | some fact =>
      cases selected : forwardingPacket known fact with
      | some message =>
          simpa only [canonical, selected, resolve] using
            forwardingPacket_resolves known fact message selected
      | none =>
          have available := (resolve_owned_of_no_forward who candidates known request fact
            resolved selected).2
          simp [canonical, selected, resolve, available]

theorem normalize_idempotent (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (request : EvidenceRequest graph) :
    (request.normalize who candidates known).normalize who candidates known =
      request.normalize who candidates known := by
  change canonical known ((request.normalize who candidates known).resolve who candidates known) = _
  rw [resolve_normalize]
  rfl

theorem normalize_eq_iff_resolve_eq (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (first second : EvidenceRequest graph) :
    first.normalize who candidates known = second.normalize who candidates known ↔
      first.resolve who candidates known = second.resolve who candidates known := by
  constructor
  · intro same
    simpa only [resolve_normalize] using
      congrArg (fun request => request.resolve who candidates known) same
  · exact congrArg (canonical known)

@[simp] theorem normalize_none (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) :
    (EvidenceRequest.none (graph := graph)).normalize who candidates known = .none := rfl

theorem normalize_owned_of_no_forward (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (fact : OpeningFact graph)
    (owned : fact.handle.1 = who) (valid : candidates fact.handle.2 = .openable fact.raw)
    (absent : forwardingPacket known fact = Option.none) :
    (EvidenceRequest.owned fact).normalize who candidates known = .owned fact := by
  simp [normalize, resolve, owned, valid, canonical, absent]

theorem normalize_owned_nil (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L)) (fact : OpeningFact graph) :
    (EvidenceRequest.owned fact).normalize who candidates [] =
      if fact.handle.1 = who ∧ candidates fact.handle.2 = .openable fact.raw
      then .owned fact else .none := by
  classical
  by_cases available : fact.handle.1 = who ∧ candidates fact.handle.2 = .openable fact.raw <;>
    simp [normalize, resolve, available, canonical, forwardingPacket]

theorem normalize_empty_forward (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (id : MessageId Player)
    (empty : forwardedEvidence known id = Option.none) :
    (EvidenceRequest.forward (graph := graph) id).normalize who candidates known = .none := by
  simp only [normalize, resolve, empty, canonical]

theorem normalize_unknown (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (known : List (Message Player (WitnessedPacket graph))) (id : MessageId Player)
    (absent : ¬ ∃ message ∈ known, message.id = id) :
    (EvidenceRequest.forward (graph := graph) id).normalize who candidates known = .none := by
  apply normalize_empty_forward
  have missing : known.find? (fun message => message.id = id) = Option.none := by
    apply List.find?_eq_none.mpr
    intro message member found
    exact absent ⟨message, member, of_decide_eq_true found⟩
  simp only [forwardedEvidence, missing, Option.bind_none]

end Vegas.EventGraphRuntime.EvidenceRequest

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem WitnessedSubmission.emit_eq_resolve (submission : WitnessedSubmission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) :
    submission.emit state who known =
      ⟨submission.call.packet, submission.evidence.resolve who
        (fun slot => state.candidates.lookup (who, slot)) known⟩ := by
  classical
  cases request : submission.evidence with
  | none | forward =>
      simp only [WitnessedSubmission.emit, request, EvidenceRequest.resolve,
        EvidenceRequest.forwardedEvidence]
  | owned fact =>
      by_cases owner : fact.handle.1 = who
      · have handle : fact.handle = (who, fact.handle.2) := by rw [← owner]
        have localMeaning := congrArg state.candidates.lookup handle
        simp [WitnessedSubmission.emit, EvidenceRequest.resolve, request,
          CommitmentCandidates.verify, owner, localMeaning]
      · simp [WitnessedSubmission.emit, EvidenceRequest.resolve, request, owner]

end Vegas.EventGraphRuntime
