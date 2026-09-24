/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPlayerAction

/-! # Transferable evidence attached to native calls

An ideal opening certificate states the immutable value of one candidate.
Its public representation is separate from the application call and its
authorization. Certificates are issued from an owner's candidate catalogue or
copied from a packet the sender already possesses. Requests with no available
certificate still transmit their call as an unauthenticated claim.

Issuance runs after private registration in the same atomic response. Thus a
player can create a candidate and disclose its opening in one submission.
The public certificate is fixed in the emitted packet: subsequent inclusion,
application rejection, forwarding, and candidate selection cannot change it.
This is an ideal evidence capability, not a concrete cryptographic encoding.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Evidence concerns a candidate, which need not have won any game binding. -/
structure OpeningFact (graph : Vegas.EventGraph Player L) where
  handle : Handle graph
  raw : Raw L
  deriving DecidableEq

def OpeningFact.Holds (fact : OpeningFact graph) (state : State graph) : Prop :=
  state.candidates.lookup fact.handle = .openable fact.raw

inductive EvidenceRequest (graph : Vegas.EventGraph Player L) where
  | none
  | owned (fact : OpeningFact graph)
  | forward (id : MessageId Player)
  deriving DecidableEq

/-- The public packet contains a call and optional independently checkable evidence. -/
structure WitnessedPacket (graph : Vegas.EventGraph Player L) where
  call : Payload graph
  evidence : Option (OpeningFact graph)

/-- Evidence is requested, never supplied as a freely forgeable authentic token. -/
structure WitnessedSubmission (graph : Vegas.EventGraph Player L) where
  call : Submission graph
  evidence : EvidenceRequest graph

variable [DecidableEq Player]

/-- Materialize an ideal certificate using only owned or received evidence.
The supplied state is the state after this submission's private registration. -/
def WitnessedSubmission.emit (submission : WitnessedSubmission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) : WitnessedPacket graph :=
  ⟨submission.call.packet, match submission.evidence with
    | .none => none
    | .owned fact =>
        if fact.handle.1 = who ∧ state.candidates.verify fact.handle fact.raw then
          some fact else none
    | .forward id =>
        (known.find? fun message => message.id = id).bind fun message =>
          message.payload.evidence⟩

@[simp] theorem WitnessedSubmission.emit_call (submission : WitnessedSubmission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) :
    (submission.emit state who known).call = submission.call.packet := rfl

@[simp] theorem WitnessedSubmission.emit_none (call : Submission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) :
    (WitnessedSubmission.mk call .none |>.emit state who known).evidence = none := rfl

theorem WitnessedSubmission.emit_owned (call : Submission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (fact : OpeningFact graph)
    (owner : fact.handle.1 = who) (valid : fact.Holds state) :
    (WitnessedSubmission.mk call (.owned fact) |>.emit state who known).evidence =
      some fact := by
  have verified : state.candidates.verify fact.handle fact.raw = true :=
    (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr valid
  simp [emit, owner, verified]

/-- A foreign candidate cannot be tested by requesting its certificate. -/
theorem WitnessedSubmission.emit_foreign (call : Submission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (fact : OpeningFact graph)
    (foreign : fact.handle.1 ≠ who) :
    (WitnessedSubmission.mk call (.owned fact) |>.emit state who known).evidence = none := by
  simp [emit, foreign]

theorem WitnessedSubmission.emit_forward (call : Submission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (id : MessageId Player)
    (message : Message Player (WitnessedPacket graph))
    (found : known.find? (fun message => message.id = id) = some message) :
    (WitnessedSubmission.mk call (.forward id) |>.emit state who known).evidence =
      message.payload.evidence := by
  simp [emit, found]

/-- Invalid or guessed references create no certificate. -/
theorem WitnessedSubmission.emit_unknown (call : Submission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (id : MessageId Player)
    (absent : known.find? (fun message => message.id = id) = none) :
    (WitnessedSubmission.mk call (.forward id) |>.emit state who known).evidence = none := by
  simp [emit, absent]

/-- Every emitted certificate was available by ownership or earlier observation. -/
theorem WitnessedSubmission.emit_origin (submission : WitnessedSubmission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (fact : OpeningFact graph)
    (certified : (submission.emit state who known).evidence = some fact) :
    (fact.handle.1 = who ∧ fact.Holds state) ∨
      ∃ message ∈ known, message.payload.evidence = some fact := by
  cases request : submission.evidence with
  | none => simp [emit, request] at certified
  | owned selected =>
      simp only [emit, request] at certified
      split at certified
      · rename_i available
        cases Option.some.inj certified
        exact Or.inl ⟨available.1,
          (CommitmentCandidates.verify_eq_true_iff _ _ _).mp available.2⟩
      · cases certified
  | forward id =>
      cases found : known.find? (fun message => message.id = id) with
      | none => simp [emit, request, found] at certified
      | some message =>
          exact Or.inr ⟨message, List.mem_of_find?_eq_some found, by
            simpa [emit, request, found] using certified⟩

theorem WitnessedSubmission.emit_sound (submission : WitnessedSubmission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (received : ∀ message ∈ known, ∀ fact,
      message.payload.evidence = some fact → fact.Holds state)
    (fact : OpeningFact graph)
    (certified : (submission.emit state who known).evidence = some fact) :
    fact.Holds state := by
  rcases submission.emit_origin state who known fact certified with own | forwarded
  · exact own.2
  · obtain ⟨message, member, evidence⟩ := forwarded
    exact received message member fact evidence

/-- Emission depends on the sender's own candidate meanings and possessed
packets. It cannot query another player's private catalogue or game state. -/
theorem WitnessedSubmission.emit_local (submission : WitnessedSubmission graph)
    (first second : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (same : ∀ slot, first.candidates.lookup (who, slot) =
      second.candidates.lookup (who, slot)) :
    submission.emit first who known = submission.emit second who known := by
  cases request : submission.evidence with
  | none | forward => simp only [emit, request]
  | owned fact =>
      by_cases owner : fact.handle.1 = who
      · have lookup : first.candidates.lookup fact.handle =
            second.candidates.lookup fact.handle := by
          simpa only [← owner] using same fact.handle.2
        simp only [emit, request, CommitmentCandidates.verify, lookup]
      · simp [emit, request, owner]

end Vegas.EventGraphRuntime
