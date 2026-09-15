/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.LogicalCommitment
import Interaction.SealedCandidateResolution
import Interaction.SealedProgramLaws

/-! # Local admission for a logical commitment binding

This module factors the inclusion-time validator for one candidate commitment
binding.  The sealed graph supplies only the site's enabled bit; authority,
the selected source handle, and the candidate meaning are checked by the
existing logical commitment kernel.

The result is deliberately local.  It does not project transport, graph
refresh, deadline settlement, observations, or policy laws, and hence is not
a strategic refinement theorem.
-/

namespace Interaction.LogicalCommitment

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- The logical authority carried by a native owner/slot candidate handle. -/
private def admissionProtocol (owner : Principal) :
    LogicalCommitment Principal (CommitmentHandle Principal Nat) where
  owner := owner
  handleOwner := Prod.fst

/-- The semantic part of one pending native candidate binding. -/
private def admissionSnapshot
    (candidates : CommitmentCandidates Principal Nat Value)
    (selected : Option (CommitmentHandle Principal Nat)) :
    State Principal (CommitmentHandle Principal Nat) Value :=
  { State.empty with
    meanings := candidates.lookup
    selected := selected }

/-- The admission bit supplied by the sealed dependency graph. -/
def graphAdmissionEnabled (events : List (SealedProgram.Event Principal Value))
    (node : Nat) (requires : List Nat) : Bool :=
  !SealedProgram.done events node && requires.all (SealedProgram.done events)

/-- Apply the existing logical validator only when the graph site is enabled. -/
def State.applyClaimWhenEnabled? [DecidableEq Principal] [DecidableEq Value]
    (enabled : Bool)
    (protocol : LogicalCommitment Principal (CommitmentHandle Principal Nat))
    (state : State Principal (CommitmentHandle Principal Nat) Value)
    (claim : Claim Principal (CommitmentHandle Principal Nat) Value) :
    Option (State Principal (CommitmentHandle Principal Nat) Value) :=
  if enabled then state.applyClaim? protocol claim else none

@[simp] theorem State.applyClaimWhenEnabled?_false
    [DecidableEq Principal] [DecidableEq Value]
    (protocol : LogicalCommitment Principal (CommitmentHandle Principal Nat))
    (state : State Principal (CommitmentHandle Principal Nat) Value)
    (claim : Claim Principal (CommitmentHandle Principal Nat) Value) :
    state.applyClaimWhenEnabled? false protocol claim = none := rfl

@[simp] theorem graphAdmissionEnabled_eq_true_iff
    (events : List (SealedProgram.Event Principal Value))
    (node : Nat) (requires : List Nat) :
    graphAdmissionEnabled events node requires = true ↔
      SealedProgram.done events node = false ∧
        requires.all (SealedProgram.done events) = true := by
  simp [graphAdmissionEnabled]

/-- For a commitment rule, native acceptance is exactly graph enablement
followed by logical authority and first-selection admission.  Candidate
openability is deliberately not an acceptance premise. -/
theorem candidateMessage?_commit_isSome
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (sender owner : Principal) (serial node : Nat)
    (handle : CommitmentHandle Principal Nat) (requires : List Nat)
    (hrule : program.rules[node]? = some ⟨.commit owner, requires⟩) :
    (program.candidateMessage? candidates events
      ⟨(sender, serial), .commitment node handle⟩).isSome =
      ((admissionSnapshot candidates (SealedProgram.accepted? events node)).applyClaimWhenEnabled?
        (graphAdmissionEnabled events node requires) (admissionProtocol owner)
        (.select sender handle)).isSome := by
  rw [program.candidateMessage?_commit candidates events sender owner serial node handle requires
    hrule]
  cases hdone : SealedProgram.done events node with
  | false =>
      have hselected := SealedProgram.accepted?_none_of_not_done events node hdone
      cases hready : requires.all (SealedProgram.done events) <;>
        by_cases hsender : sender = owner <;>
        by_cases hhandleOwner : handle.1 = owner <;>
        simp [State.applyClaimWhenEnabled?, graphAdmissionEnabled, State.applyClaim?,
          admissionSnapshot, admissionProtocol, State.empty, hdone, hselected, hready,
          hsender, hhandleOwner]
  | true => simp [State.applyClaimWhenEnabled?, graphAdmissionEnabled, hdone]

/-- For a reveal rule, native acceptance is exactly graph enablement followed
by logical authority, selected-handle agreement, and candidate meaning. -/
theorem candidateMessage?_opening_isSome
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (sender owner : Principal) (serial node source : Nat)
    (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (requires : List Nat)
    (hrule : program.rules[node]? = some ⟨.reveal owner source, requires⟩) :
    (program.candidateMessage? candidates events
      ⟨(sender, serial), .opening node handle claimed⟩).isSome =
      ((admissionSnapshot candidates
        (SealedProgram.accepted? events source)).applyClaimWhenEnabled?
        (graphAdmissionEnabled events node requires) (admissionProtocol owner)
        (.open sender handle claimed)).isSome := by
  cases hdone : SealedProgram.done events node <;>
    cases hready : requires.all (SealedProgram.done events) <;>
    by_cases hsender : sender = owner <;>
    by_cases hhandleOwner : handle.1 = owner <;>
    by_cases hselected : SealedProgram.accepted? events source = some handle <;>
    by_cases hmeaning : candidates.lookup handle = .openable claimed <;>
    simp [SealedProgram.candidateMessage?, hrule, State.applyClaimWhenEnabled?,
      SealedProgram.prerequisitesDone, graphAdmissionEnabled, State.applyClaim?,
      admissionSnapshot, admissionProtocol, State.empty, Message.sender,
      CommitmentCandidates.verify_eq_true_iff, hdone, hready, hsender, hhandleOwner,
      hselected, hmeaning]

/-- Incomplete graph prerequisites disable either logical admission path. -/
theorem graphAdmissionEnabled_eq_false_of_incomplete
    (events : List (SealedProgram.Event Principal Value))
    (node : Nat) (requires : List Nat)
    (hincomplete : requires.all (SealedProgram.done events) = false) :
    graphAdmissionEnabled events node requires = false := by
  simp [graphAdmissionEnabled, hincomplete]

/-- A completed site disables later competing claims at that site. -/
theorem graphAdmissionEnabled_eq_false_of_done
    (events : List (SealedProgram.Event Principal Value))
    (node : Nat) (requires : List Nat)
    (hdone : SealedProgram.done events node = true) :
    graphAdmissionEnabled events node requires = false := by
  simp [graphAdmissionEnabled, hdone]

/-- An incomplete prerequisite rejects the actual candidate commitment
validator, independently of authority or candidate preparation. -/
theorem candidateMessage?_commit_none_of_incomplete
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (sender owner : Principal) (serial node : Nat)
    (handle : CommitmentHandle Principal Nat) (requires : List Nat)
    (hrule : program.rules[node]? = some ⟨.commit owner, requires⟩)
    (hincomplete : requires.all (SealedProgram.done events) = false) :
    program.candidateMessage? candidates events
      ⟨(sender, serial), .commitment node handle⟩ = none := by
  rw [program.candidateMessage?_commit candidates events sender owner serial node handle requires
    hrule]
  simp [hincomplete]

/-- Completion by a first accepted candidate rejects a competing commitment
at the actual validator. -/
theorem candidateMessage?_commit_none_of_done
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (sender owner : Principal) (serial node : Nat)
    (handle : CommitmentHandle Principal Nat) (requires : List Nat)
    (hrule : program.rules[node]? = some ⟨.commit owner, requires⟩)
    (hdone : SealedProgram.done events node = true) :
    program.candidateMessage? candidates events
      ⟨(sender, serial), .commitment node handle⟩ = none := by
  rw [program.candidateMessage?_commit candidates events sender owner serial node handle requires
    hrule]
  simp [hdone]

/-- The actual candidate validator accepts an enabled owner-scoped fresh
candidate and freezes its previously unprepared meaning as unopenable. -/
theorem candidateMessage?_commit_fresh
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (owner : Principal) (serial node : Nat)
    (handle : CommitmentHandle Principal Nat) (requires : List Nat)
    (hrule : program.rules[node]? = some ⟨.commit owner, requires⟩)
    (howner : handle.1 = owner)
    (hnotDone : SealedProgram.done events node = false)
    (hrequires : requires.all (SealedProgram.done events) = true)
    (hfresh : candidates.lookup handle = .fresh) :
    program.candidateMessage? candidates events
        ⟨(owner, serial), .commitment node handle⟩ =
          some (candidates.accept handle, .accepted node handle) ∧
      (candidates.accept handle).lookup handle = .unopenable := by
  constructor
  · rw [program.candidateMessage?_commit candidates events owner owner serial node handle
      requires hrule]
    simp [howner, hnotDone, hrequires]
  · simp [CommitmentCandidates.lookup_accept_self, hfresh]

/-- Malformed native payloads and malformed logical claims are rejected for
every supplied gate value. -/
theorem malformed_rejected [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (sender : Principal) (serial : Nat) (enabled : Bool)
    (owner : Principal)
    (state : State Principal (CommitmentHandle Principal Nat) Value) :
    program.candidateMessage? candidates events ⟨(sender, serial), .malformed⟩ = none ∧
      state.applyClaimWhenEnabled? enabled (admissionProtocol owner)
        (.malformed sender) = none := by
  cases enabled <;>
    simp [SealedProgram.candidateMessage?, State.applyClaimWhenEnabled?, State.applyClaim?]

/-- Cleartext claims cannot bypass the native or logical commitment boundary. -/
theorem cleartext_rejected [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (sender : Principal) (serial node : Nat) (value : Value)
    (enabled : Bool) (owner : Principal)
    (state : State Principal (CommitmentHandle Principal Nat) Value) :
    program.candidateMessage? candidates events
        ⟨(sender, serial), .cleartext node value⟩ = none ∧
      state.applyClaimWhenEnabled? enabled (admissionProtocol owner)
        (.malformed sender) = none := by
  cases enabled <;>
    simp [SealedProgram.candidateMessage?, State.applyClaimWhenEnabled?, State.applyClaim?]

/-- info: 'Interaction.LogicalCommitment.candidateMessage?_commit_isSome'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms candidateMessage?_commit_isSome

/-- info: 'Interaction.LogicalCommitment.candidateMessage?_opening_isSome'
depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms candidateMessage?_opening_isSome

/-- info: 'Interaction.LogicalCommitment.candidateMessage?_commit_fresh'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms candidateMessage?_commit_fresh

end Interaction.LogicalCommitment
