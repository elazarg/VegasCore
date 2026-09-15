/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.LogicalCommitmentAdmission

/-! # Semantic effects of candidate admission

This module strengthens the local candidate admission comparison from an
acceptance bit to the resulting semantic binding state.  It projects exactly
the selected handle, every candidate meaning, and the logical opening result.
The comparison still ends at `SealedProgram.candidateMessage?`: transport,
receipts, timeout discharge, post-admission graph refresh, clocks, and player
observations are intentionally outside it.

Thus the laws isolate one operational projection case.  They are not yet a
strategic edge: the surrounding candidate handler must still relate insertion
and refresh, and a probability proof must additionally relate observations and
policy choices along the resulting traces.
-/

namespace Interaction.LogicalCommitment

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- The semantic fields shared by a native candidate site and one logical
commitment binding. -/
structure CandidateSemantics (Principal : Type uPrincipal) (Value : Type uValue) where
  meanings : CommitmentHandle Principal Nat → CommitmentCandidate Value
  selected : Option (CommitmentHandle Principal Nat)
  result : Result Value

/-- Forget occurrence lists while retaining the local semantic fields. -/
def State.candidateSemantics
    (state : State Principal (CommitmentHandle Principal Nat) Value) :
    CandidateSemantics Principal Value :=
  ⟨state.meanings, state.selected, state.result⟩

/-- Read a successful native validator result as one local semantic effect. -/
def CandidateSemantics.ofNativeResult
    (selected : Option (CommitmentHandle Principal Nat))
    (result : CommitmentCandidates Principal Nat Value ×
      SealedProgram.Event Principal Value) : CandidateSemantics Principal Value :=
  match result.2 with
  | .accepted _ handle => ⟨result.1.lookup, some handle, .pending⟩
  | .opened _ value => ⟨result.1.lookup, selected, .opened value⟩

private theorem acceptMeanings_eq
    [DecidableEq Principal]
    (candidates : CommitmentCandidates Principal Nat Value)
    (handle : CommitmentHandle Principal Nat) :
    (match candidates.lookup handle with
      | .fresh => fun queried =>
          if queried = handle then .unopenable else candidates.lookup queried
      | .openable _ | .unopenable => candidates.lookup) =
      (candidates.accept handle).lookup := by
  funext queried
  by_cases heq : queried = handle
  · subst queried
    cases hlookup : candidates.lookup handle <;>
      simp [hlookup, CommitmentCandidates.lookup_accept_self]
  · rw [candidates.lookup_accept_other handle queried heq]
    cases candidates.lookup handle <;> simp [heq]

private theorem select_ofCandidate_semantics
    [DecidableEq Principal] [DecidableEq Value]
    (candidates : CommitmentCandidates Principal Nat Value)
    (handle : CommitmentHandle Principal Nat) :
    ((State.ofCandidate candidates none).applyClaim?
      (candidateProtocol handle.1) (.select handle.1 handle)).map
        State.candidateSemantics =
      some ⟨(candidates.accept handle).lookup, some handle, .pending⟩ := by
  rw [State.applyClaim?_select (protocol := candidateProtocol handle.1)
    (state := State.ofCandidate candidates none) (sender := handle.1)
    (handle := handle) rfl rfl rfl rfl]
  exact congrArg (fun meanings =>
    some (CandidateSemantics.mk meanings (some handle) Result.pending))
    (acceptMeanings_eq candidates handle)

/-- Commitment inclusion has the same projected semantic result in the actual
candidate validator and the graph-gated logical validator.  This includes
disabled or incomplete sites, competing selections, and prepared or fresh
candidates. -/
theorem candidateMessage?_commit_semantics
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (sender owner : Principal) (serial node : Nat)
    (handle : CommitmentHandle Principal Nat) (requires : List Nat)
    (hrule : program.rules[node]? = some ⟨.commit owner, requires⟩) :
    ((State.ofCandidate candidates (SealedProgram.accepted? events node)).applyClaimWhenEnabled?
      (graphAdmissionEnabled events node requires) (candidateProtocol owner)
      (.select sender handle)).map State.candidateSemantics =
    (program.candidateMessage? candidates events
      ⟨(sender, serial), .commitment node handle⟩).map
        (CandidateSemantics.ofNativeResult (SealedProgram.accepted? events node)) := by
  rw [program.candidateMessage?_commit candidates events sender owner serial node handle requires
    hrule]
  cases hdone : SealedProgram.done events node with
  | false =>
      have hselected := SealedProgram.accepted?_none_of_not_done events node hdone
      cases hready : requires.all (SealedProgram.done events) <;>
        by_cases hsender : sender = owner <;>
        by_cases hhandleOwner : handle.1 = owner
      all_goals solve
        | simp [State.applyClaimWhenEnabled?, graphAdmissionEnabled, State.applyClaim?,
            State.ofCandidate, candidateProtocol, State.empty, hdone, hselected, hready,
            hsender, hhandleOwner]
        | simpa [State.applyClaimWhenEnabled?, graphAdmissionEnabled,
            CandidateSemantics.ofNativeResult, hdone, hselected, hready, hsender,
            hhandleOwner] using select_ofCandidate_semantics candidates handle
  | true => simp [State.applyClaimWhenEnabled?, graphAdmissionEnabled, hdone]

/-- Opening inclusion has the same projected semantic result in the actual
candidate validator and the graph-gated logical validator.  It preserves all
candidate meanings and the selected handle while producing the opened result;
malformed, mismatched, competing, and fresh-unopenable openings are rejected. -/
theorem candidateMessage?_opening_semantics
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (sender owner : Principal) (serial node source : Nat)
    (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (requires : List Nat)
    (hrule : program.rules[node]? = some ⟨.reveal owner source, requires⟩) :
    ((State.ofCandidate candidates
      (SealedProgram.accepted? events source)).applyClaimWhenEnabled?
      (graphAdmissionEnabled events node requires) (candidateProtocol owner)
      (.open sender handle claimed)).map State.candidateSemantics =
    (program.candidateMessage? candidates events
      ⟨(sender, serial), .opening node handle claimed⟩).map
        (CandidateSemantics.ofNativeResult (SealedProgram.accepted? events source)) := by
  cases hdone : SealedProgram.done events node <;>
    cases hready : requires.all (SealedProgram.done events) <;>
    by_cases hsender : sender = owner <;>
    by_cases hhandleOwner : handle.1 = owner <;>
    by_cases hselected : SealedProgram.accepted? events source = some handle <;>
    by_cases hmeaning : candidates.lookup handle = .openable claimed <;>
    simp [SealedProgram.candidateMessage?, hrule, State.applyClaimWhenEnabled?,
      SealedProgram.prerequisitesDone, graphAdmissionEnabled, State.applyClaim?,
      State.ofCandidate, candidateProtocol, CandidateSemantics.ofNativeResult,
      State.candidateSemantics, State.empty, Message.sender,
      CommitmentCandidates.verify_eq_true_iff, hdone, hready, hsender, hhandleOwner,
      hselected, hmeaning]

/-- info: 'Interaction.LogicalCommitment.candidateMessage?_commit_semantics'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms candidateMessage?_commit_semantics

/-- info: 'Interaction.LogicalCommitment.candidateMessage?_opening_semantics'
depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms candidateMessage?_opening_semantics

end Interaction.LogicalCommitment
