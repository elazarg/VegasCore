/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommitmentCandidates

/-! # A one-binding logical commitment protocol

This module isolates the semantic state of one commitment binding from a
concrete message queue and clock.  It retains a quotient of relevant
observations: locally sent and exposed logical claims, the public logical-claim
ledger, and public acceptance receipts.  Exposure and inclusion are different
events.  In particular, seeing an opening claim does not open the binding.
The quotient is not asserted to preserve every native payload distinction.

The transition system does not assert that an arbitrary logical trace is the
image of a transport trace.  `Action.RealizableAt` is a small provenance check
which rules out spontaneous claims, but it deliberately does not reconstruct
pending-copy counts, identifiers, or delivery service.  A concrete refinement
must prove both this unary condition and its own relative-information law.

`settleQuit` is an attributed settlement event, not an assertion that the owner
was scheduled at that point or chose to quit after seeing the final view.
Turning it into an informed strategic deviation requires a separate utility
comparison.
-/

namespace Interaction

universe uPrincipal uHandle uValue

/-- Static authority for one logical binding.  Several handles may compete for
the binding, but they must belong to its owner. -/
structure LogicalCommitment (Principal : Type uPrincipal) (Handle : Type uHandle) where
  owner : Principal
  handleOwner : Handle → Principal

namespace LogicalCommitment

/-- Claims are semantic payloads, not packets.  Repeated occurrences remain
observable in the lists below. -/
inductive Claim (Principal : Type uPrincipal) (Handle : Type uHandle)
    (Value : Type uValue) where
  | select (sender : Principal) (handle : Handle)
  | open (sender : Principal) (handle : Handle) (value : Value)
  | malformed (sender : Principal)
  deriving DecidableEq

namespace Claim

variable {Principal : Type uPrincipal} {Handle : Type uHandle} {Value : Type uValue}

def sender : Claim Principal Handle Value → Principal
  | .select who _ | .open who _ _ | .malformed who => who

@[simp] theorem sender_select (who : Principal) (handle : Handle) :
    (Claim.select who handle : Claim Principal Handle Value).sender = who := rfl

@[simp] theorem sender_open (who : Principal) (handle : Handle) (value : Value) :
    (Claim.open who handle value : Claim Principal Handle Value).sender = who := rfl

@[simp] theorem sender_malformed (who : Principal) :
    (Claim.malformed who : Claim Principal Handle Value).sender = who := rfl

end Claim

/-- Public semantic resolution.  `quit` records attributed fallback settlement
and contains no invented opening value. -/
inductive Result (Value : Type uValue) where
  | pending
  | opened (value : Value)
  | quit
  deriving DecidableEq

/-- State of one binding.  Candidate meanings are proof-facing and private;
all other fields occur in player observations, with `sent` and `inbox` scoped
to the observing principal. -/
structure State (Principal : Type uPrincipal) (Handle : Type uHandle)
    (Value : Type uValue) where
  meanings : Handle → CommitmentCandidate Value
  selected : Option Handle
  sent : Principal → List (Claim Principal Handle Value)
  inbox : Principal → List (Claim Principal Handle Value)
  ledger : List (Claim Principal Handle Value)
  receipts : List (Claim Principal Handle Value × Bool)
  result : Result Value

namespace State

variable {Principal : Type uPrincipal} {Handle : Type uHandle} {Value : Type uValue}

def empty : State Principal Handle Value where
  meanings := fun _ => .fresh
  selected := none
  sent := fun _ => []
  inbox := fun _ => []
  ledger := []
  receipts := []
  result := .pending

/-- Player-visible state at this quotient: sent and delivered logical claims
are local, whereas the logical-claim ledger and acceptance receipts are
shared.  A refinement must justify every payload distinction it forgets. -/
structure View (Principal : Type uPrincipal) (Handle : Type uHandle)
    (Value : Type uValue) where
  sent : List (Claim Principal Handle Value)
  inbox : List (Claim Principal Handle Value)
  ledger : List (Claim Principal Handle Value)
  receipts : List (Claim Principal Handle Value × Bool)
  selected : Option Handle
  result : Result Value

def observe (state : State Principal Handle Value) (who : Principal) :
    View Principal Handle Value :=
  ⟨state.sent who, state.inbox who, state.ledger, state.receipts,
    state.selected, state.result⟩

/-- Private authenticated preparation.  A fixed handle is immutable. -/
def prepare [DecidableEq Principal] [DecidableEq Handle]
    (protocol : LogicalCommitment Principal Handle) (state : State Principal Handle Value)
    (who : Principal) (handle : Handle) (value : Value) : State Principal Handle Value :=
  if who = protocol.owner ∧ protocol.handleOwner handle = who then
    match state.meanings handle with
    | .fresh => { state with meanings := fun queried =>
        if queried = handle then .openable value else state.meanings queried }
    | .openable _ | .unopenable => state
  else state

/-- Record a locally authored or relayed claim.  `Action.RealizableAt` states
the capability condition used by well-supported traces. -/
def submit [DecidableEq Principal] (state : State Principal Handle Value) (who : Principal)
    (claim : Claim Principal Handle Value) : State Principal Handle Value :=
  { state with sent := fun observer =>
      if observer = who then state.sent who ++ [claim] else state.sent observer }

/-- Record recipient-local visibility without publishing the claim. -/
def expose [DecidableEq Principal] (state : State Principal Handle Value) (recipient : Principal)
    (claim : Claim Principal Handle Value) : State Principal Handle Value :=
  { state with inbox := fun observer =>
      if observer = recipient then state.inbox recipient ++ [claim]
      else state.inbox observer }

private def acceptMeaning [DecidableEq Handle]
    (state : State Principal Handle Value) (handle : Handle) : Handle → CommitmentCandidate Value :=
  match state.meanings handle with
  | .fresh => fun queried => if queried = handle then .unopenable else state.meanings queried
  | .openable _ | .unopenable => state.meanings

/-- Apply an already included claim to the semantic binding.  This operation
does not decide whether a packet was available for inclusion. -/
def applyClaim? [DecidableEq Principal] [DecidableEq Handle] [DecidableEq Value]
    (protocol : LogicalCommitment Principal Handle) (state : State Principal Handle Value) :
    Claim Principal Handle Value → Option (State Principal Handle Value)
  | .select sender handle =>
      if state.result = .pending ∧ state.selected = none ∧
          sender = protocol.owner ∧ protocol.handleOwner handle = protocol.owner then
        some { state with
          meanings := acceptMeaning state handle
          selected := some handle }
      else none
  | .open sender handle value =>
      if state.result = .pending ∧ state.selected = some handle ∧
          sender = protocol.owner ∧ protocol.handleOwner handle = protocol.owner ∧
          state.meanings handle = .openable value then
        some { state with result := .opened value }
      else none
  | .malformed _ => none

/-- Ledger inclusion is public even when semantic admission rejects.  The
receipt records that distinction. -/
def recordInclusion [DecidableEq Principal] [DecidableEq Handle] [DecidableEq Value]
    (protocol : LogicalCommitment Principal Handle) (state : State Principal Handle Value)
    (claim : Claim Principal Handle Value) : State Principal Handle Value :=
  match applyClaim? protocol state claim with
  | some applied => { applied with
      ledger := state.ledger ++ [claim]
      receipts := state.receipts ++ [(claim, true)] }
  | none => { state with
      ledger := state.ledger ++ [claim]
      receipts := state.receipts ++ [(claim, false)] }

/-- Install the attributed fallback while the binding is unresolved.  The
concrete cause (deadline, explicit decline, or another authorized mechanism)
is intentionally outside this logical machine. -/
def settleQuit [DecidableEq Principal] [DecidableEq Value]
    (protocol : LogicalCommitment Principal Handle) (state : State Principal Handle Value)
    (who : Principal) : State Principal Handle Value :=
  if who = protocol.owner ∧ state.result = .pending then
    { state with result := .quit }
  else state

end State

/-- Trace facts at the semantic boundary.  Transport realizes `submit`,
`expose`, and `include`; it is not implemented by this datatype. -/
inductive Action (Principal : Type uPrincipal) (Handle : Type uHandle)
    (Value : Type uValue) where
  | prepare (who : Principal) (handle : Handle) (value : Value)
  | submit (who : Principal) (claim : Claim Principal Handle Value)
  | expose (recipient : Principal) (claim : Claim Principal Handle Value)
  | include (claim : Claim Principal Handle Value)
  | settleQuit (who : Principal)

namespace Action

variable {Principal : Type uPrincipal} {Handle : Type uHandle} {Value : Type uValue}

/-- A necessary, intentionally incomplete provenance condition.  Submission
is either fresh authorship or a relay of something already known to the
broadcaster.  Exposure and inclusion must refer to a previously recorded
submission.  Pending-copy availability is a stronger runtime obligation. -/
def RealizableAt (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) : Action Principal Handle Value → Prop
  | .prepare who handle _ => who = protocol.owner ∧ protocol.handleOwner handle = who
  | .submit who claim => claim.sender = who ∨
      claim ∈ state.sent who ∨ claim ∈ state.inbox who ∨ claim ∈ state.ledger
  | .expose _ claim | .include claim => ∃ who, claim ∈ state.sent who
  | .settleQuit who => who = protocol.owner

end Action

variable {Principal : Type uPrincipal} {Handle : Type uHandle} {Value : Type uValue}

def step [DecidableEq Principal] [DecidableEq Handle] [DecidableEq Value]
    (protocol : LogicalCommitment Principal Handle) (state : State Principal Handle Value) :
    Action Principal Handle Value → State Principal Handle Value
  | .prepare who handle value => state.prepare protocol who handle value
  | .submit who claim => state.submit who claim
  | .expose recipient claim => state.expose recipient claim
  | .include claim => state.recordInclusion protocol claim
  | .settleQuit who => state.settleQuit protocol who

def run [DecidableEq Principal] [DecidableEq Handle] [DecidableEq Value]
    (protocol : LogicalCommitment Principal Handle) (state : State Principal Handle Value)
    (actions : List (Action Principal Handle Value)) : State Principal Handle Value :=
  actions.foldl protocol.step state

private theorem applyClaim?_transport
    [DecidableEq Principal] [DecidableEq Handle] [DecidableEq Value]
    (protocol : LogicalCommitment Principal Handle)
    (state next : State Principal Handle Value) (claim : Claim Principal Handle Value)
    (hnext : State.applyClaim? protocol state claim = some next) :
    next.sent = state.sent ∧ next.inbox = state.inbox := by
  cases claim with
  | select sender handle =>
      simp only [State.applyClaim?] at hnext
      split at hnext <;> try contradiction
      cases hnext
      exact ⟨rfl, rfl⟩
  | «open» sender handle value =>
      simp only [State.applyClaim?] at hnext
      split at hnext <;> try contradiction
      cases hnext
      exact ⟨rfl, rfl⟩
  | malformed sender => simp [State.applyClaim?] at hnext

@[simp] theorem expose_ledger [DecidableEq Principal]
    (state : State Principal Handle Value) (recipient : Principal)
    (claim : Claim Principal Handle Value) :
    (state.expose recipient claim).ledger = state.ledger := rfl

@[simp] theorem expose_result [DecidableEq Principal]
    (state : State Principal Handle Value) (recipient : Principal)
    (claim : Claim Principal Handle Value) :
    (state.expose recipient claim).result = state.result := rfl

@[simp] theorem include_inbox [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (claim : Claim Principal Handle Value)
    (who : Principal) :
    (state.recordInclusion protocol claim).inbox who = state.inbox who := by
  cases hnext : State.applyClaim? protocol state claim with
  | none => simp [State.recordInclusion, hnext]
  | some next =>
      simp only [State.recordInclusion, hnext]
      exact congrFun (applyClaim?_transport protocol state next claim hnext).2 who

@[simp] theorem include_sent [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (claim : Claim Principal Handle Value)
    (who : Principal) :
    (state.recordInclusion protocol claim).sent who = state.sent who := by
  cases hnext : State.applyClaim? protocol state claim with
  | none => simp [State.recordInclusion, hnext]
  | some next =>
      simp only [State.recordInclusion, hnext]
      exact congrFun (applyClaim?_transport protocol state next claim hnext).1 who

@[simp] theorem include_ledger [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (claim : Claim Principal Handle Value) :
    (state.recordInclusion protocol claim).ledger = state.ledger ++ [claim] := by
  cases hnext : State.applyClaim? protocol state claim <;>
    simp [State.recordInclusion, hnext]

@[simp] theorem include_receipts [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (claim : Claim Principal Handle Value) :
    ∃ accepted, (state.recordInclusion protocol claim).receipts =
      state.receipts ++ [(claim, accepted)] := by
  cases hnext : State.applyClaim? protocol state claim with
  | none => exact ⟨false, by simp [State.recordInclusion, hnext]⟩
  | some next => exact ⟨true, by simp [State.recordInclusion, hnext]⟩

@[simp] theorem include_malformed_result [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (sender : Principal) :
    (state.recordInclusion protocol (.malformed sender)).result = state.result := by
  rfl

theorem include_select_fresh [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (handle : Handle)
    (hpending : state.result = .pending) (hunselected : state.selected = none)
    (howner : protocol.handleOwner handle = protocol.owner)
    (hfresh : state.meanings handle = .fresh) :
    let next := state.recordInclusion protocol (.select protocol.owner handle)
    next.selected = some handle ∧ next.meanings handle = .unopenable ∧
      next.receipts = state.receipts ++ [(.select protocol.owner handle, true)] := by
  simp [State.recordInclusion, State.applyClaim?, hpending, hunselected, howner,
    State.acceptMeaning, hfresh]

theorem include_select_openable [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (handle : Handle) (value : Value)
    (hpending : state.result = .pending) (hunselected : state.selected = none)
    (howner : protocol.handleOwner handle = protocol.owner)
    (hvalue : state.meanings handle = .openable value) :
    let next := state.recordInclusion protocol (.select protocol.owner handle)
    next.selected = some handle ∧ next.meanings handle = .openable value := by
  simp [State.recordInclusion, State.applyClaim?, hpending, hunselected, howner,
    State.acceptMeaning, hvalue]

theorem include_open_selected [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (handle : Handle) (value : Value)
    (hpending : state.result = .pending) (hselected : state.selected = some handle)
    (howner : protocol.handleOwner handle = protocol.owner)
    (hvalue : state.meanings handle = .openable value) :
    (state.recordInclusion protocol (.open protocol.owner handle value)).result = .opened value := by
  simp [State.recordInclusion, State.applyClaim?, hpending, hselected, howner, hvalue]

theorem include_selected_stable [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (claim : Claim Principal Handle Value)
    (handle : Handle) (hselected : state.selected = some handle) :
    (state.recordInclusion protocol claim).selected = some handle := by
  cases hnext : State.applyClaim? protocol state claim with
  | none => simpa [State.recordInclusion, hnext] using hselected
  | some next =>
      simp only [State.recordInclusion, hnext]
      cases claim with
      | select sender candidate =>
          have hnone : State.applyClaim? protocol state (.select sender candidate) = none := by
            simp [State.applyClaim?, hselected]
          rw [hnone] at hnext
          contradiction
      | «open» sender candidate value =>
          simp only [State.applyClaim?] at hnext
          split at hnext <;> try contradiction
          cases hnext
          exact hselected
      | malformed sender => simp [State.applyClaim?] at hnext

theorem include_result_of_resolved [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (claim : Claim Principal Handle Value)
    (hresolved : state.result ≠ .pending) :
    (state.recordInclusion protocol claim).result = state.result := by
  cases claim <;> simp [State.recordInclusion, State.applyClaim?, hresolved]

theorem settleQuit_after_malformed [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (sender : Principal)
    (hpending : state.result = .pending) :
    ((state.recordInclusion protocol (.malformed sender)).settleQuit
      protocol protocol.owner).result = .quit := by
  simp [State.recordInclusion, State.applyClaim?, State.settleQuit, hpending]

@[simp] theorem run_nil [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) : protocol.run state [] = state := rfl

@[simp] theorem run_cons [DecidableEq Principal] [DecidableEq Handle]
    [DecidableEq Value] (protocol : LogicalCommitment Principal Handle)
    (state : State Principal Handle Value) (action : Action Principal Handle Value)
    (rest : List (Action Principal Handle Value)) :
    protocol.run state (action :: rest) = protocol.run (protocol.step state action) rest := rfl
end LogicalCommitment

end Interaction
