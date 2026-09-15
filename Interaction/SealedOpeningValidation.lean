/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateBinding
import Interaction.SealedCandidateKnowledge
import Interaction.SealedResolutionTermination

/-! # Public validation of authenticated candidate openings

This module adds one public check after candidate authentication.  The check
receives only the reveal node, the pre-inclusion public event log, and the
claimed value.  Commitment admission is unchanged, and malformed or
unauthenticated openings never reach the check because `candidateHandle`
rejects them first.

Including a rejected opening records a negative receipt without adding its
application event. The existing clock still completes the site with the runtime
null value after its deadline. A compiler using this hook must separately prove
that its null value is a safe default and that the public context used by a guard remains
appropriate until inclusion.  This layer proves termination through timeout,
not timely inclusion or a strategic refinement.
-/

noncomputable section

namespace Interaction.SealedResolution

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- A public predicate checked for an authenticated candidate opening.  It has
no access to the private candidate catalog or to the submitted handle. -/
abbrev PublicOpeningValidator (Principal : Type uPrincipal) (Value : Type uValue) :=
  Nat → List (SealedProgram.Event Principal Value) → Value → Bool

/-- Non-opening payloads require no additional permission.  For an opening,
the validator sees the claimed value and the public log before inclusion. -/
def openingPermitted
    (validator : PublicOpeningValidator Principal Value)
    (events : List (SealedProgram.Event Principal Value)) :
    SealedProgram.Payload Principal Value → Bool
  | .opening node _ claimed => validator node events claimed
  | .commitment _ _ | .cleartext _ _ | .malformed => true

/-- Apply the public opening predicate only after the ordinary candidate
handler has authenticated and admitted the payload.  A rejected predicate
does not append an event or mutate the candidate catalog. -/
def guardedCandidateHandle [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (state : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value)) :
    Option (ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value)) := do
  let next ← runtime.candidateHandle state message
  if openingPermitted validator state.visible.events message.payload then
    some next
  else
    none

/-- Public validation preserves candidate hiding: paired runs present exactly
the same pre-inclusion events, node and claimed value to the predicate. -/
theorem guardedCandidateHandle_knowledge [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value) :
    CandidateHandlerKnowledge (runtime.guardedCandidateHandle validator) := by
  intro known left right hvalues hpublic message hknown
  have hbase := runtime.candidateHandle_knowledge known left right
    hvalues hpublic message hknown
  cases hpermitted : openingPermitted validator right.visible.events message.payload with
  | false => simp [guardedCandidateHandle, hpublic, hpermitted]
  | true => simpa [guardedCandidateHandle, hpublic, hpermitted] using hbase

/-- Every successful guarded application was first accepted by the original
candidate handler and passed the public opening check. -/
theorem guardedCandidateHandle_success [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (state next : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.guardedCandidateHandle validator state message = some next) :
    runtime.candidateHandle state message = some next ∧
      openingPermitted validator state.visible.events message.payload = true := by
  unfold guardedCandidateHandle at hnext
  cases hcandidate : runtime.candidateHandle state message with
  | none => simp [hcandidate] at hnext
  | some candidateNext =>
      simp only [hcandidate, Option.bind_eq_bind, Option.bind_some] at hnext
      split at hnext
      · rename_i hpermitted
        cases hnext
        exact ⟨rfl, hpermitted⟩
      · contradiction

/-- A successful guarded opening exposes the exact public check that passed. -/
theorem guardedCandidateHandle_opening_valid
    [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (state next : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (hpayload : message.payload = .opening node handle claimed)
    (hnext : runtime.guardedCandidateHandle validator state message = some next) :
    validator node state.visible.events claimed = true := by
  have hpermitted :=
    (runtime.guardedCandidateHandle_success validator state next message hnext).2
  simpa [openingPermitted, hpayload] using hpermitted

/-- On an opening payload, guarded admission is exactly original authenticated
admission followed by the public predicate. -/
theorem guardedCandidateHandle_opening_eq [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (state : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (hpayload : message.payload = .opening node handle claimed) :
    runtime.guardedCandidateHandle validator state message =
      if validator node state.visible.events claimed then
        runtime.candidateHandle state message
      else none := by
  cases hcandidate : runtime.candidateHandle state message <;>
    cases hvalidator : validator node state.visible.events claimed <;>
    simp [guardedCandidateHandle, openingPermitted, hpayload, hcandidate, hvalidator]

/-- An opening already accepted by `candidateHandle` is retained when its
public predicate succeeds. -/
theorem guardedCandidateHandle_opening [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (state next : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (hpayload : message.payload = .opening node handle claimed)
    (hcandidate : runtime.candidateHandle state message = some next)
    (hvalidator : validator node state.visible.events claimed = true) :
    runtime.guardedCandidateHandle validator state message = some next := by
  rw [runtime.guardedCandidateHandle_opening_eq validator state message node handle claimed
    hpayload, hvalidator, if_pos rfl, hcandidate]

/-- Commitment admission is exactly unchanged by opening validation,
including rejection by the original candidate authentication checks. -/
theorem guardedCandidateHandle_commitment [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (state : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (hpayload : message.payload = .commitment node handle) :
    runtime.guardedCandidateHandle validator state message =
      runtime.candidateHandle state message := by
  cases hcandidate : runtime.candidateHandle state message <;>
    simp [guardedCandidateHandle, openingPermitted, hpayload, hcandidate]

/-- Successful guarded handling has the same event-and-refresh shape as the
original candidate handler. -/
theorem guardedCandidateHandle_records [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value) :
    runtime.HandlerRecords (runtime.guardedCandidateHandle validator) := by
  intro state message next hnext
  exact runtime.candidateHandle_records state message next
    (runtime.guardedCandidateHandle_success validator state next message hnext).1

/-- The existing candidate service hosted with public opening validation.
Transport, observations, preparation, clock advancement, and timeout behavior
are exactly those of `SealedResolution.host`. -/
noncomputable def guardedCandidateApplication [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value) : MessageApplication Principal :=
  runtime.host (Service := CommitmentCandidates Principal Nat Value)
    (fun state owner slot value => state.prepare owner slot value)
    (runtime.guardedCandidateHandle validator)

/-- Every enabled backward-dependency program hosted with guarded candidate
openings completes within the ordinary resolution bound under arbitrary player
and wire policies.  Rejected openings may complete by timeout. -/
theorem guardedCandidate_runRounds_complete [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (henabled : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule → rule.kind ≠ .disabled)
    (hbackward : ∀ (node : Nat) (rule : SealedRule Principal),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.guardedCandidateApplication validator).PlayerPolicy)
    (environment : (runtime.guardedCandidateApplication validator).WirePolicy)
    (total : Nat) (hbound : runtime.program.rules.length * (runtime.window + 1) ≤ total)
    (execution next : (runtime.guardedCandidateApplication validator).PolicyExecution)
    (hbounded : execution.native.application.visible.ClockBounded)
    (hnext : next ∈ ((runtime.hostRoundDriver
      (fun state owner slot value => state.prepare owner slot value)
      (runtime.guardedCandidateHandle validator)).runRounds
        principals serviceSlots players environment total execution).support) :
    runtime.complete next.native.application.visible = true := by
  exact runtime.runRounds_complete (runtime.guardedCandidateHandle_records validator)
    henabled hbackward principals serviceSlots players environment total hbound
    execution next hbounded hnext

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.guardedCandidate_runRounds_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.guardedCandidate_runRounds_complete

/-- info: 'Interaction.SealedResolution.guardedCandidateHandle_knowledge'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.guardedCandidateHandle_knowledge
