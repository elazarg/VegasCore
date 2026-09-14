/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateResolution
import Interaction.MessageApplicationPolicyLaws

/-! # Candidate binding in arbitrary policy runs

Acceptance and private preparation are the only operations that can change the
candidate catalog. Once a handle has a nonfresh meaning, both operations leave
that meaning fixed. These local facts lift through the shared message-policy
runner without restricting player or environment policies.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- Any successfully handled candidate message preserves an already fixed
handle, whether or not the message mentions that handle. -/
theorem candidateMessage?_lookup_eq_of_not_fresh
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (result : CommitmentCandidates Principal Nat Value ×
      SealedProgram.Event Principal Value)
    (tracked : CommitmentHandle Principal Nat)
    (hfixed : candidates.lookup tracked ≠ .fresh)
    (hresult : program.candidateMessage? candidates events message = some result) :
    result.1.lookup tracked = candidates.lookup tracked := by
  rcases program.candidateMessage?_effect candidates events message result hresult with
    ⟨node, handle, _hpayload, rfl⟩ | ⟨node, handle, claimed, _hpayload, rfl⟩
  · exact candidates.lookup_accept_eq_of_not_fresh tracked handle hfixed
  · rfl

/-- A public acceptance returned by the candidate validator leaves its selected
handle with a nonfresh, globally fixed meaning. -/
theorem candidateMessage?_accepted_fixed
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (nextCandidates : CommitmentCandidates Principal Nat Value)
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (hresult : program.candidateMessage? candidates events message =
      some (nextCandidates, .accepted node handle)) :
    nextCandidates.lookup handle ≠ .fresh := by
  rcases program.candidateMessage?_effect candidates events message _ hresult with
    ⟨otherNode, otherHandle, _hpayload, heq⟩ |
      ⟨otherNode, otherHandle, claimed, _hpayload, heq⟩
  · cases heq
    exact candidates.lookup_accept_ne_fresh handle
  · cases heq

/-- The resolving handler preserves the exact meaning of every already fixed
candidate handle. -/
theorem candidateHandle_lookup_eq_of_not_fresh
    (runtime : SealedResolution Principal Value)
    (state next : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (tracked : CommitmentHandle Principal Nat)
    (hfixed : state.service.lookup tracked ≠ .fresh)
    (hnext : runtime.candidateHandle state message = some next) :
    next.service.lookup tracked = state.service.lookup tracked := by
  unfold candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge state.visible.timeouts).candidateMessage?
        state.service state.visible.events message with
    | none =>
        have himpossible : (none : Option (CommitmentCandidates Principal Nat Value)) =
            some next.service := by
          simpa [hmessage] using congrArg
            (Option.map (fun application : ApplicationState Principal Value
              (CommitmentCandidates Principal Nat Value) => application.service)) hnext
        contradiction
    | some result =>
        have hservice : result.1 = next.service := Option.some.inj (by
          simpa [hmessage] using congrArg
            (Option.map (fun application : ApplicationState Principal Value
              (CommitmentCandidates Principal Nat Value) => application.service)) hnext)
        rw [← hservice]
        exact candidateMessage?_lookup_eq_of_not_fresh
          (runtime.program.discharge state.visible.timeouts) state.service state.visible.events
            message result tracked hfixed hmessage

/-- Successfully handling a commitment fixes its submitted candidate handle,
without requiring that it was prepared or openable. -/
theorem candidateHandle_commitment_fixed
    (runtime : SealedResolution Principal Value)
    (state next : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (hpayload : message.payload = .commitment node handle)
    (hnext : runtime.candidateHandle state message = some next) :
    next.service.lookup handle ≠ .fresh := by
  unfold candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge state.visible.timeouts).candidateMessage?
        state.service state.visible.events message with
    | none =>
        have himpossible : (none : Option (CommitmentCandidates Principal Nat Value)) =
            some next.service := by
          simpa [hmessage] using congrArg
            (Option.map (fun application : ApplicationState Principal Value
              (CommitmentCandidates Principal Nat Value) => application.service)) hnext
        contradiction
    | some result =>
        have hservice : result.1 = next.service := Option.some.inj (by
          simpa [hmessage] using congrArg
            (Option.map (fun application : ApplicationState Principal Value
              (CommitmentCandidates Principal Nat Value) => application.service)) hnext)
        rw [← hservice]
        rcases (runtime.program.discharge state.visible.timeouts).candidateMessage?_effect
            state.service state.visible.events message result hmessage with
          ⟨otherNode, otherHandle, hcommitment, rfl⟩ |
            ⟨otherNode, otherHandle, claimed, hopening, rfl⟩
        · rw [hpayload] at hcommitment
          cases hcommitment
          exact state.service.lookup_accept_ne_fresh handle
        · rw [hpayload] at hopening
          contradiction

/-- Arbitrary player and environment policies preserve the exact meaning of a
handle that was fixed at the start of the supplied policy-run suffix. -/
theorem runPolicies_candidate_lookup_of_not_fresh
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.candidateApplication.PolicyExecution)
    (handle : CommitmentHandle Principal Nat)
    (hfixed : execution.native.application.service.lookup handle ≠ .fresh)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies
      players environment schedule execution).support) :
    next.native.application.service.lookup handle =
      execution.native.application.service.lookup handle := by
  let original := execution.native.application.service.lookup handle
  let invariant := fun state : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value) => state.service.lookup handle = original
  apply runtime.candidateApplication.runPolicies_application_invariant invariant
    (fun state owner command hinvariant => ?_)
    (fun state message result hinvariant hresult => ?_)
    (fun state command result hinvariant hresult => ?_)
    players environment schedule execution next rfl hnext
  · change (state.service.prepare owner command.down.1 command.down.2).lookup handle = original
    rw [state.service.lookup_prepare_eq_of_not_fresh handle owner command.down.1 command.down.2]
    · exact hinvariant
    · rw [hinvariant]
      exact hfixed
  · change runtime.candidateHandle state message = some result at hresult
    change result.service.lookup handle = original
    rw [runtime.candidateHandle_lookup_eq_of_not_fresh state result message handle]
    · exact hinvariant
    · rw [hinvariant]
      exact hfixed
    · exact hresult
  · simp only [candidateApplication, host, GameTheory.Math.Probability.FinDist.mem_support_pure]
      at hresult
    subst result
    exact hinvariant

/-- Consequently every claimed-value verification result is fixed throughout
the same arbitrary policy-run suffix. -/
theorem runPolicies_candidate_verify
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.candidateApplication.PolicyExecution)
    (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (hfixed : execution.native.application.service.lookup handle ≠ .fresh)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies
      players environment schedule execution).support) :
    next.native.application.service.verify handle claimed =
      execution.native.application.service.verify handle claimed := by
  unfold CommitmentCandidates.verify
  rw [runtime.runPolicies_candidate_lookup_of_not_fresh players environment schedule
    execution next handle hfixed hnext]

end Interaction.SealedResolution

/- Guard the arbitrary-policy persistence theorem against accidental new axioms. -/
/-- info: 'Interaction.SealedResolution.runPolicies_candidate_lookup_of_not_fresh'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_candidate_lookup_of_not_fresh
