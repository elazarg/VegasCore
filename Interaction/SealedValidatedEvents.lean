/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateEvents
import Interaction.SealedOpeningValidation

/-! # Public event provenance under guarded opening validation

The guarded candidate handler is a restriction of ordinary candidate
admission.  Consequently the existing public-event invariant lifts through
the shared policy runner and round driver without a new execution argument.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- Arbitrary guarded-candidate player and environment policies preserve
public event provenance. -/
theorem runPolicies_guarded_publicEvents
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (players : Principal → (runtime.guardedCandidateApplication validator).PlayerPolicy)
    (environment : (runtime.guardedCandidateApplication validator).EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : (runtime.guardedCandidateApplication validator).PolicyExecution)
    (hinitial : PublicEventInvariant runtime execution.native.application.visible)
    (hnext : next ∈ ((runtime.guardedCandidateApplication validator).runPolicies
      players environment schedule execution).support) :
    PublicEventInvariant runtime next.native.application.visible := by
  apply (runtime.guardedCandidateApplication validator).runPolicies_application_invariant
    (fun state => PublicEventInvariant runtime state.visible) ?_ ?_ ?_
    players environment schedule execution next hinitial hnext
  · intro state owner command hstate
    exact hstate
  · intro state message result hstate hresult
    exact hstate.candidateHandle message
      (runtime.guardedCandidateHandle_success validator state result message hresult).1
  · intro state command result hstate hresult
    simp only [guardedCandidateApplication, SealedResolution.host,
      FinDist.mem_support_pure] at hresult
    subst result
    exact hstate.clock.refresh true

/-- Public event provenance also survives arbitrary guarded-candidate round
execution, including wire traffic and mandatory timeout boundaries. -/
theorem runRounds_guarded_publicEvents
    (runtime : SealedResolution Principal Value)
    (validator : PublicOpeningValidator Principal Value)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → (runtime.guardedCandidateApplication validator).PlayerPolicy)
    (environment : (runtime.guardedCandidateApplication validator).WirePolicy)
    (count : Nat)
    (execution next : (runtime.guardedCandidateApplication validator).PolicyExecution)
    (hinitial : PublicEventInvariant runtime execution.native.application.visible)
    (hnext : next ∈ ((runtime.hostRoundDriver
      (fun state owner slot value => state.prepare owner slot value)
      (runtime.guardedCandidateHandle validator)).runRounds principals serviceSlots
        players environment count execution).support) :
    PublicEventInvariant runtime next.native.application.visible := by
  apply (runtime.hostRoundDriver
    (fun state owner slot value => state.prepare owner slot value)
    (runtime.guardedCandidateHandle validator)).runRounds_application_invariant
      (fun state => PublicEventInvariant runtime state.visible) ?_ ?_ ?_
      principals serviceSlots players environment count execution next hinitial hnext
  · intro state owner command hstate
    exact hstate
  · intro state message result hstate hresult
    exact hstate.candidateHandle message
      (runtime.guardedCandidateHandle_success validator state result message hresult).1
  · intro state command result hstate hresult
    simp only [SealedResolution.host, FinDist.mem_support_pure] at hresult
    subst result
    exact hstate.clock.refresh true

end Interaction.SealedResolution
