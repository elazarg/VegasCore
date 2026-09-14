/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateEvents
import Interaction.SealedCandidateOpening
import Interaction.SealedResolutionSettlement

/-! # Source-site timeout settlement with arbitrary commitment candidates

Opening admission authenticates the selected source-site handle. Together with
the shared public clock laws, this establishes that an opening at a timed-out
site has exactly the designated default. No openable-candidate premise is used.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]


/-- Candidate admission supplies the shared public settlement contract. A
rejected malformed or failed opening has no effect; expiration remains the
operation that installs the programmed default. -/
theorem SettlementInvariant.candidateHandle
    {runtime : SealedResolution Principal Value}
    {state next : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)}
    (invariant : SettlementInvariant runtime state.visible)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.candidateHandle state message = some next) :
    SettlementInvariant runtime next.visible := by
  unfold SealedResolution.candidateHandle at hnext
  split at hnext
  · contradiction
  next hgate =>
    cases hmessage : (runtime.program.discharge state.visible.timeouts).candidateMessage?
        state.service state.visible.events message with
    | none => simp [hmessage] at hnext
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
        subst next
        apply SettlementInvariant.refresh (resolveExpired := false)
        apply invariant.record result.2
        · have hpayload : message.payload.node? = some result.2.node := by
            rcases (runtime.program.discharge state.visible.timeouts).candidateMessage?_effect
                state.service state.visible.events message result hmessage with
              ⟨node, handle, hpayload, rfl⟩ | ⟨node, handle, value, hpayload, rfl⟩ <;>
                simp [hpayload, SealedProgram.Payload.node?, SealedProgram.Event.node]
          intro htimeout
          simp [hpayload, htimeout] at hgate
        · intro node value hevent
          obtain ⟨owner, source, requires, handle, hrule, hselected, _howner, _hvalue⟩ :=
            (runtime.program.discharge state.visible.timeouts).candidateMessage?_opening_sound
              state.service result.1 state.visible.events message node value
              (by simpa only [← hevent] using hmessage)
          have haccepted := SealedProgram.accepted_mem_of_accepted?_eq_some hselected
          simp only [SealedProgram.discharge, List.getElem?_map] at hrule
          cases horiginal : runtime.program.rules[node]? with
          | none => simp [horiginal] at hrule
          | some original =>
              simp only [horiginal, Option.map_some, Option.some.injEq] at hrule
              refine ⟨owner, source, original.requires, handle, ?_, haccepted⟩
              have hshape : original =
                  ({ kind := .reveal owner source, requires := original.requires } :
                    SealedRule Principal) := by
                cases original
                simp_all [SealedRule.discharge]
              exact congrArg some hshape

/-- The public timeout settlement invariant holds under arbitrary native
candidate-host policies, including adversarial candidate preparation. -/
theorem runPolicies_candidate_settlementInvariant
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.candidateApplication.PolicyExecution)
    (hinitial : SettlementInvariant runtime execution.native.application.visible)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies
      players environment schedule execution).support) :
    SettlementInvariant runtime next.native.application.visible := by
  apply runtime.candidateApplication.runPolicies_application_invariant
    (fun state => SettlementInvariant runtime state.visible) ?_ ?_ ?_
    players environment schedule execution next hinitial hnext
  · intro state owner command hstate
    exact hstate
  · intro state message result hstate hresult
    exact hstate.candidateHandle message hresult
  · intro state command result hstate hresult
    simp only [candidateApplication, host, FinDist.mem_support_pure] at hresult
    subst result
    exact hstate.clock.refresh true

end Interaction.SealedResolution
