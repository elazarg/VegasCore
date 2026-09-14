/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateResolution
import Interaction.SealedResolutionEvents

/-! # Public event provenance in the candidate host

The candidate validator supplies the same public rule-provenance invariant as
the registered host. The clock and timeout proofs are shared. No openability
or canonical-source-slot requirement enters the public invariant.
-/

noncomputable section

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- A successfully admitted event has the corresponding rule kind. Private
candidate preparation is irrelevant to this public provenance statement. -/
theorem candidateMessage?_event_kind
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (Event Principal Value))
    (message : Message Principal (Payload Principal Value))
    (result : CommitmentCandidates Principal Nat Value × Event Principal Value)
    (hresult : program.candidateMessage? candidates events message = some result) :
    ∃ rule, program.rules[result.2.node]? = some rule ∧
      match result.2 with
      | .accepted _ _ => ∃ owner, rule.kind = .commit owner
      | .opened _ _ => ∃ owner source, rule.kind = .reveal owner source := by
  unfold candidateMessage? at hresult
  cases hpayload : message.payload with
  | malformed | cleartext => simp only [hpayload] at hresult; contradiction
  | commitment node handle =>
      simp only [hpayload] at hresult
      cases hrule : program.rules[node]? with
      | none => simp only [hrule] at hresult; contradiction
      | some rule =>
          simp only [hrule] at hresult
          cases hkind : rule.kind with
          | disabled | reveal => simp only [hkind] at hresult; contradiction
          | commit owner =>
              simp only [hkind] at hresult
              split at hresult
              · cases hresult
                exact ⟨rule, hrule, owner, hkind⟩
              · contradiction
  | opening node handle claimed =>
      simp only [hpayload] at hresult
      cases hrule : program.rules[node]? with
      | none => simp only [hrule] at hresult; contradiction
      | some rule =>
          simp only [hrule] at hresult
          cases hkind : rule.kind with
          | disabled | commit => simp only [hkind] at hresult; contradiction
          | reveal owner source =>
              simp only [hkind] at hresult
              split at hresult
              · cases hresult
                exact ⟨rule, hrule, owner, source, hkind⟩
              · contradiction

end Interaction.SealedProgram

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- The candidate handler preserves public event provenance, including when
it accepts a handle that has no opening. -/
theorem PublicEventInvariant.candidateHandle
    {runtime : SealedResolution Principal Value}
    {state next : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)}
    (invariant : PublicEventInvariant runtime state.visible)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.candidateHandle state message = some next) :
    PublicEventInvariant runtime next.visible := by
  unfold SealedResolution.candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge state.visible.timeouts).candidateMessage?
        state.service state.visible.events message with
    | none => simp [hmessage] at hnext
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
        subst next
        apply PublicEventInvariant.refresh (resolveExpired := false)
        obtain ⟨rule, hrule, hkind⟩ :=
          (runtime.program.discharge state.visible.timeouts).candidateMessage?_event_kind
            state.service state.visible.events message result hmessage
        simp only [SealedProgram.discharge, List.getElem?_map] at hrule
        cases horiginal : runtime.program.rules[result.2.node]? with
        | none => simp [horiginal] at hrule
        | some original =>
            simp only [horiginal, Option.map_some, Option.some.injEq] at hrule
            subst rule
            rcases result with ⟨candidates, event⟩
            cases event with
            | accepted node handle =>
                obtain ⟨owner, howner⟩ := hkind
                exact invariant.appendAccepted node handle owner original horiginal howner
            | opened node value =>
                obtain ⟨owner, source, howner⟩ := hkind
                apply invariant.appendOpened node value owner source original.requires
                have hshape : original =
                    ({ kind := .reveal owner source, requires := original.requires } :
                      SealedRule Principal) := by
                  cases original
                  simp_all [SealedRule.discharge]
                exact horiginal.trans (congrArg some hshape)

/-- Arbitrary randomized candidate-host policies preserve the public invariant.
Only the shared application invariant lifting is used; there is no new runner
or whole-execution induction. -/
theorem runPolicies_candidate_publicEvents
    (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.candidateApplication.PolicyExecution)
    (hinitial : PublicEventInvariant runtime execution.native.application.visible)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies
      players environment schedule execution).support) :
    PublicEventInvariant runtime next.native.application.visible := by
  apply runtime.candidateApplication.runPolicies_application_invariant
    (fun state => PublicEventInvariant runtime state.visible) ?_ ?_ ?_
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
