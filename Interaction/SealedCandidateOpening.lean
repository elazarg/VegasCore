/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateBinding
import Interaction.SealedResolutionBinding

/-! # Successful candidate openings before timeout

A successful opening refers to the handle accepted at its source site and
matches that handle's immutable meaning. This property holds for arbitrary
native policies before timeout; after resolution the public default may differ
from the private opening. Acceptance need not imply openability.
-/

noncomputable section

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

theorem accepted?_append_of_some (events rest : List (Event Principal Value))
    (node : Nat) (handle : CommitmentHandle Principal Nat)
    (h : accepted? events node = some handle) :
    accepted? (events ++ rest) node = some handle := by
  unfold accepted? at h ⊢
  rw [List.findSome?_append, h]
  rfl

variable [DecidableEq Principal] [DecidableEq Value]

/-- Successful opening admission supplies its actual accepted source handle,
authenticated owner, and verified value, without a canonical-slot assumption. -/
theorem candidateMessage?_opening_sound (program : SealedProgram Principal)
    (candidates next : CommitmentCandidates Principal Nat Value)
    (events : List (Event Principal Value))
    (message : Message Principal (Payload Principal Value)) (node : Nat) (value : Value)
    (hvalid : program.candidateMessage? candidates events message =
      some (next, .opened node value)) :
    ∃ owner source requires handle,
      program.rules[node]? = some ⟨.reveal owner source, requires⟩ ∧
      accepted? events source = some handle ∧ handle.1 = owner ∧
      candidates.lookup handle = .openable value := by
  rcases program.candidateMessage?_effect candidates events message _ hvalid with
    ⟨index, handle, _hpayload, heq⟩ | ⟨index, handle, claimed, hpayload, heq⟩
  · cases heq
  · cases heq
    simp only [candidateMessage?, hpayload] at hvalid
    cases hrule : program.rules[node]? with
    | none => simp [hrule] at hvalid
    | some rule =>
        simp only [hrule] at hvalid
        cases hkind : rule.kind with
        | commit | disabled => simp only [hkind] at hvalid; contradiction
        | reveal owner source =>
            simp only [hkind] at hvalid
            split at hvalid
            next hchecks =>
              refine ⟨owner, source, rule.requires, handle, ?_,
                hchecks.2.2.2.2.1, hchecks.2.1, ?_⟩
              · have heq : rule = ⟨.reveal owner source, rule.requires⟩ := by
                  cases rule
                  simp_all
                exact congrArg some heq
              · exact (candidates.verify_eq_true_iff handle value).mp hchecks.2.2.2.2.2
            next => contradiction

end Interaction.SealedProgram

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable {runtime : SealedResolution Principal Value}

/-- Before any timeout, included openings have an authenticated source-site
handle with that exact opening. Other accepted handles may be unopenable. -/
def CandidateOpeningInvariant (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)) : Prop :=
  state.visible.timeouts = [] → ∀ node value,
    SealedProgram.Event.opened node value ∈ state.visible.events →
    ∃ owner source requires handle,
      runtime.program.rules[node]? = some ⟨.reveal owner source, requires⟩ ∧
      SealedProgram.accepted? state.visible.events source = some handle ∧ handle.1 = owner ∧
      state.service.lookup handle = .openable value

omit [DecidableEq Principal] [DecidableEq Value] in
theorem CandidateOpeningInvariant.initial :
    CandidateOpeningInvariant runtime runtime.candidateInitial := by
  intro _ node value hmem
  have hevents := runtime.refresh_false_events ({} : PublicState Principal Value) rfl
  change SealedProgram.Event.opened node value ∈ (runtime.refresh false {}).events at hmem
  rw [hevents] at hmem
  exact (List.not_mem_nil hmem).elim

omit [DecidableEq Value] in
theorem CandidateOpeningInvariant.prepare
    {state : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)}
    (invariant : CandidateOpeningInvariant runtime state)
    (who : Principal) (slot : Nat) (value : Value) :
    CandidateOpeningInvariant runtime
      { state with service := state.service.prepare who slot value } := by
  intro hclear node opened hmem
  obtain ⟨owner, source, requires, handle, hrule, haccepted, howner, hvalue⟩ :=
    invariant hclear node opened hmem
  refine ⟨owner, source, requires, handle, hrule, haccepted, howner, ?_⟩
  rw [state.service.lookup_prepare_eq_of_not_fresh handle who slot value (by rw [hvalue]; simp)]
  exact hvalue

theorem CandidateOpeningInvariant.handle
    {state next : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)}
    (invariant : CandidateOpeningInvariant runtime state)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.candidateHandle state message = some next) :
    CandidateOpeningInvariant runtime next := by
  unfold candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge state.visible.timeouts).candidateMessage?
        state.service state.visible.events message with
    | none => simp [hmessage] at hnext
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
        subst next
        intro hclear node value hmem
        obtain ⟨hbefore, hevents⟩ := runtime.refresh_clear false
          { state.visible with events := state.visible.events ++ [result.2] } hclear
        change state.visible.timeouts = [] at hbefore
        have hraw : runtime.program.candidateMessage? state.service state.visible.events message =
            some result := by
          simpa only [hbefore, SealedProgram.discharge_nil] using hmessage
        rw [hevents] at hmem ⊢
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hprior | hnew
        · obtain ⟨owner, source, requires, handle, hrule, haccepted, howner, hvalue⟩ :=
            invariant hbefore node value hprior
          refine ⟨owner, source, requires, handle, hrule,
            SealedProgram.accepted?_append_of_some _ _ source handle haccepted, howner, ?_⟩
          rw [candidateMessage?_lookup_eq_of_not_fresh runtime.program state.service
            state.visible.events message result handle (by rw [hvalue]; simp) hraw]
          exact hvalue
        · obtain ⟨owner, source, requires, handle, hrule, haccepted, howner, hvalue⟩ :=
            runtime.program.candidateMessage?_opening_sound state.service result.1
              state.visible.events message node value (by simpa only [hnew] using hraw)
          refine ⟨owner, source, requires, handle, hrule,
            SealedProgram.accepted?_append_of_some _ _ source handle haccepted, howner, ?_⟩
          rw [candidateMessage?_lookup_eq_of_not_fresh runtime.program state.service
            state.visible.events message result handle (by rw [hvalue]; simp) hraw]
          exact hvalue

omit [DecidableEq Principal] [DecidableEq Value] in
theorem CandidateOpeningInvariant.tick
    {state : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)}
    (invariant : CandidateOpeningInvariant runtime state) :
    CandidateOpeningInvariant runtime (runtime.tick state) := by
  intro hclear node value hmem
  obtain ⟨hbefore, hevents⟩ := runtime.refresh_clear true
    { state.visible with clock := state.visible.clock + 1 } hclear
  change (runtime.tick state).visible.events = state.visible.events at hevents
  rw [hevents] at hmem ⊢
  exact invariant hbefore node value hmem

/-- The opening invariant holds under arbitrary randomized candidate-host
policies, malformed traffic, replay, delivery, inclusion, and clock choices. -/
theorem runPolicies_candidate_openings
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.candidateApplication.PolicyExecution)
    (hinitial : CandidateOpeningInvariant runtime execution.native.application)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment
      schedule execution).support) : CandidateOpeningInvariant runtime next.native.application := by
  apply runtime.candidateApplication.runPolicies_application_invariant
    (CandidateOpeningInvariant runtime) ?_ ?_ ?_ players environment schedule
    execution next hinitial hnext
  · intro state who command hstate
    exact hstate.prepare who command.down.1 command.down.2
  · intro state message after hstate hafter
    exact hstate.handle message hafter
  · intro state command after hstate hafter
    simp only [candidateApplication, host, FinDist.mem_support_pure] at hafter
    subst after
    exact hstate.tick

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_candidate_openings' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_candidate_openings
