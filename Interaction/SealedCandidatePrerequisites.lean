/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateAcceptance
import Interaction.SealedCandidateBinding
import Interaction.SealedResolutionSubmission

/-! # Completed prerequisites of accepted candidates

Candidate acceptance checks the selected commitment rule's prerequisites.
Completion is monotone under later message handling and timeout resolution, so
those prerequisites remain completed throughout every subsequent policy run.
-/

noncomputable section

namespace Interaction.SealedProgram

universe uPrincipal uValue
variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- A newly accepted candidate passed the commitment rule's prerequisite
check. This is the admission-time fact before timeout discharge is translated
back to the original rule. -/
theorem candidateMessage?_accepted_prerequisites
    (program : SealedProgram Principal)
    (candidates next : CommitmentCandidates Principal Nat Value)
    (events : List (Event Principal Value))
    (message : Message Principal (Payload Principal Value)) (node : Nat)
    (handle : CommitmentHandle Principal Nat)
    (hvalid : program.candidateMessage? candidates events message =
      some (next, .accepted node handle)) :
    ∃ requires, program.rules[node]? = some ⟨.commit handle.1, requires⟩ ∧
      requires.all (done events) = true := by
  rcases program.candidateMessage?_effect candidates events message _ hvalid with
    ⟨index, selected, hpayload, heq⟩ | ⟨index, selected, value, _hpayload, heq⟩
  · cases heq
    simp only [candidateMessage?, hpayload] at hvalid
    cases hrule : program.rules[node]? with
    | none => simp [hrule] at hvalid
    | some rule =>
        simp only [hrule] at hvalid
        cases hkind : rule.kind with
        | disabled | reveal => simp only [hkind] at hvalid; contradiction
        | commit owner =>
            simp only [hkind] at hvalid
            split at hvalid
            next hchecks =>
              refine ⟨rule.requires, ?_, hchecks.2.2.2⟩
              have hshape : rule = ⟨.commit handle.1, rule.requires⟩ := by
                cases rule
                simp_all
              exact congrArg some hshape
            next => contradiction
  · cases heq

end Interaction.SealedProgram

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue
variable {Principal : Type uPrincipal} {Value : Type uValue}
variable (runtime : SealedResolution Principal Value)

/-- Every accepted commitment retains the original rule whose prerequisites
were completed when it was accepted, and those prerequisites remain completed
in the current public state. -/
def CandidatePrerequisiteInvariant (state : PublicState Principal Value) : Prop :=
  ∀ node handle, SealedProgram.Event.accepted node handle ∈ state.events →
    ∃ owner requires,
      runtime.program.rules[node]? = some ⟨.commit owner, requires⟩ ∧
        requires.all state.completed = true

namespace CandidatePrerequisiteInvariant

variable {runtime} {state : PublicState Principal Value}

theorem refresh (invariant : CandidatePrerequisiteInvariant runtime state)
    (resolveExpired : Bool) :
    CandidatePrerequisiteInvariant runtime (runtime.refresh resolveExpired state) := by
  intro node handle haccepted
  obtain ⟨owner, requires, hrule, hrequires⟩ := invariant node handle
    ((runtime.refresh_accepted_iff resolveExpired state node handle).mp haccepted)
  refine ⟨owner, requires, hrule, ?_⟩
  exact List.all_eq_true.mpr fun prerequisite hprerequisite =>
    runtime.refresh_completed resolveExpired state prerequisite
      (List.all_eq_true.mp hrequires prerequisite hprerequisite)

theorem initial : CandidatePrerequisiteInvariant runtime runtime.candidateInitial.visible := by
  exact (show CandidatePrerequisiteInvariant runtime {} from by
    simp [CandidatePrerequisiteInvariant]).refresh false

variable [DecidableEq Principal] [DecidableEq Value]

theorem handle
    {application next : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value)}
    (invariant : CandidatePrerequisiteInvariant runtime application.visible)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.candidateHandle application message = some next) :
    CandidatePrerequisiteInvariant runtime next.visible := by
  have hcompleted : ∀ prerequisite, application.visible.completed prerequisite = true →
      next.visible.completed prerequisite = true := fun prerequisite hprerequisite =>
    handle_preserves_completed runtime runtime.candidateHandle
      runtime.candidateHandle_records application next message prerequisite hprerequisite hnext
  unfold candidateHandle at hnext
  split at hnext
  · contradiction
  · cases hmessage : (runtime.program.discharge application.visible.timeouts).candidateMessage?
        application.service application.visible.events message with
    | none => simp [hmessage] at hnext
    | some result =>
        simp only [hmessage, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
        subst next
        intro node handle haccepted
        have hbefore := (runtime.refresh_accepted_iff false
          { application.visible with events := application.visible.events ++ [result.2] }
          node handle).mp haccepted
        simp only [List.mem_append, List.mem_singleton] at hbefore
        rcases hbefore with hprior | hnew
        · obtain ⟨owner, requires, hrule, hrequires⟩ := invariant node handle hprior
          refine ⟨owner, requires, hrule, ?_⟩
          exact List.all_eq_true.mpr fun prerequisite hprerequisite =>
            hcompleted prerequisite
              (List.all_eq_true.mp hrequires prerequisite hprerequisite)
        · have hacceptedMessage :
              (runtime.program.discharge application.visible.timeouts).candidateMessage?
                application.service application.visible.events message =
                  some (result.1, .accepted node handle) := by
            simpa only [hnew] using hmessage
          obtain ⟨dischargedRequires, hdischargedRule, hdischargedRequires⟩ :=
            (runtime.program.discharge application.visible.timeouts
              ).candidateMessage?_accepted_prerequisites application.service result.1
                application.visible.events message node handle hacceptedMessage
          simp only [SealedProgram.discharge, List.getElem?_map] at hdischargedRule
          cases horiginal : runtime.program.rules[node]? with
          | none => simp [horiginal] at hdischargedRule
          | some original =>
              simp only [horiginal, Option.map_some, Option.some.injEq] at hdischargedRule
              have hshape : original = ⟨.commit handle.1, original.requires⟩ := by
                cases original
                simp_all [SealedRule.discharge]
              have hrequires : original.requires.all application.visible.completed = true := by
                rw [← PublicState.prerequisitesDone_discharge]
                rw [hdischargedRule]
                exact hdischargedRequires
              refine ⟨handle.1, original.requires, congrArg some hshape, ?_⟩
              exact List.all_eq_true.mpr fun prerequisite hprerequisite =>
                hcompleted prerequisite
                  (List.all_eq_true.mp hrequires prerequisite hprerequisite)

end CandidatePrerequisiteInvariant

variable [DecidableEq Principal] [DecidableEq Value]

/-- Arbitrary candidate player and environment policies preserve accepted
commitment prerequisites from the actual candidate initial state. -/
theorem runPolicies_candidate_prerequisites
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support) :
    CandidatePrerequisiteInvariant runtime next.native.application.visible := by
  apply runtime.candidateApplication.runPolicies_initial_application_invariant
    (fun state => CandidatePrerequisiteInvariant runtime state.visible) ?_ ?_ ?_
    players environment schedule (State.initial _ runtime.candidateInitial) next
    CandidatePrerequisiteInvariant.initial hnext
  · intro application owner command hstate
    exact hstate
  · intro application message result hstate hresult
    exact hstate.handle message hresult
  · intro application command result hstate hresult
    simp only [candidateApplication, host] at hresult
    have heq := FinDist.mem_support_pure.mp hresult
    subst result
    have hclock : CandidatePrerequisiteInvariant runtime
        { application.visible with clock := application.visible.clock + 1 } := hstate
    exact hclock.refresh true

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_candidate_prerequisites'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_candidate_prerequisites
