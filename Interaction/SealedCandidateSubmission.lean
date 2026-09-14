/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateAcceptance
import Interaction.SealedResolutionSubmission

/-! # Persistent ready submissions in the candidate host

A ready commitment or opening remains pending until its node completes. The
proof allows arbitrary intervening policies, candidate preparations, competing
submissions, delivery, replay, and clock steps. Commitment readiness does not
require an openable handle. Opening readiness requires precisely the selected
handle and its fixed opening value.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Stable admission data for one authenticated candidate packet. Whether
the site has already completed is checked separately by inclusion. -/
inductive CandidateSubmissionReady (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)) :
    Message Principal (SealedProgram.Payload Principal Value) → Nat → Prop where
  | commitment (owner : Principal) (serial node : Nat)
      (handle : CommitmentHandle Principal Nat) (requires : List Nat)
      (hrule : runtime.program.rules[node]? = some ⟨.commit owner, requires⟩)
      (howner : handle.1 = owner) (hrequires : requires.all state.visible.completed = true) :
      CandidateSubmissionReady runtime state ⟨(owner, serial), .commitment node handle⟩ node
  | opening (owner : Principal) (serial node source : Nat)
      (handle : CommitmentHandle Principal Nat) (value : Value) (requires : List Nat)
      (hrule : runtime.program.rules[node]? = some ⟨.reveal owner source, requires⟩)
      (howner : handle.1 = owner)
      (haccepted : SealedProgram.accepted? state.visible.events source = some handle)
      (hvalue : state.service.lookup handle = .openable value)
      (hrequires : requires.all state.visible.completed = true) :
      CandidateSubmissionReady runtime state ⟨(owner, serial), .opening node handle value⟩ node

variable [DecidableEq Principal] [DecidableEq Value]
variable {runtime : SealedResolution Principal Value}
variable {state : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)}
variable {target : Message Principal (SealedProgram.Payload Principal Value)} {node : Nat}

namespace CandidateSubmissionReady

omit [DecidableEq Value] in
theorem prepare (ready : CandidateSubmissionReady runtime state target node)
    (actor : Principal) (slot : Nat) (value : Value) :
    CandidateSubmissionReady runtime
      { state with service := state.service.prepare actor slot value } target node := by
  cases ready with
  | commitment owner serial node handle requires hrule howner hrequires =>
      exact .commitment owner serial node handle requires hrule howner hrequires
  | opening owner serial node source handle claimed requires hrule howner haccepted hvalue
    hrequires =>
      refine opening (state := { state with service := state.service.prepare actor slot value })
        owner serial node source handle claimed requires hrule howner haccepted ?_ hrequires
      rw [state.service.lookup_prepare_eq_of_not_fresh handle actor slot value]
      · exact hvalue
      · rw [hvalue]; simp

theorem handle (ready : CandidateSubmissionReady runtime state target node)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (next : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))
    (hnext : runtime.candidateHandle state message = some next) :
    CandidateSubmissionReady runtime next target node := by
  have hcompleted : ∀ index, state.visible.completed index = true →
      next.visible.completed index = true := fun index hindex =>
    handle_preserves_completed runtime runtime.candidateHandle runtime.candidateHandle_records
      state next message index hindex hnext
  have hall : ∀ requires : List Nat, requires.all state.visible.completed = true →
      requires.all next.visible.completed = true := by
    intro requires hrequires
    exact List.all_eq_true.mpr fun index hindex =>
      hcompleted index (List.all_eq_true.mp hrequires index hindex)
  cases ready with
  | commitment owner serial node handle requires hrule howner hrequires =>
      exact .commitment owner serial node handle requires hrule howner (hall requires hrequires)
  | opening owner serial node source handle claimed requires hrule howner haccepted hvalue
    hrequires =>
      refine .opening owner serial node source handle claimed requires hrule howner ?_ ?_
        (hall requires hrequires)
      · obtain ⟨event, heffect⟩ := runtime.candidateHandle_records state message next hnext
        rw [heffect, runtime.refresh_accepted?]
        exact SealedProgram.accepted?_append_of_some _ _ source handle haccepted
      · rw [runtime.candidateHandle_lookup_eq_of_not_fresh state next message handle
          (by rw [hvalue]; simp) hnext]
        exact hvalue

omit [DecidableEq Principal] [DecidableEq Value] in
theorem tick (ready : CandidateSubmissionReady runtime state target node) :
    CandidateSubmissionReady runtime (runtime.tick state) target node := by
  have hall : ∀ requires : List Nat, requires.all state.visible.completed = true →
      requires.all (runtime.tick state).visible.completed = true := by
    intro requires hrequires
    exact List.all_eq_true.mpr fun index hindex => runtime.refresh_completed true _ index
      (List.all_eq_true.mp hrequires index hindex)
  cases ready with
  | commitment owner serial node handle requires hrule howner hrequires =>
      exact .commitment owner serial node handle requires hrule howner (hall requires hrequires)
  | opening owner serial node source handle claimed requires hrule howner haccepted hvalue
    hrequires =>
      exact .opening owner serial node source handle claimed requires hrule howner
        ((runtime.refresh_accepted? true _ source).trans haccepted) hvalue (hall requires hrequires)

/-- Inclusion of this packet completes its site, including the case where a
competing packet or a deadline has already completed it. -/
theorem include_completed (execution : runtime.candidateApplication.State) (id : MessageId
  Principal)
    (ready : CandidateSubmissionReady runtime execution.application target node)
    (hlookup : execution.pool.lookup id = some target) :
    (runtime.candidateApplication.includePending execution id).application.visible.completed
      node = true := by
  cases hcompleted : execution.application.visible.completed node with
  | true =>
      exact runtime.candidateApplication.includePending_application_invariant
        (fun state => state.visible.completed node = true)
        (fun state message next hbefore hnext =>
          handle_preserves_completed runtime runtime.candidateHandle runtime.candidateHandle_records
            state next message node hbefore hnext) execution id hcompleted
  | false =>
      have hchecks := Bool.or_eq_false_iff.mp hcompleted
      have htimeout : execution.application.visible.timeouts.contains node = false := hchecks.2
      cases ready with
      | commitment owner serial node handle requires hrule howner hrequires =>
          let next : runtime.candidateApplication.Application :=
            ⟨execution.application.service.accept handle, runtime.refresh false
              { execution.application.visible with
                events := execution.application.visible.events ++ [.accepted node handle] }⟩
          have hhandle : runtime.candidateHandle execution.application
              ⟨(owner, serial), .commitment node handle⟩ = some next := by
            have hrequires' : SealedProgram.prerequisitesDone execution.application.visible.events
                ((⟨.commit owner, requires⟩ : SealedRule Principal).discharge
                  execution.application.visible.timeouts) = true := by
              rw [PublicState.prerequisitesDone_discharge]
              exact hrequires
            change (requires.filter (fun prior =>
              !execution.application.visible.timeouts.contains prior)).all
                (SealedProgram.done execution.application.visible.events) = true at hrequires'
            simp only [candidateHandle, SealedProgram.Payload.node?, Option.any_some, htimeout,
              Bool.false_eq_true, ↓reduceIte, SealedProgram.candidateMessage?,
                SealedProgram.discharge,
              List.getElem?_map, hrule, Option.map_some, SealedRule.discharge, Message.sender,
              howner, hchecks.1, SealedProgram.prerequisitesDone, hrequires', and_self,
              Option.bind_eq_bind, Option.bind_some]
            rfl
          rw [runtime.candidateApplication.includePending_accept execution id _ next hlookup
            hhandle]
          apply runtime.refresh_completed false _ node
          simp [PublicState.completed, SealedProgram.done, SealedProgram.Event.node]
      | opening owner serial node source handle claimed requires hrule howner haccepted hvalue
        hrequires =>
          let next : runtime.candidateApplication.Application :=
            ⟨execution.application.service, runtime.refresh false
              { execution.application.visible with
                events := execution.application.visible.events ++ [.opened node claimed] }⟩
          have hhandle : runtime.candidateHandle execution.application
              ⟨(owner, serial), .opening node handle claimed⟩ = some next := by
            have hrequires' : SealedProgram.prerequisitesDone execution.application.visible.events
                ((⟨.reveal owner source, requires⟩ : SealedRule Principal).discharge
                  execution.application.visible.timeouts) = true := by
              rw [PublicState.prerequisitesDone_discharge]
              exact hrequires
            change (requires.filter (fun prior =>
              !execution.application.visible.timeouts.contains prior)).all
                (SealedProgram.done execution.application.visible.events) = true at hrequires'
            simp only [candidateHandle, SealedProgram.Payload.node?, Option.any_some, htimeout,
              Bool.false_eq_true, ↓reduceIte, SealedProgram.candidateMessage?,
                SealedProgram.discharge,
              List.getElem?_map, hrule, Option.map_some, SealedRule.discharge, Message.sender,
              howner, hchecks.1, SealedProgram.prerequisitesDone, hrequires', haccepted,
              CommitmentCandidates.verify, hvalue, decide_true, and_self,
              Option.bind_eq_bind, Option.bind_some]
            rfl
          rw [runtime.candidateApplication.includePending_accept execution id _ next hlookup
            hhandle]
          apply runtime.refresh_completed false _ node
          simp [PublicState.completed, SealedProgram.done, SealedProgram.Event.node]

end CandidateSubmissionReady

/-- Under arbitrary candidate policies, a ready submitted packet remains
pending until its site completes. Draining the pending pool therefore completes
that site. No other player's candidate is required to be openable. -/
theorem runPolicies_candidate_pendingOrCompleted
    (players : Principal → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : runtime.candidateApplication.PolicyExecution)
    (hpending : target ∈ execution.native.pool.pending)
    (hready : CandidateSubmissionReady runtime execution.native.application target node)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment schedule
      execution).support) :
    next.native.application.visible.completed node = true ∨
      (target ∈ next.native.pool.pending ∧
        CandidateSubmissionReady runtime next.native.application target node) := by
  obtain ⟨actions, _, hrun⟩ := runtime.candidateApplication.runPolicies_native_support
    players environment schedule execution next hnext
  exact runtime.run_pending_or_completed
    (fun (state : CommitmentCandidates Principal Nat Value) owner slot value =>
      state.prepare owner slot value)
    runtime.candidateHandle runtime.candidateHandle_records
    (fun state => CandidateSubmissionReady runtime state target node) target node
    (fun _ actor command h => h.prepare actor command.down.1 command.down.2)
    (fun _ message next h hnext => h.handle message next hnext)
    (fun _ h => h.tick) (fun state id h hlookup => h.include_completed state id hlookup)
    actions execution.native next.native (Or.inr ⟨hpending, hready⟩) hrun

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.runPolicies_candidate_pendingOrCompleted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.runPolicies_candidate_pendingOrCompleted
