/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateSubmission
import Interaction.SealedCandidateRounds
import Interaction.SealedResolutionDeadline

/-! # Candidate delivery with independent handles and unopenable commitments -/

noncomputable section

namespace InteractionTests.SealedCandidateSubmission

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

private def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.reveal false 0, [0]⟩]⟩, none, 3⟩

private def commitment : Message Bool (SealedProgram.Payload Bool (Option Bool)) :=
  ⟨(false, 0), .commitment 0 (false, 7)⟩

private def submitted : runtime.candidateApplication.PolicyExecution :=
  let initial := State.initial runtime.candidateApplication runtime.candidateInitial
  PolicyExecution.initial _
    { initial with pool := (initial.pool.submit false commitment.payload).2 }

/-- A candidate need not have an opening for its commitment packet to be ready.
Its candidate number differs from both its source node and its message serial. -/
theorem unprepared_commitment_is_ready :
    SealedResolution.CandidateSubmissionReady runtime submitted.native.application commitment 0 ∧
      submitted.native.application.service.lookup (false, 7) = .fresh :=
  ⟨.commitment false 0 0 (false, 7) [] rfl rfl rfl, rfl⟩

theorem unprepared_inclusion_fixes_unopenable :
    let included := runtime.candidateApplication.includePending submitted.native (false, 0)
    included.application.visible.completed 0 = true ∧
      included.application.service.lookup (false, 7) = .unopenable := by
  decide

/-- Even with arbitrary policies, the ready packet cannot disappear from a
drained queue without completing its node. -/
theorem drained_unprepared_commitment_completes
    (players : Bool → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Bool)) (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment schedule
      submitted).support) (hdrained : next.native.pool.pending = []) :
    next.native.application.visible.completed 0 = true := by
  rcases SealedResolution.runPolicies_candidate_pendingOrCompleted players environment schedule
      submitted next (show commitment ∈ submitted.native.pool.pending from by
        change commitment ∈ [commitment]
        exact List.mem_cons_self)
      unprepared_commitment_is_ready.1 hnext with hdone | ⟨hpending, _⟩
  · exact hdone
  · simp only [hdrained, List.not_mem_nil] at hpending

private def opening : Message Bool (SealedProgram.Payload Bool (Option Bool)) :=
  ⟨(false, 0), .opening 1 (false, 7) (some true)⟩

private def openingState : runtime.candidateApplication.PolicyExecution :=
  let application : runtime.candidateApplication.Application :=
    ⟨((CommitmentCandidates.empty.prepare false 7 (some true)).accept (false, 7)),
      runtime.refresh false { events := [.accepted 0 (false, 7)] }⟩
  let initial := State.initial runtime.candidateApplication application
  PolicyExecution.initial _
    { initial with pool := (initial.pool.submit false opening.payload).2 }

private theorem opening_ready :
    SealedResolution.CandidateSubmissionReady runtime openingState.native.application opening 1 :=
  .opening false 0 1 0 (false, 7) (some true) [0] rfl rfl (by decide) (by decide) (by decide)

/-- Intervening replacements, other preparations, and arbitrary scheduling
cannot invalidate an already-ready opening of the selected candidate. -/
theorem drained_opening_completes
    (players : Bool → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Bool)) (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment schedule
      openingState).support) (hdrained : next.native.pool.pending = []) :
    next.native.application.visible.completed 1 = true := by
  rcases SealedResolution.runPolicies_candidate_pendingOrCompleted players environment schedule
      openingState next (show opening ∈ openingState.native.pool.pending from by
        change opening ∈ [opening]
        exact List.mem_cons_self)
      opening_ready hnext with hdone | ⟨hpending, _⟩
  · exact hdone
  · simp only [hdrained, List.not_mem_nil] at hpending

/-- The shared deadline law applies to the actual candidate stopped driver
without assumptions on any player or wire policy. -/
theorem candidate_rounds_have_genuine_deadlines
    (players : Bool → runtime.candidateApplication.PlayerPolicy)
    (wire : runtime.candidateApplication.WirePolicy) (total : Nat)
    (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateRoundDriver.runRounds [false, true] 2 players wire total
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support) :
    next.native.application.visible.DeadlineSound runtime :=
  runtime.runRounds_deadlineSound
    (fun (state : CommitmentCandidates Bool Nat (Option Bool)) owner slot value =>
      state.prepare owner slot value) runtime.candidateHandle runtime.candidateHandle_records
    [false, true] 2 players wire total _ next rfl
    (SealedResolution.PublicState.DeadlineSound.initial runtime) hnext

end InteractionTests.SealedCandidateSubmission
