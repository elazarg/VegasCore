/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperBindingRecords
import Vegas.Examples.CommitSeedBroadcastPublicationAfterSubmission
import Interaction.ReactiveRecordedResponseAfter
import Vegas.Examples.CommitSeedBroadcastBudget
import Vegas.Examples.CommitSeedBroadcastTailDecision

/-! # Actual remembered proper publications protect the original continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

variable (clock : Nat)

/-- A remembered publication callback on the original proper trajectory
already protects the owner at the actual later endpoint. The successful
binding value and the literal opening response are derived from original
records and their exact before-view, not supplied as endpoint assumptions. -/
theorem scheduled_proper_recorded_publication_survives
    (seed : Seeds) (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (owner : Player)
    (ownConsistent : (scheduledProperPolicy clock owner).Consistent (final.execution.recall owner))
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (publication : coordinate.event = revealEvent owner)
    (entry : app.PlayerEntry) (recorded : entry ∈ final.execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    owner ∉ final.execution.application.current.excluded := by
  obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp recorded
  obtain ⟨remaining, execution, prior, postTrace, kept, past, viewed, _allowed, _before, _length⟩ :=
    countedMenu.recorded_response_after initial horizon (family seed) final trace owner
      earlier entry later recalled
  have firstConsistent : (scheduledProperPolicy clock owner).Consistent (earlier ++ [entry]) := by
    apply ReactiveApplication.Policy.Consistent.of_append (after := later)
    simpa only [List.append_assoc, List.singleton_append] using (recalled ▸ ownConsistent)
  have before := ((scheduledProperPolicy clock owner).consistent_snoc_iff earlier entry).mp
    firstConsistent
  have priorConsistent : (scheduledProperPolicy clock owner).Consistent (execution.recall
    owner) := by
    rw [past]
    exact before.1
  have selected : entry.action ∈ (scheduledProperPolicy clock owner (execution.recall owner)
      (execution.observe app owner)).support := by
    rw [past, ← viewed]
    exact before.2
  have valid := raw_native_valid (family seed) ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) prior)
  rw [viewed] at requested
  have request := (execution.application.requests_publicView valid owner coordinate).mp requested
  have coordinateEq : coordinate =
      ⟨execution.application.attempt, revealEvent owner⟩ := by
    cases coordinate with
    | mk attempt event => exact congrArg₂ CommitAttemptEvent.mk request.1 publication
  have sourceRequest : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩ := coordinateEq ▸ request
  have budget := family_requested_remaining seed ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) prior)
      ⟨execution.application.attempt, revealEvent owner⟩ owner sourceRequest
  cases remaining with
  | zero =>
      change (20 : Nat) < 0 at budget
      omega
  | succ remaining =>
    have sourceRetired : execution.application.attempt ≠ originalAttempt := by
      rwa [← request.1]
    have preceding : bindingEvent owner ∈ graph.order.predecessors (revealEvent owner) :=
      (reveal_predecessors owner (bindingEvent owner)).mpr owner.isLt
    have completed := sourceRequest.2.2.1.2 preceding
    have stored := scheduled_proper_completed_binding_success_of_consistent clock seed
      ⟨remaining + 1, some owner, execution⟩ prior owner priorConsistent completed
        sourceRequest.2.2.2.2
    have typed : (ownBindingRef owner).get? execution.application.current.native.config.store =
        some (.success true) := by
      fin_cases owner <;> exact stored
    have unsubmitted := fixed_tail_callback_unsubmitted seed (remaining + 1) execution owner prior
      ⟨execution.application.attempt, revealEvent owner⟩ sourceRetired sourceRequest
    have inputRecall := PhaseCount.countRecall_history runtime leaks
      (countedMenu.toRawTrace initial horizon (family seed) prior)
    have unsent (message : Message Player (CommitAttemptPacket graph))
        (member : message ∈ app.outputs (execution.recall owner)) :
        PhaseCount.event? message.payload ≠
          some ⟨execution.application.attempt, revealEvent owner⟩ := by
      rw [← inputRecall.1 owner] at member
      exact unsubmitted message (List.mem_filter.mp member).1
        (of_decide_eq_true (List.mem_filter.mp member).2)
    obtain ⟨checks, codeEq, node⟩ := own_reveal_descriptor owner
    obtain ⟨candidate, _accepted, literal⟩ := properPolicy_opening_response (lateAtRule clock)
      (family seed) ⟨remaining + 1, some owner, execution⟩ prior owner (revealEvent owner)
        (ownBindingRef owner) checks (revealEvent_layout owner) codeEq node sourceRequest unsent
          true typed
    have proper : scheduledProperPolicy clock owner (execution.recall owner)
      (execution.observe app owner) =
        properPolicy (lateAtRule clock) owner (execution.recall owner)
          (execution.observe app owner) := by
      unfold scheduledProperPolicy
      exact ite_eq_right (fun both => sourceRetired both.1)
    rw [proper, literal, PMF.mem_support_pure_iff] at selected
    let material : WitnessedSubmission graph :=
      disclosureSubmission (.opening (revealEvent owner) candidate ⟨.bool, true⟩)
    have actionEq : entry.action = (⟨some material⟩ : app.Action) := selected
    have properSupported : (⟨some material⟩ : app.Action) ∈
        (properPolicy (lateAtRule clock) owner (execution.recall owner)
          (execution.observe app owner)).support := by
      rw [literal]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    have offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
        (execution.recall owner) (execution.observe app owner) :=
      properPolicy_counted (lateAtRule clock) owner (execution.recall owner)
        (execution.observe app owner) ⟨some material⟩ properSupported
    rcases entry with ⟨entryView, ⟨transmission⟩, emitted⟩
    have transmissionEq : transmission = some material :=
      congrArg (fun action : app.Action => action.transmission) actionEq
    cases transmissionEq
    exact family_publication_after_submission_survives seed (remaining + 1) execution owner prior
      sourceRetired sourceRequest true stored material offered postTrace final trace kept

end Vegas.Examples.CommitSeedBroadcast
