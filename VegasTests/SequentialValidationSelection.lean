/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationGuess
import Vegas.Pending.ReactiveContinuationObservation

/-! # Final native selection admits only Bob's current proposal -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

theorem native_bob_playerView (bit : Bool) (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control))
    (view : control.execution.observe nativeApp true =
      (nativeBobExecution bit).observe nativeApp true) :
    control.execution.application.playerView true =
      (nativeBobExecution bit).application.playerView true :=
  reactive_playerView_congr nativeRuntime nativeLeaks _ _ true
    (congrArg ReactiveApplication.PlayerView.application view)
    ((native_remembered control trace).trans (native_remembered _ (nativeBobTrace bit)).symm)

theorem native_bob_ready (bit : Bool) (execution : nativeApp.Execution)
    (views : execution.application.playerView true =
      (nativeBobExecution bit).application.playerView true) :
    execution.application.publicView.EventReady guessEvent := by
  have publicEq : execution.application.publicView =
      (nativeBobExecution bit).application.publicView :=
    congrArg PlayerView.publicView views
  rw [publicEq, State.publicView_eventReady, native_bob_application]
  exact native_secret_ready bit

def nativeFinalCommand (execution : nativeApp.Execution) (action : nativeApp.Action) :
    nativeApp.Command :=
  match action.transmission with
  | some (.submit submission) =>
      if submission.call.packet.event? nativeGraph = some guessEvent then
        .include (true, execution.network.nextSerial true) else .wait
  | _ => .wait

theorem native_bob_selection (bit : Bool) (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some true)
    (empty : control.execution.recall true = [])
    (views : control.execution.application.playerView true =
      (nativeBobExecution bit).application.playerView true)
    (action : nativeApp.Action) :
    nativeScheduler (control.execution.respond nativeApp true action).environmentRecall
      ((control.execution.respond nativeApp true action).observeEnvironment nativeApp) =
        FinDist.pure (nativeFinalCommand control.execution action) := by
  classical
  let execution := control.execution
  have rawTrace := nativeMenu.toRawTrace nativeInitialLaw 56 nativeScheduler trace
  have position := (native_bob_remaining control trace active).1
  have serials := nativeApp.serialsBeforeNext_history nativeScheduler nativeInitialLaw 56 rawTrace
  have retained := nativeApp.pendingOrPublished_history nativeScheduler nativeInitialLaw 56 rawTrace
  have noOld : MessageNetwork.eligibleIds
      (execution.network.unpublished (nativeApp.authorizedEligibility dependencyCondition
        execution.environmentRecall (eventProposal guessEvent true))) execution.network.pending =
          ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro id member
    obtain ⟨message, filtered, _⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have selected := (List.mem_filter.mp filtered).2
    simp only [MessageNetwork.unpublished, ReactiveApplication.authorizedEligibility,
      eventProposal, Bool.and_eq_true, decide_eq_true_eq] at selected
    exact native_no_bob_pending control trace empty message
      (List.mem_filter.mp filtered).1 selected.1.1.1
  have old : nativeApp.authorizedUniform dependencyCondition execution.environmentRecall
      (execution.observeEnvironment nativeApp) (eventProposal guessEvent true) =
        FinDist.pure none := by
    change MessageNetwork.chooseUniform (MessageNetwork.eligibleIds
      (execution.network.unpublished (nativeApp.authorizedEligibility dependencyCondition
        execution.environmentRecall (eventProposal guessEvent true))) execution.network.pending) = _
    rw [noOld]
    simp [MessageNetwork.chooseUniform]
  have submitted (submission : WitnessedSubmission nativeGraph) :
      nativeApp.submitsEligible (nativeApp.authorizedEligibility dependencyCondition
        execution.environmentRecall (eventProposal guessEvent true)) execution true
        ⟨some (.submit submission)⟩ =
          decide (submission.call.packet.event? nativeGraph = some guessEvent) := by
    let packet := submission.emit (nativeApp.submit execution.application true submission)
      true (execution.network.known true)
    have unpublished := serials.next_unpublished true
    have absent : (execution.network.ledger.any fun prior =>
        decide (prior.id = (true, execution.network.nextSerial true))) = false := by
      apply Bool.eq_false_iff.mpr
      intro seen
      obtain ⟨message, member, same⟩ := List.any_eq_true.mp seen
      exact unpublished (List.mem_map.mpr ⟨message, member, of_decide_eq_true same⟩)
    have permitted := nativeApp.submissionPermitted_fresh_history ReactivePlayerView.publicView
      (fun _ _ => rfl) dependencyCondition nativeInitialLaw 56 nativeScheduler control rawTrace
      true active packet
    simp only [ReactiveApplication.submitsEligible, MessageNetwork.submit,
      MessageNetwork.unpublished, ReactiveApplication.authorizedEligibility]
    rw [absent]
    simp only [Bool.not_false, Bool.and_true, eventProposal, Message.sender, true_and]
    change (decide (submission.call.packet.event? nativeGraph = some guessEvent) &&
      decide (nativeApp.SubmissionPermitted dependencyCondition execution.environmentRecall
        ⟨(true, execution.network.nextSerial true), packet⟩)) =
          decide (submission.call.packet.event? nativeGraph = some guessEvent)
    by_cases address : submission.call.packet.event? nativeGraph = some guessEvent
    · have allowed : dependencyCondition (nativeApp.observePublic execution.application)
          ⟨(true, execution.network.nextSerial true), packet⟩ := by
        intro target same predecessor member
        have identified : guessEvent = target := Option.some.inj (address.symm.trans same)
        subst target
        exact (native_bob_ready bit execution views).2 predecessor member
      simp only [address, decide_true, Bool.true_and]
      exact decide_eq_true (permitted.mpr allowed)
    · simp only [address, decide_false, Bool.false_and]
  rw [native_schedule _ _ (by
    rw [nativeApp.respond_environmentRecall, position])]
  change (nativeApp.authorizedUniform dependencyCondition _ _
    (eventProposal guessEvent true)).map _ = _
  rw [nativeApp.authorizedUniform_response_eq dependencyCondition _ _ retained,
    noOld, old, Finset.insert_empty, MessageNetwork.chooseUniform_singleton]
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => simp only [ReactiveApplication.submitsEligible, Bool.false_eq_true,
      ↓reduceIte, FinDist.map_pure, Option.elim_none, nativeFinalCommand]
  | some transmission =>
      cases transmission with
      | replay id => simp only [ReactiveApplication.submitsEligible, Bool.false_eq_true,
          ↓reduceIte, FinDist.map_pure, Option.elim_none, nativeFinalCommand]
      | submit submission =>
          rw [submitted]
          by_cases address : submission.call.packet.event? nativeGraph = some guessEvent <;>
            simp only [nativeFinalCommand, address, decide_true, decide_false, ↓reduceIte,
              Bool.false_eq_true, FinDist.map_pure, Option.elim_some, Option.elim_none]

end VegasTests.SequentialValidation
