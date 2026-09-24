/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGuessSettlement
import VegasTests.SelectiveAssociationDecisionContinuation
import Vegas.Pending.ReactiveAssociationEvidence
import Interaction.ReactiveInvariantContinuation
import GameTheoryExtensions.Protocol.CommittedContinuation

/-! # Information-local binding incentives for a certified Alice value -/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

theorem native_bob_site_facts (view : nativeApp.PlayerView) (control : nativeApp.Control)
    (observed : control.execution.observe nativeApp bob = view)
    (granted : view.application.publicView.serviceGrant = some bobBinding)
    (unfinished : bobBinding ∉ view.application.publicView.observation.completionOrder) :
    control.execution.application.serviceGrant = some bobBinding ∧
      bobBinding ∉ control.execution.application.config.cut.completed := by
  rw [← observed] at granted unfinished
  refine ⟨granted, ?_⟩
  change bobBinding ∉
    control.execution.application.config.history.map EventGraph.Completion.event at unfinished
  exact fun completed => unfinished
    ((control.execution.application.config.history_exact _).mpr completed)

open Classical in
/-- Every raw response has one eventual binding result throughout Bob's entire
information fiber. This includes rejection, prior replays, and timeout. -/
theorem native_committed_bob_binding_local
    (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (granted : view.application.publicView.serviceGrant = some bobBinding)
    (unfinished : bobBinding ∉ view.application.publicView.observation.completionOrder)
    (choice : nativeModel.Choice bob (some (past, view)))
    (first second : nativeModel.InformationHistory bob (some (past, view)))
    (firstFinal secondFinal : nativeArena.History)
    (firstMem : firstFinal ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) profile bob
        ((profile bob).commit (some (past, view)) choice)) (2 * nativeHorizon + 1) first.1).support)
    (secondMem : secondFinal ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) profile bob
        ((profile bob).commit (some (past, view)) choice))
          (2 * nativeHorizon + 1) second.1).support) :
    nativeBobBindingAt firstFinal.state = nativeBobBindingAt secondFinal.state := by
  obtain ⟨response, _, selected⟩ := choice.2
  obtain ⟨left, leftEq, leftActive, leftRecall, leftView⟩ := native_information_control bob
    past view first
  obtain ⟨right, rightEq, rightActive, rightRecall, rightView⟩ := native_information_control bob
    past view second
  rcases first with ⟨⟨leftState, leftTrace⟩, firstInfo⟩
  rcases second with ⟨⟨rightState, rightTrace⟩, secondInfo⟩
  change leftState = some left at leftEq
  change rightState = some right at rightEq
  subst leftState
  subst rightState
  let changed := Profile.update (sig := nativeModel.behavioralSignature) profile bob
    ((profile bob).commit (some (past, view)) choice)
  obtain ⟨leftGrant, leftUnfinished⟩ := native_bob_site_facts view left leftView granted unfinished
  obtain ⟨rightGrant, rightUnfinished⟩ :=
    native_bob_site_facts view right rightView granted unfinished
  obtain ⟨afterLeft, afterLeftMem, leftBound⟩ := native_bob_settlement_behavioral changed left
    leftTrace response leftActive leftGrant leftUnfinished
    (native_committed_response profile bob _ choice response selected _ _
      (congrArg some (Prod.ext leftRecall leftView))) firstFinal firstMem
  obtain ⟨afterRight, afterRightMem, rightBound⟩ := native_bob_settlement_behavioral changed right
    rightTrace response rightActive rightGrant rightUnfinished
    (native_committed_response profile bob _ choice response selected _ _
      (congrArg some (Prod.ext rightRecall rightView))) secondFinal secondMem
  have leftInput : (left.execution.recall bob, left.execution.observe nativeApp bob) =
      (past, view) := Prod.ext leftRecall leftView
  have rightInput : (right.execution.recall bob, right.execution.observe nativeApp bob) =
      (past, view) := Prod.ext rightRecall rightView
  have same := native_bob_binding_reserved_local left right leftTrace rightTrace leftActive
    rightActive (leftInput.trans rightInput.symm) leftGrant response _ afterLeft afterRight
    afterLeftMem afterRightMem
  rw [leftBound, rightBound, same]

def aliceBindingEvidence (bit : Bool) : EventGraph.CommitmentEvidence nativeGraph :=
  ⟨alice, .bool, aliceBindingRef, bit⟩

theorem native_observed_alice_binding (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) (bit : Bool)
    (observed : nativeRuntime.bindingEvidenceObserved nativeLeaks view (aliceBindingEvidence bit))
    (history : nativeModel.InformationHistory bob (some (past, view))) :
    ReactiveApplication.stateInvariant (fun state : State nativeGraph =>
      aliceBindingRef.get? state.config.store = some (.success bit)) history.1.state := by
  have known := nativeRuntime.knows_bindingEvidence_menu nativeLeaks nativeMenu
    (FinDist.pure nativeInputs) nativeHorizon nativeScheduler bob past view
    (aliceBindingEvidence bit) observed
  rw [FinDist.map_pure] at known
  exact known history

/-- A wrong or failed fixed guess cannot earn positive Bob utility, regardless
of anyone's later opening choice. -/
theorem native_bob_wrong_binding_bound (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (bit : Bool)
    (aliceStored : aliceBindingRef.get? control.execution.application.config.store =
      some (.success bit))
    (wrong : bobBindingRef.get? control.execution.application.config.store ≠
      some (.success bit)) :
    nativeUtility bob (some control) ≤ 0 := by
  have reachable := native_history_reachable control trace
  change utility (nativeResults control.execution.application.config) bob ≤ 0
  simp only [utility_bob, nativeResults]
  cases bobResult : bobPublicationRef.get? control.execution.application.config.store with
  | none => simp [correctness, openingPenalty]
  | some result =>
      cases result with
      | failure => simp [correctness, openingPenalty]
      | success guess =>
          have bound := native_publication_binding _ reachable bob guess bobResult
          have different : guess ≠ bit := by intro same; subst guess; exact wrong bound
          cases aliceResult :
              alicePublicationRef.get? control.execution.application.config.store with
          | none => simp [correctness, openingPenalty]
          | some result =>
              cases result with
              | failure => simp [correctness, openingPenalty]
              | success value =>
                  have valueBound := native_publication_binding _ reachable alice value aliceResult
                  have same : value = bit := by
                    change aliceBindingRef.get? _ = some (.success value) at valueBound
                    rw [aliceStored] at valueBound
                    cases Option.some.inj valueBound
                    rfl
                  subst value
                  simp [correctness, openingPenalty, Ne.symm different]

def bobCorrectiveChoice (bit : Bool) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) : nativeModel.Choice bob (some (past, view)) :=
  ⟨some (bobCorrectiveResponse bit view), bobCorrectiveResponse bit view,
    bob_corrective_response_available bit past view, rfl⟩

open Classical in
/-- The correction changes only the current response. Its binding guarantee
holds against the original arbitrary future strategy of every player. -/
theorem native_bob_corrective_binding
    (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some bobBinding)
    (unfinished : bobBinding ∉ view.application.publicView.observation.completionOrder)
    (history : nativeModel.InformationHistory bob (some (past, view)))
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) profile bob
        ((profile bob).commit (some (past, view)) (bobCorrectiveChoice bit past view)))
          (2 * nativeHorizon + 1) history.1).support) :
    nativeBobBindingAt final.state = some (.success bit) := by
  obtain ⟨control, stateEq, active, recall, observed⟩ := native_information_control bob
    past view history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  obtain ⟨grant, incomplete⟩ := native_bob_site_facts view control observed granted unfinished
  let changed := Profile.update (sig := nativeModel.behavioralSignature) profile bob
    ((profile bob).commit (some (past, view)) (bobCorrectiveChoice bit past view))
  obtain ⟨middle, middleMem, result⟩ := native_bob_settlement_behavioral changed control trace
    (bobCorrectiveResponse bit view) active grant incomplete
    (native_committed_response profile bob _ (bobCorrectiveChoice bit past view) _ rfl _ _
      (congrArg some (Prod.ext recall observed))) final supported
  rw [← observed] at middleMem
  obtain ⟨next, stored, realized⟩ := bob_corrective_response_realizes _ control trace active
    grant incomplete bit
  have mapped : middle.application ∈ (FinDist.pure next).support := by
    rw [← realized, FinDist.support_map]
    exact ⟨middle, middleMem, rfl⟩
  rw [result, FinDist.mem_support_pure.mp mapped, stored]
  rfl

end VegasTests.SelectiveAssociation
