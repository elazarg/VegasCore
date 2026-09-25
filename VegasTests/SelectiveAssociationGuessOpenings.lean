/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGuessIncentives
import VegasTests.SelectiveAssociationOpeningFuture
import VegasTests.SelectiveAssociationUnfinished

/-! # The unchanged equilibrium continuation opens both successful bindings

Bob may change his present binding response. At all subsequent decisions the
assessment's strategy is unchanged, and sequential rationality still forces
ordinary successful opening throughout each information fiber.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

private theorem native_acts_once : nativeModel.ActsOnceWhereItMatters :=
  nativeModel.actsOnceWhereItMatters_of_actsOnce
    (InformationModel.actsOnce_of_decisionInformationAntichain
      (nativeMenu.decisionInformationAntichain (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler))

theorem native_bob_future_opening (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (active : control.actor = some bob)
    (granted : control.execution.application.serviceGrant = some bobBinding)
    (later : nativeArena.History)
    (supported : later ∈ (nativeModel.runBehavioralFrom profile 43
      ⟨some control, trace⟩).support) :
    ∃ result, later.state = some result ∧ result.actor = some bob ∧
      result.execution.application.serviceGrant = some bobPublication := by
  rw [show 43 = 9 + (13 + 21) by decide, nativeModel.runBehavioralFrom_add] at supported
  obtain ⟨first, firstMem, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨firstControl, firstEq, firstActive, firstGrant⟩ := native_next_decision profile bobBinding
    alicePublication rfl control trace active granted first firstMem
  rcases first with ⟨firstState, firstTrace⟩
  change firstState = some firstControl at firstEq
  subst firstState
  rw [nativeModel.runBehavioralFrom_add] at rest
  obtain ⟨second, secondMem, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rest)
  obtain ⟨secondControl, secondEq, secondActive, secondGrant⟩ :=
    native_next_decision profile alicePublication carolPublication rfl firstControl firstTrace
      firstActive firstGrant second secondMem
  rcases second with ⟨secondState, secondTrace⟩
  change secondState = some secondControl at secondEq
  subst secondState
  exact native_next_decision profile carolPublication bobPublication rfl secondControl secondTrace
    secondActive secondGrant later rest

open Classical in
theorem native_bob_committed_alice_opens
    (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some bobBinding)
    (observed : nativeRuntime.bindingEvidenceObserved nativeLeaks view (aliceBindingEvidence bit))
    (choice : nativeModel.Choice bob (some (past, view)))
    (history : nativeModel.InformationHistory bob (some (past, view)))
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
        ((assessment.strategy bob).commit (some (past, view)) choice))
          (2 * nativeHorizon + 1) history.1).support) :
    nativePublicationAt alice final.state = some (.success bit) := by
  obtain ⟨control, stateEq, active, recall, viewEq⟩ :=
    native_information_control bob past view history
  have aliceStored := native_observed_alice_binding past view bit observed history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  have grant : control.execution.application.serviceGrant = some bobBinding := by
    rw [← viewEq] at granted
    exact granted
  have running : ¬nativeArena.terminal (some control) := by
    intro stopped
    have no : control.actor = none := stopped.2
    rw [active] at no
    cases no
  let changed := Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
    ((assessment.strategy bob).commit (some (past, view)) choice)
  have split := nativeModel.runBehavioralFrom_commit_split native_acts_once assessment.strategy
    bob (some (past, view)) choice ⟨some control, trace⟩ information active running 8 170
  change nativeModel.runBehavioralFrom changed (2 * nativeHorizon + 1) ⟨some control, trace⟩ =
    (nativeModel.runBehavioralFrom changed 9 ⟨some control, trace⟩).bind
      (nativeModel.runBehavioralFrom assessment.strategy 170) at split
  rw [split] at supported
  obtain ⟨opening, openingMem, tailMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨openingControl, openingEq, openingActive, openingGrant⟩ :=
    native_next_decision changed bobBinding alicePublication rfl control trace active grant
      opening openingMem
  obtain ⟨preservedControl, preservedEq, preserved⟩ :=
    (native_binding_invariant alice (.success bit)).behavioral_continuation nativeMenu
      (FinDist.pure nativeInitial) nativeHorizon nativeScheduler changed 9 control trace opening
      aliceStored openingMem
  have same : preservedControl = openingControl := Option.some.inj
    (preservedEq.symm.trans openingEq)
  subst preservedControl
  rcases opening with ⟨openingState, openingTrace⟩
  change openingState = some openingControl at openingEq
  subst openingState
  apply native_opening_exact_from_control assessment rational alice openingControl openingTrace
    openingActive openingGrant
    (native_decision_unfinished alicePublication openingControl openingTrace alice
      openingActive openingGrant) bit preserved 170 _ final tailMem
  have position := (native_decision_cursor alicePublication openingControl openingTrace alice
    openingActive openingGrant).2
  have accounted := (native_decision_predecessor alicePublication openingControl openingTrace
    openingActive position).1
  change openingControl.remaining + 22 + 1 = 89 at accounted
  change 2 * openingControl.remaining + (if openingControl.actor.isSome then 1 else 0) ≤ 170
  rw [openingActive]
  simp only [Option.isSome_some, ite_true]
  omega

open Classical in
theorem native_bob_committed_bob_opens
    (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some bobBinding)
    (choice : nativeModel.Choice bob (some (past, view)))
    (history : nativeModel.InformationHistory bob (some (past, view)))
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
        ((assessment.strategy bob).commit (some (past, view)) choice))
          (2 * nativeHorizon + 1) history.1).support)
    (bound : nativeBindingAt bob final.state = some (.success bit)) :
    nativePublicationAt bob final.state = some (.success bit) := by
  obtain ⟨control, stateEq, active, recall, viewEq⟩ :=
    native_information_control bob past view history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  have grant : control.execution.application.serviceGrant = some bobBinding := by
    rw [← viewEq] at granted
    exact granted
  have running : ¬nativeArena.terminal (some control) := by
    intro stopped
    have no : control.actor = none := stopped.2
    rw [active] at no
    cases no
  let changed := Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
    ((assessment.strategy bob).commit (some (past, view)) choice)
  have split := nativeModel.runBehavioralFrom_commit_split native_acts_once assessment.strategy
    bob (some (past, view)) choice ⟨some control, trace⟩ information active running 42 136
  change nativeModel.runBehavioralFrom changed (2 * nativeHorizon + 1) ⟨some control, trace⟩ =
    (nativeModel.runBehavioralFrom changed 43 ⟨some control, trace⟩).bind
      (nativeModel.runBehavioralFrom assessment.strategy 136) at split
  rw [split] at supported
  obtain ⟨opening, openingMem, tailMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨openingControl, openingEq, openingActive, openingGrant⟩ :=
    native_bob_future_opening changed control trace active grant opening openingMem
  rcases opening with ⟨openingState, openingTrace⟩
  change openingState = some openingControl at openingEq
  subst openingState
  cases finalEq : final.state with
  | none => simp only [nativeBindingAt, finalEq, Option.bind_none] at bound; cases bound
  | some result =>
      have stored := native_binding_at_opening_from_final assessment.strategy bob openingControl
        openingTrace openingActive openingGrant 136 final tailMem result finalEq bit
        (by simpa only [nativeBindingAt, finalEq, Option.bind_some] using bound)
      rw [← finalEq]
      apply native_opening_exact_from_control assessment rational bob openingControl openingTrace
        openingActive openingGrant
        (native_decision_unfinished bobPublication openingControl openingTrace bob
          openingActive openingGrant) bit stored 136 _ final tailMem
      have position := (native_decision_cursor bobPublication openingControl openingTrace bob
        openingActive openingGrant).2
      have accounted := (native_decision_predecessor bobPublication openingControl openingTrace
        openingActive position).1
      change openingControl.remaining + 54 + 1 = 89 at accounted
      change 2 * openingControl.remaining + (if openingControl.actor.isSome then 1 else 0) ≤ 136
      rw [openingActive]
      simp only [Option.isSome_some, ite_true]
      omega

open Classical in
/-- Correcting the guess earns utility one under the unchanged target
continuation. Both openings follow from sequential rationality at their later
information sets; they are not prescribed as part of Bob's deviation. -/
theorem native_bob_corrective_utility
    (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some bobBinding)
    (unfinished : bobBinding ∉ view.application.publicView.observation.completionOrder)
    (observed : nativeRuntime.bindingEvidenceObserved nativeLeaks view (aliceBindingEvidence bit))
    (history : nativeModel.InformationHistory bob (some (past, view)))
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom
      (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
        ((assessment.strategy bob).commit (some (past, view))
          (bobCorrectiveChoice bit past view))) (2 * nativeHorizon + 1) history.1).support) :
    nativeUtility bob final.state = 1 := by
  have binding := native_bob_corrective_binding assessment.strategy past view bit granted
    unfinished history final supported
  have aliceOpens := native_bob_committed_alice_opens assessment rational past view bit granted
    observed (bobCorrectiveChoice bit past view) history final supported
  have bobOpens := native_bob_committed_bob_opens assessment rational past view bit granted
    (bobCorrectiveChoice bit past view) history final supported binding
  cases finalEq : final.state with
  | none =>
      simp only [nativePublicationAt, finalEq, Option.bind_none] at aliceOpens
      cases aliceOpens
  | some result =>
      simp only [nativePublicationAt, finalEq, Option.bind_some] at aliceOpens bobOpens
      change alicePublicationRef.get? result.execution.application.config.store = _ at aliceOpens
      change bobPublicationRef.get? result.execution.application.config.store = _ at bobOpens
      change utility (nativeResults result.execution.application.config) bob = 1
      apply (utility_bob_eq_one_iff _).mpr
      exact ⟨bit, by simp only [nativeResults, aliceOpens, Option.getD_some],
        by simp only [nativeResults, bobOpens, Option.getD_some]⟩

end VegasTests.SelectiveAssociation
