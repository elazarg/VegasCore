/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeResolutionTail
import VegasTests.MonitoredGuessingNativeInitial
import VegasTests.MonitoredGuessingNativeOutcome
import VegasTests.MonitoredGuessingNativeUnfinished

/-! # Final native opening dominates every full continuation policy -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability

theorem resolution_final_position (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (granted : control.execution.application.serviceGrant = some alicePublication) :
    control.execution.environmentRecall.length = 10 ∧ control.remaining = 4 := by
  rcases native_alice_calendar control trace active with early | late
  · obtain ⟨bit, same⟩ := native_alice_initial_representation control trace active early.1
    subst control
    change none = some alicePublication at granted
    cases granted
  · exact late

/-- Once Bob's guess has settled, no later raw response can improve on a
truthful final opening or remove an earlier sanction. -/
theorem resolution_plan_alice_upper (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (players : Player → nativeApp.Policy) (plan : List (ServiceInstruction nativeGraph))
    (execution : nativeApp.Execution) (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit execution.application)
    (stored : bobPublicationRef.get? execution.application.config.store = some guess) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan execution).expect
      (nativeExecutionUtility deposit alice) ≤ correctness (.success bit) guess -
        if rejectedAlice execution.receipts then deposit else 0 := by
  apply FinDist.expect_le_of_forall
  intro final supported
  have fixed := resolution_plan_invariant players _ (native_fixed_invariant bit) plan
    execution final valid supported
  have bound := resolution_plan_invariant players _
    (nativeRuntime.reactiveStoreInvariant nativeLeaks (.inr bobPublication) guess) plan
    execution final stored supported
  have retained := native_plan_receipts_prefix players plan execution final supported
  exact resolution_execution_payoff_upper deposit nonnegative bit execution final fixed guess
    bound retained

theorem resolution_history_finish_dominates (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (profile : Profile nativeModel.behavioralSignature)
    (prescribed : profile alice = nativeAliceBehavior)
    (alternative : nativeModel.BehavioralPolicy alice)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (active : control.actor = some alice)
    (position : control.execution.environmentRecall.length = 10)
    (remaining : control.remaining = 4)
    (ready : control.execution.application.config.cut.Ready alicePublication)
    (timely : control.execution.application.WithinDeadline nativeRuntime alicePublication)
    (guess : PublicationResult Bool)
    (stored : bobPublicationRef.get? control.execution.application.config.store = some guess) :
    (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      (nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
        (Profile.update (sig := nativeModel.behavioralSignature) profile alice alternative))
      (some control)).expect (nativeUtility deposit alice) ≤
    (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      (nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
      (some control)).expect (nativeUtility deposit alice) := by
  obtain ⟨bit, fixed⟩ := native_history_fixed control trace
  have grant := native_alice_final_grant control trace active position
  have serials := nativeApp.serialsBeforeNext_history nativeScheduler nativeInitialLaw
    nativeHorizon (nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler trace)
  have opens : (nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
      alice (control.execution.recall alice) (control.execution.observe nativeApp alice) =
      FinDist.pure (nativeOpeningAction alicePublication aliceHandle bit) := by
    change (nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler alice (profile alice))) _ _ = _
    rw [prescribed, decode_native_alice]
    change FinDist.pure (nativeAliceResponse (control.execution.observe nativeApp alice)) = _
    rw [native_alice_response_eq bit control.execution fixed grant]
  have bounded := resolution_finish_alice_dominates deposit nonnegative
    (nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile)
    (nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
      (Profile.update (sig := nativeModel.behavioralSignature) profile alice alternative))
    control.execution bit guess fixed stored ready timely serials position opens
  have representation : control = ⟨4, some alice, control.execution⟩ := by
    cases control
    simp_all only
  simpa only [← representation] using bounded

theorem resolution_final_site_dominates (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (assessment : nativeModel.BehavioralAssessment)
    (prescribed : assessment.strategy alice = nativeAliceBehavior)
    (site : nativeModel.InformationSite alice)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (information : site.1 = some (past, view))
    (granted : view.application.publicView.serviceGrant = some alicePublication)
    (alternative : nativeModel.BehavioralPolicy alice) :
    (assessment.continuationContext site
      (fun history => nativeUtility deposit alice history.state)
        (2 * nativeHorizon + 1)).value alternative ≤
    (assessment.continuationContext site
      (fun history => nativeUtility deposit alice history.state)
        (2 * nativeHorizon + 1)).value (assessment.strategy alice) := by
  rw [nativeMenu.context_value_finish nativeInitialLaw nativeHorizon nativeScheduler,
    nativeMenu.context_value_finish nativeInitialLaw nativeHorizon nativeScheduler,
    Profile.update_eq_self]
  apply FinDist.expect_mono
  intro history _
  let typed : nativeModel.InformationHistory alice (some (past, view)) :=
    ⟨history.1, history.2.trans information⟩
  obtain ⟨control, stateEq, active, _, observed⟩ :=
    native_information_control alice past view typed
  have trace : nativeArena.Trace (some control) := stateEq ▸ history.1.trace
  have grant : control.execution.application.serviceGrant = some alicePublication := by
    have projected := congrArg (fun observation : nativeApp.PlayerView =>
      observation.application.publicView.serviceGrant) observed
    exact projected.trans granted
  have position := resolution_final_position control trace active grant
  obtain ⟨completed, ready, timely⟩ := native_alice_final_service control trace active grant
  have present := control.execution.application.config.output_available bobPublication
  have existsResult : ∃ guess, bobPublicationRef.get?
      control.execution.application.config.store = some guess := by
    have available : (bobPublicationRef.get?
        control.execution.application.config.store).isSome = true :=
      present.mpr completed
    exact Option.isSome_iff_exists.mp available
  obtain ⟨guess, stored⟩ := existsResult
  rw [stateEq]
  exact resolution_history_finish_dominates deposit nonnegative assessment.strategy prescribed
    alternative control trace active position.1 position.2 ready timely guess stored

end VegasTests.MonitoredGuessing
