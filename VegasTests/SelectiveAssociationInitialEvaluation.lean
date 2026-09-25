/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationNativeDeviation
import Interaction.ReactiveAssessmentEvaluation
import Interaction.ReactiveMenuPolicy

/-! # Native evaluation from Alice's first response -/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol ReactiveAssociationEvidence

theorem native_initial_finish (players : Player → nativeApp.Policy) :
    nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler players
      (some ⟨88, some alice, activatedInitial⟩) =
        (nativeApp.runRounds nativeScheduler players nativeHorizon nativeRoot).map
          nativeApp.finished := by
  have firstRound : nativeApp.runRounds nativeScheduler players 1 nativeRoot =
      nativeApp.invoke players alice activatedInitial := by
    change (serviceApp nativeLeaks).runRounds (serviceScheduler nativeLeaks) players
      ([.player alice] : List (ServiceInstruction nativeGraph)).length nativeRoot = _
    rw [native_prefix_rounds players [.player alice] nativePlan.tail rfl]
    simp only [runInteractionPlan, interactionStep, interactionInstruction,
      FinDist.pure_bind, FinDist.bind_pure, ReactiveApplication.dispatch]
    rw [show nativeRoot.environmentStep nativeApp (.activate alice) =
      FinDist.pure activatedInitial from initial_activation, FinDist.pure_bind]
    rfl
  change _ = (nativeApp.runRounds nativeScheduler players (1 + 88) nativeRoot).map _
  rw [ReactiveApplication.runRounds_add, firstRound, FinDist.map_bind]
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, FinDist.map_bind]

theorem native_initial_finish_value (players : Player → nativeApp.Policy) :
    (nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler players
      (some ⟨88, some alice, activatedInitial⟩)).expect (nativeUtility alice) =
        (nativeApp.runRounds nativeScheduler players nativeHorizon nativeRoot).expect
          (fun final => utility (nativeResults final.application.config) alice) := by
  rw [native_initial_finish, FinDist.expect_map]
  rfl

theorem native_initial_value
    {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}
    (profile : Profile (serviceModel observation).behavioralSignature) :
    ((serviceModel observation).runBehavioral profile (2 * nativeHorizon + 1)).expect
      (fun history => nativeUtility alice history.state) =
        ((serviceApp observation).runRounds (serviceScheduler observation)
          ((serviceMenu observation).decodeProfile (FinDist.pure nativeInitial) nativeHorizon
      (serviceScheduler observation)
            profile) nativeHorizon nativeRoot).expect
              (fun final => utility (nativeResults final.application.config) alice) := by
  have law := (serviceMenu observation).run_eq_finish (FinDist.pure nativeInitial) nativeHorizon
      (serviceScheduler observation)
    profile (2 * nativeHorizon + 1) (serviceArena observation).initHistory (by exact le_rfl)
  have value := congrArg (fun law : FinDist (serviceApp observation).ProtocolState =>
    law.expect (nativeUtility alice)) law
  rw [FinDist.expect_map] at value
  change ((serviceModel observation).runBehavioral profile (2 * nativeHorizon + 1)).expect
    (fun history => nativeUtility alice history.state) = _ at value
  rw [value]
  change ((serviceApp observation).finish (FinDist.pure nativeInitial) nativeHorizon
      (serviceScheduler observation)
    ((serviceMenu observation).decodeProfile (FinDist.pure nativeInitial) nativeHorizon
      (serviceScheduler observation) profile)
      none).expect (nativeUtility alice) = _
  simp only [ReactiveApplication.finish, FinDist.pure_bind, FinDist.expect_map]
  rfl

theorem native_decode_alice_deviation (profile : Profile nativeModel.behavioralSignature) :
    nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
        (Profile.update (sig := nativeModel.behavioralSignature)
          profile alice nativeAliceBehavior) =
      nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler profile) := by
  rw [nativeMenu.decodeProfile_update]
  apply congrArg (Function.update _ alice)
  exact nativeMenu.decode_restrictPolicy_of_covered (FinDist.pure nativeInitial)
    nativeHorizon nativeScheduler alice nativeAlicePolicy native_alice_admissible
      native_alice_available

theorem native_initial_result_law (profile : Profile nativeModel.behavioralSignature) :
    (nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map
        (fun history => history.state.elim (⟨.failure, .failure, .failure⟩ : Results)
          (fun control => nativeResults control.execution.application.config)) =
      (nativeApp.runRounds nativeScheduler
        (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
          nativeHorizon nativeScheduler profile)
          nativeHorizon nativeRoot).map
            (fun final => nativeResults final.application.config) := by
  have law := nativeMenu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
    profile (2 * nativeHorizon + 1) nativeArena.initHistory (by exact le_rfl)
  have projected := congrArg (fun law : FinDist nativeApp.ProtocolState => law.map
    (fun state => state.elim (⟨.failure, .failure, .failure⟩ : Results)
      (fun control => nativeResults control.execution.application.config))) law
  rw [FinDist.map_comp] at projected
  change (nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).map _ =
    (nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
      (nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon nativeScheduler profile)
        none).map _ at projected
  erw [projected]
  simp only [ReactiveApplication.finish, FinDist.pure_bind, FinDist.map_comp]
  rfl

end VegasTests.SelectiveAssociation
