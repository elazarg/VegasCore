/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationInitialEvaluation
import VegasTests.SelectiveAssociationInitialSite
import VegasTests.SelectiveAssociationNativeSequentialDeviation

/-! # Sequential rationality bounds Alice's initialized native value

Alice's first information set contains a single concrete control state. Its
continuation comparison is therefore exactly the initialized game comparison,
for every belief. The selective-disclosure deviation gives at least one half.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem native_initial_context_value (assessment : nativeModel.BehavioralAssessment)
    (alternative : nativeModel.BehavioralPolicy alice) :
    (assessment.continuationContext nativeInitialSite
      (fun history => nativeUtility alice history.state) (2 * nativeHorizon + 1)).value
        alternative =
      (nativeApp.runRounds nativeScheduler
        (nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
          (Profile.update (sig := nativeModel.behavioralSignature)
            assessment.strategy alice alternative)) nativeHorizon nativeRoot).expect
              (fun final => utility (nativeResults final.application.config) alice) := by
  rw [nativeMenu.context_value_of_known_state (FinDist.pure nativeInitial) nativeHorizon
    nativeScheduler assessment alice nativeInitialSite (nativeUtility alice) alternative
      (some nativeInitialControl) native_initial_information_control]
  exact native_initial_finish_value _

theorem native_sequential_initial_bound (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1)) :
    1 / 2 ≤ (nativeModel.runBehavioral assessment.strategy (2 * nativeHorizon + 1)).expect
      (fun history => nativeUtility alice history.state) := by
  have optimal := rational alice nativeInitialSite nativeAliceBehavior (Set.mem_univ _)
  change (assessment.continuationContext nativeInitialSite
    (fun history => nativeUtility alice history.state) (2 * nativeHorizon + 1)).value
      nativeAliceBehavior ≤
    (assessment.continuationContext nativeInitialSite
      (fun history => nativeUtility alice history.state) (2 * nativeHorizon + 1)).value
        (assessment.strategy alice) at optimal
  rw [native_initial_context_value, native_initial_context_value,
    native_decode_alice_deviation, Profile.update_eq_self] at optimal
  rw [native_initial_value]
  exact (native_sequential_deviation_gain assessment rational).trans optimal

end VegasTests.SelectiveAssociation
