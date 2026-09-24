/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationInitialEvaluation
import VegasTests.SelectiveAssociationInitialSite
import VegasTests.SelectiveAssociationNativeSequentialDeviation
import GameTheoryExtensions.Analysis.Protocol.InducedInformation

/-! # Sequential rationality bounds Alice's initialized native value

Alice's first information set contains a single concrete control state. Its
continuation comparison is therefore exactly the initialized game comparison,
for every belief. The selective-disclosure deviation gives at least one half.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem native_initial_history_value (profile : Profile nativeModel.behavioralSignature)
    (history : nativeModel.InformationHistory alice nativeInitialSite.1) :
    (nativeModel.runBehavioralFrom profile (2 * nativeHorizon + 1) history.1).expect
      (fun history => nativeUtility alice history.state) =
    (nativeModel.runBehavioral profile (2 * nativeHorizon + 1)).expect
      (fun history => nativeUtility alice history.state) := by
  have enough : nativeApp.rank nativeHorizon history.1.state ≤ 2 * nativeHorizon + 1 := by
    rw [native_initial_information_control history]
    decide
  have law := nativeMenu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
    profile (2 * nativeHorizon + 1) history.1 enough
  have value := congrArg (fun law : FinDist nativeApp.ProtocolState =>
    law.expect (nativeUtility alice)) law
  rw [FinDist.expect_map, native_initial_information_control history] at value
  rw [value, native_initial_value]
  exact native_initial_finish_value _

theorem native_sequential_initial_bound (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1)) :
    1 / 2 ≤ (nativeModel.runBehavioral assessment.strategy (2 * nativeHorizon + 1)).expect
      (fun history => nativeUtility alice history.state) := by
  apply nativeModel.initial_value_ge_of_induced_deviation assessment
    (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1)
      rational alice nativeInitialSite native_initial_history_value nativeAliceBehavior
  rw [native_initial_value, native_decode_alice_deviation]
  exact native_sequential_deviation_gain assessment rational

end VegasTests.SelectiveAssociation
