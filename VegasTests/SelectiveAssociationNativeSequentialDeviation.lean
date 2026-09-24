/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationNativeDeviationCompletion

/-! # The selective-disclosure deviation gains at least one half

The opponent assessment is sequentially rational at every legal information
set. Its supported local Bob responses therefore bind and publish the certified
bit even under Alice's changed continuation. Alice's opening is her own ordinary
choice. Carol's common guess law bounds her correctness by one half.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open ReactiveAssociationEvidence

theorem native_deviation_publications (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (bit : Bool) (result : Results)
    (supported : result ∈ (nativeDeviationOutcomes (nativeMenu.decodeProfile
      (FinDist.pure nativeInitial) nativeHorizon nativeScheduler assessment.strategy)
        bit).support) :
    result.alice = .success bit ∧ result.bob = .success bit := by
  let opponents := nativeMenu.decodeProfile (FinDist.pure nativeInitial)
    nativeHorizon nativeScheduler assessment.strategy
  let players := nativeAliceProfile opponents
  obtain ⟨settled, settledMem, finished⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨prior, priorMem, carolMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ settledMem)
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ finished
  have global := native_deviation_settled_global opponents bit prior priorMem settled carolMem
  have aliceStored := native_carol_settlement_alice players bit prior settled carolMem
  have alicePublished := native_alice_deviation_opening assessment.strategy bit settled final
    global aliceStored finalMem
  have evidence := native_carol_settlement_evidence players bit prior settled carolMem
  have continuation : final ∈
      (nativeApp.runRounds nativeScheduler players (3 + 73) settled).support := finalMem
  rw [ReactiveApplication.runRounds_add] at continuation
  obtain ⟨bound, boundMem, restMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ continuation)
  have bobStored := native_deviation_bob_binding assessment rational bit settled bound global
    evidence boundMem
  have boundGlobal := native_run_support_append players 13 3 settled bound global boundMem
  have bobPublished := native_deviation_bob_opening assessment rational bit bound final
    boundGlobal bobStored restMem
  exact ⟨by simp only [nativeResults, alicePublished, Option.getD_some],
    by simp only [nativeResults, bobPublished, Option.getD_some]⟩

/-- This lower bound is for the actual finite native game, with all bounded
raw responses, passive leaks, optional ordinary openings, and the original
public-result utility. It needs sequential rationality, without consistency. -/
theorem native_sequential_deviation_gain (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1)) :
    1 / 2 ≤ (nativeApp.runRounds nativeScheduler
      (nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler assessment.strategy)) nativeHorizon nativeRoot).expect
          (fun final => utility (nativeResults final.application.config) alice) := by
  apply native_deviation_advantage
  · intro bit result supported
    exact (native_deviation_publications assessment rational bit result supported).1
  · intro bit result supported
    exact (native_deviation_publications assessment rational bit result supported).2

end VegasTests.SelectiveAssociation
