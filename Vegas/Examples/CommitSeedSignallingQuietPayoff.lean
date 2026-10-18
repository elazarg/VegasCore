/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingProperPayoff
import Vegas.Examples.CommitSeedSignallingBobQuietInitialization

/-! # A positive whole deviation at the actual quiet information set -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- Waiting and then using the proper late policy earns at least one quarter
at Bob's actual quiet information set, against the assessed Alice continuation.
The bound also holds when this information set has zero equilibrium reach. -/
theorem bobQuiet_fixedLate_context_quarter
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    (1 / 4 : ℝ) ≤ (assessment.continuationContext canonicalCertificate bobQuietSite
      (rawPayoff bob)).value (fixedLateContinuation bob) := by
  rw [bobQuiet_fixedLate_context_initialized_value assessment equilibrium]
  let profile := Function.update (countedAssessmentProfile assessment) bob
    (countedMenu.restrictPolicy initial horizon scheduler bob (fixedLatePolicy bob))
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  have selected : players bob = fixedLatePolicy bob := by
    change app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler bob
      ((Function.update (countedAssessmentProfile assessment) bob
        (countedMenu.restrictPolicy initial horizon scheduler bob (fixedLatePolicy bob))) bob)) = _
    rw [Function.update_self]
    exact countedMenu.decode_restrictPolicy_of_covered initial horizon scheduler bob _
      (fixedLatePolicy_counted bob)
  have bobSelected : countedMenu.decodeProfile initial horizon scheduler
      (quietAliceCountedProfile profile) bob = fixedLatePolicy bob := by
    rw [decode_quietAliceCountedProfile, quietAlicePlayers_bob]
    exact selected
  apply initialized_fixed_late_netPayoff_quarter (quietAliceCountedProfile profile) bob
    bobSelected
  · rw [decode_quietAliceCountedProfile]
    exact quietAlicePlayers_aliceFirst players
  · rw [bobSelected]
    exact fixedLatePolicy_bobQuiet

end Vegas.Examples.CommitSeedSignalling
