/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryDebtUniformity

/-! # Owing agents are indifferent among actual recovery continuations

Uniform source debt and completion of the actual recovery runtime imply zero
whole-policy and local-law gain for any assessment belief. The result directly
supplies the owing-agent obligation of a recovery pooled certificate.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "N" => model setup leaks bounds Initial horizon scheduler
local notation "menu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- Every whole-policy deviation of an owing agent has zero actual recovery
gain, under any assessment at that information site. -/
theorem owingAgent_gain_eq_zero [recoveryHistoryFintype : Fintype (E).History]
    [recoveryInfoDecidable : ∀ who,
      DecidableEq ((model setup leaks bounds Initial horizon scheduler).InfoState who)]
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (certificate : (E).WellFoundedHistories)
    (assessment : (N).BehavioralAssessment) {who : Player}
    (deviation : (N).AssessmentDeviation who)
    (owing : OwingAgent setup leaks bounds Initial horizon scheduler ((N).agentAt deviation.1)) :
    expect ((N).assessmentComparisonWith ((N).runBehavioralTerminalFrom certificate)
      (fun final => final.state) assessment who deviation).alternative
        (fun state => recoveryExclusionBase parameter utility excludedPayoff state who) -
      expect ((N).assessmentComparisonWith ((N).runBehavioralTerminalFrom certificate)
        (fun final => final.state) assessment who deviation).prescribed
        (fun state => recoveryExclusionBase parameter utility excludedPayoff state who) = 0 := by
  exact recovery_gain_eq_zero_of_owes parameter utility excludedPayoff (menu) Initial horizon
    scheduler certificate completes assessment deviation
    (fun history _supported => Or.inr (owingAgent_allHistories setup leaks bounds horizon scheduler
      (failureProfile setup.program) deviation.1 owing history))

/-- At an owing site every whole continuation policy has exactly the assessed
continuation value. -/
theorem owingAgent_value_eq [recoveryHistoryFintype : Fintype (E).History]
    [recoveryInfoDecidable : ∀ who,
      DecidableEq ((model setup leaks bounds Initial horizon scheduler).InfoState who)]
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (certificate : (E).WellFoundedHistories)
    (assessment : (N).BehavioralAssessment) {who : Player} (site : (N).InformationSite who)
    (owing : OwingAgent setup leaks bounds Initial horizon scheduler ((N).agentAt site))
    (alternative : (N).BehavioralPolicy who) :
    (assessment.continuationContext certificate site
        (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state who)).value
        alternative =
      (assessment.continuationContext certificate site
        (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state who)).value
        (assessment.strategy who) := by
  apply sub_eq_zero.mp
  have zero := owingAgent_gain_eq_zero setup leaks bounds horizon scheduler parameter utility
    excludedPayoff completes certificate assessment (site, alternative) owing
  simpa only [BehavioralAssessment.continuationContext_value,
    InformationModel.assessmentComparisonWith, InformationModel.assessmentLawWith, expect_map,
    Function.comp_def]
    using zero

/-- The truncated local-law gain of any owing agent is exactly zero. -/
theorem owingAgent_localGain_eq_zero [recoveryHistoryFintype : Fintype (E).History]
    [recoveryInfoDecidable : ∀ who,
      DecidableEq ((model setup leaks bounds Initial horizon scheduler).InfoState who)]
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (assessment : (N).BehavioralAssessment) {who : Player}
    (site : (N).InformationSite who)
    (owing : OwingAgent setup leaks bounds Initial horizon scheduler ((N).agentAt site))
    (law : PMF ((N).Choice who site.1)) :
    localGain (2 * horizon + 1) (fun final => final.state)
      (recoveryExclusionBase parameter utility excludedPayoff) assessment site law = 0 := by
  rw [localGain_eq_sub]
  simp only [localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
    (recoveryExclusionBase parameter utility excludedPayoff) assessment site
    ((menu).bounded Initial horizon scheduler), BehavioralPolicy.withLaw_eq_self]
  exact sub_eq_zero.mpr (owingAgent_value_eq setup leaks bounds horizon scheduler parameter utility
    excludedPayoff completes ((menu).bounded Initial horizon scheduler).wellFoundedHistories
    assessment site owing ((assessment.strategy who).withLaw site.1 law))

end Vegas.RecoveryOnePacket
