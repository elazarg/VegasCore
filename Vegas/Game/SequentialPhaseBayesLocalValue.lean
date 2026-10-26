/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseLocalBayesValueBound
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Local values of actual Bayesian phase assessments -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "P" => phaseApplication runtime leaks
local notation "A" => recoveryApplication runtime (recoveryLeaks setup leaks)
local notation "M" => model setup runtime leaks bounds horizon scheduler
local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds
local notation "rawModel" => ReactiveApplication.information (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "RecoveryProtocol" => ReactiveApplication.ResponseMenu.protocol (RecoveryMenu)
    (RecoveryPrior)
  horizon (RecoveryScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState runtime leaks
    RecoveryLeaks
local notation "projectInfo" => PhaseRecoveryProjection.information runtime leaks
    RecoveryLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "RecoveryClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

/-- The existing local value is exactly the actual Bayesian average of original
whole phase continuations under the chosen focal law. -/
theorem phase_localValue_eq_bayes_terminal_expect
    (assessment : (M).BehavioralAssessment)
    (bayes : BehavioralAssessment.IsBayesConsistent (M) assessment
      ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
        horizon
          scheduler))
    (payoff : (P).ProtocolState → Player → ℝ)
    (who : Player) (site : (M).InformationSite who)
    (positive : 0 < (M).informationMass assessment.strategy who site)
    (law : PMF ((M).Choice who site.1)) :
    localValue (2 * horizon + 1) (fun final => final.state) payoff assessment site law =
      expect ((M).bayesBelief assessment.strategy who site
        ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
          horizon
            scheduler
          who site) positive)
        (fun history => expect ((M).runBehavioralTerminalFrom
          ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon
            scheduler).wellFoundedHistories
          (Profile.update (sig := (M).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 law)) history.1)
          (fun final => payoff final.state who)) := by
  rw [localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
    payoff assessment site ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup)
      horizon
        scheduler),
    BehavioralAssessment.continuationContext_value, expect_bind_of_finite]
  rw [(BehavioralAssessment.isBayesConsistentAt_iff (M) assessment who site
    ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup) horizon
        scheduler
      who site) positive).mp (bayes who site positive)]

end Vegas.SequentialPhase
