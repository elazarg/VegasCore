/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonPolicy

/-! # Local law replacements respect clear phase information -/

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
local notation "projection" => PhaseRecoveryProjection.protocolState runtime leaks
    RecoveryLeaks
local notation "decode" => SequentialPhasePlayerInformation.information setup.program
  runtime leaks (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

private theorem withLaw_at_input
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup runtime leaks agent.2.1)
    (phasePolicy : (M).BehavioralPolicy agent.1)
    (recoveryPolicy : (R).BehavioralPolicy agent.1)
    (law : PMF ((M).Choice agent.1 agent.2.1)) (info : (A).Info)
    (roundtrip : PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks)
      (decode info) = info)
    (baseline : (RecoveryMenu).embedPolicy (RecoveryPrior) horizon (RecoveryScheduler) agent.1
        recoveryPolicy info =
      SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program runtime leaks
        (menu setup runtime leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler
        agent.1 phasePolicy info) :
    (RecoveryMenu).embedPolicy (RecoveryPrior) horizon (RecoveryScheduler) agent.1
        (recoveryPolicy.withLaw
          (PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks) agent.2.1)
          (law.map (choiceEquiv setup runtime leaks bounds horizon scheduler agent clear))) info =
      SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program runtime leaks
        (menu setup runtime leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler
        agent.1 (phasePolicy.withLaw agent.2.1 law) info := by
  classical
  apply pmf_map_injective Subtype.val_injective
  rw [SequentialPhaseRecoveryPolicy.behavioralPolicy_map_val]
  by_cases same : info =
      PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks) agent.2.1
  · subst info
    erw [decoded_projected_input setup runtime leaks bounds horizon scheduler agent clear,
      BehavioralPolicy.withLaw_self]
    simp only [ReactiveApplication.ResponseMenu.embedPolicy, BehavioralPolicy.withLaw_self,
      PMF.map_comp]
    rfl
  · have decodedNe : decode info ≠ agent.2.1 := by
      intro equal
      apply same
      exact roundtrip.symm.trans (congrArg
        (PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks)) equal)
    rw [BehavioralPolicy.withLaw_of_ne _ _ _ decodedNe]
    have mapped := congrArg (PMF.map Subtype.val) baseline
    rw [SequentialPhaseRecoveryPolicy.behavioralPolicy_map_val] at mapped
    simp only [ReactiveApplication.ResponseMenu.embedPolicy]
    have unchanged := BehavioralPolicy.withLaw_of_ne recoveryPolicy
      (PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks) agent.2.1)
      (law.map (choiceEquiv setup runtime leaks bounds horizon scheduler agent clear)) (other :=
        info) same
    erw [unchanged]
    exact mapped

/-- A local law replacement and its actual menu equivalence have identical
callbacks at every matched clear initialized physical state. -/
theorem comparisonPolicy_withLaw_history
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (siteClear : ClearInput setup runtime leaks agent.2.1)
    (law : PMF ((M).Choice agent.1 agent.2.1))
    (phase : ((menu setup runtime leaks bounds).protocol (phaseInitialLaw setup) horizon
      scheduler).History)
    (recoveryHistory : ((RecoveryMenu).protocol (RecoveryPrior) horizon
        (RecoveryScheduler)).History)
    (same : projection phase.state = recoveryHistory.state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : PhaseRuntimeState (graph setup) => state.current.excluded = ∅) phase.state) :
    (RecoveryMenu).embedPolicy (RecoveryPrior) horizon (RecoveryScheduler) agent.1
      ((recoveryComparisonStrategy setup runtime leaks bounds horizon scheduler assessment scale
        nonnegative
        le_one weights agent.1).withLaw
          (PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks) agent.2.1)
          (law.map (choiceEquiv setup runtime leaks bounds horizon scheduler agent siteClear)))
      ((A).observe agent.1 recoveryHistory.state) =
    SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program runtime leaks
      (menu setup runtime leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler
        agent.1
      ((componentStrategy setup runtime leaks bounds horizon scheduler fallback assessment scale
        nonnegative
        le_one weights agent.1).withLaw agent.2.1 law) ((A).observe agent.1 recoveryHistory.state)
            := by
  apply withLaw_at_input setup runtime leaks bounds horizon scheduler agent siteClear
  · have observed : (A).observe agent.1 recoveryHistory.state =
        PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks)
          ((P).observe agent.1 phase.state) := by
      rw [← same]
      exact PhaseRecoveryProjection.observe_state runtime leaks (RecoveryLeaks)
        agent.1 phase.state
    have decoded : decode ((A).observe agent.1 recoveryHistory.state) =
        (P).observe agent.1 phase.state := by
      rw [observed]
      cases stateEq : phase.state with
      | none => rfl
      | some control =>
        exact SequentialPhasePlayerInformation.information_history setup.program runtime
          leaks (RecoveryLeaks) bounds (setup.initialLaw.map setup.eventInputs) horizon scheduler
          (PhaseCount.normalized_onePacket_included runtime leaks bounds |>.trace
            (phaseInitialLaw setup) horizon scheduler (stateEq ▸ phase.trace))
          (by rwa [stateEq] at clear) agent.1
    rw [decoded, ← observed]
  · apply comparisonPolicy_history setup runtime leaks bounds horizon scheduler fallback
      assessment scale
      nonnegative le_one weights recoveryHistory
    rw [← same]
    cases stateEq : phase.state <;> rw [stateEq] at clear <;> exact clear

end Vegas.SequentialPhase
