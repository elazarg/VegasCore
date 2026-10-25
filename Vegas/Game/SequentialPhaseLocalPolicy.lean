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
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "P" => phaseApplication (runtime setup) leaks
local notation "A" => recoveryApplication (runtime setup) (recoveryLeaks setup leaks)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "oldMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "rawModel" => ReactiveApplication.information (A) (oldInitial) horizon (oldScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks oldLeaks
local notation "decode" => SequentialPhasePlayerInformation.information setup.program
  (runtime setup) leaks (oldLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

private theorem withLaw_at_input
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1)
    (phasePolicy : (M).BehavioralPolicy agent.1)
    (oldPolicy : (R).BehavioralPolicy agent.1)
    (law : PMF ((M).Choice agent.1 agent.2.1)) (info : (A).Info)
    (roundtrip : PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)
      (decode info) = info)
    (baseline : (oldMenu).embedPolicy (oldInitial) horizon (oldScheduler) agent.1 oldPolicy info =
      SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program (runtime setup) leaks
        (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler
        agent.1 phasePolicy info) :
    (oldMenu).embedPolicy (oldInitial) horizon (oldScheduler) agent.1
        (oldPolicy.withLaw
          (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1)
          (law.map (choiceEquiv setup leaks bounds horizon scheduler agent clear))) info =
      SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program (runtime setup) leaks
        (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler
        agent.1 (phasePolicy.withLaw agent.2.1 law) info := by
  classical
  apply pmf_map_injective Subtype.val_injective
  rw [SequentialPhaseRecoveryPolicy.behavioralPolicy_map_val]
  by_cases same : info =
      PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1
  · subst info
    erw [decoded_projected_input setup leaks bounds horizon scheduler agent clear,
      BehavioralPolicy.withLaw_self]
    simp only [ReactiveApplication.ResponseMenu.embedPolicy, BehavioralPolicy.withLaw_self,
      PMF.map_comp]
    rfl
  · have decodedNe : decode info ≠ agent.2.1 := by
      intro equal
      apply same
      exact roundtrip.symm.trans (congrArg
        (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)) equal)
    rw [BehavioralPolicy.withLaw_of_ne _ _ _ decodedNe]
    have mapped := congrArg (PMF.map Subtype.val) baseline
    rw [SequentialPhaseRecoveryPolicy.behavioralPolicy_map_val] at mapped
    simp only [ReactiveApplication.ResponseMenu.embedPolicy]
    have unchanged := BehavioralPolicy.withLaw_of_ne oldPolicy
      (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1)
      (law.map (choiceEquiv setup leaks bounds horizon scheduler agent clear)) (other := info) same
    erw [unchanged]
    exact mapped

/-- A local law replacement and its actual menu equivalence have identical
callbacks at every matched clear initialized physical state. -/
theorem comparisonPolicy_withLaw_history
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (siteClear : ClearInput setup leaks agent.2.1)
    (law : PMF ((M).Choice agent.1 agent.2.1))
    (phase : ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).History)
    (old : ((oldMenu).protocol (oldInitial) horizon (oldScheduler)).History)
    (same : projection phase.state = old.state)
    (clear : ReactiveApplication.stateInvariant
      (fun state : PhaseRuntimeState (graph setup) => state.current.excluded = ∅) phase.state) :
    (oldMenu).embedPolicy (oldInitial) horizon (oldScheduler) agent.1
      ((recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights agent.1).withLaw
          (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1)
          (law.map (choiceEquiv setup leaks bounds horizon scheduler agent siteClear)))
      ((A).observe agent.1 old.state) =
    SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program (runtime setup) leaks
      (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler agent.1
      ((componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
        le_one weights agent.1).withLaw agent.2.1 law) ((A).observe agent.1 old.state) := by
  apply withLaw_at_input setup leaks bounds horizon scheduler agent siteClear
  · have observed : (A).observe agent.1 old.state =
        PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)
          ((P).observe agent.1 phase.state) := by
      rw [← same]
      exact PhaseRecoveryProjection.observe_state (runtime setup) leaks (oldLeaks)
        agent.1 phase.state
    have decoded : decode ((A).observe agent.1 old.state) =
        (P).observe agent.1 phase.state := by
      rw [observed]
      cases stateEq : phase.state with
      | none => rfl
      | some control =>
        exact SequentialPhasePlayerInformation.information_history setup.program (runtime setup)
          leaks (oldLeaks) bounds (setup.initialLaw.map setup.eventInputs) horizon scheduler
          (PhaseCount.normalized_onePacket_included (runtime setup) leaks bounds |>.trace
            (initialLaw setup) horizon scheduler (stateEq ▸ phase.trace))
          (by rwa [stateEq] at clear) agent.1
    rw [decoded, ← observed]
  · apply comparisonPolicy_history setup leaks bounds horizon scheduler fallback assessment scale
      nonnegative le_one weights old
    rw [← same]
    cases stateEq : phase.state <;> rw [stateEq] at clear <;> exact clear

end Vegas.SequentialPhase
