/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseRecoveryComparison
import Vegas.Game.SequentialPhaseRecoveryPolicy
import Vegas.Game.SequentialPhaseClearLift

/-! # Actual recovery comparison policies at clear physical callbacks -/

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
  [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "P" => phaseApplication (runtime setup) leaks
local notation "A" => recoveryApplication (runtime setup) (recoveryLeaks setup leaks)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup leaks scheduler
local notation "RecoveryMenu" => Recovery.onePacketMenu (runtime setup) (RecoveryLeaks) bounds
local notation "rawModel" => ReactiveApplication.information (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks
    RecoveryLeaks
local notation "decode" => SequentialPhasePlayerInformation.information setup.program
  (runtime setup) leaks (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

/-- Assemble the actual phase component mixtures at every played input. -/
def componentStrategy
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) :
    ∀ who, (M).BehavioralPolicy who :=
  (M).agentBehavior (M).playedInformation fallback fun agent =>
    (weights (pool setup leaks bounds horizon scheduler agent)).bind
      (component setup leaks bounds horizon scheduler assessment scale nonnegative le_one agent)

/-- At every clear played phase input, the actual recovery comparison's embedded
raw policy is exactly the pure player-information decoding of the phase mixture. -/
theorem comparisonPolicy_at_projected_clear
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    (RecoveryMenu).embedPolicy (RecoveryPrior) horizon (RecoveryScheduler) agent.1
      (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights agent.1)
      (projectedAgent setup leaks bounds horizon scheduler agent clear).2.1 =
    SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program (runtime setup) leaks
      (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler agent.1
      (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
        le_one weights agent.1)
      (projectedAgent setup leaks bounds horizon scheduler agent clear).2.1 := by
  classical
  apply pmf_map_injective Subtype.val_injective
  rw [SequentialPhaseRecoveryPolicy.behavioralPolicy_map_val]
  change ((RecoveryMenu).embedPolicy (RecoveryPrior) horizon (RecoveryScheduler) agent.1
      (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights agent.1)
      (PhaseRecoveryProjection.information (runtime setup) leaks (RecoveryLeaks) agent.2.1)).map
        Subtype.val = _
  have decoded : SequentialPhasePlayerInformation.information setup.program (runtime setup) leaks
      (PhaseNativeProjection.nativeLeaks leaks (sequentialRuntimePhasePlan setup.program))
      (projectedAgent setup leaks bounds horizon scheduler agent clear).2.1 = agent.2.1 :=
    decoded_projected_input setup leaks bounds horizon scheduler agent clear
  rw [decoded]
  have recoveryLaw := congrArg (PMF.map Subtype.val)
    (recoveryComparisonStrategy_at_clear setup leaks bounds horizon scheduler assessment scale
      nonnegative le_one weights agent clear)
  rw [PMF.map_comp] at recoveryLaw
  have phaseLaw : componentStrategy setup leaks bounds horizon scheduler fallback assessment
      scale
      nonnegative le_one weights agent.1 agent.2.1 =
      (weights (pool setup leaks bounds horizon scheduler agent)).bind
        (component setup leaks bounds horizon scheduler assessment scale nonnegative le_one
          agent) :=
    (M).agentBehavior_at (M).playedInformation fallback _ agent
  rw [phaseLaw]
  simp only [ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp]
  exact recoveryLaw

/-- Every active clear played recovery input has the same raw policy law, via the
actual reverse trace representation. -/
theorem comparisonPolicy_at_clear
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (R).InformationAgent (R).playedInformation)
    (clear : RecoveryProjection.ClearInput (runtime setup) (RecoveryLeaks) agent.2.1)
    (active : agent.2.1 ≠ none) :
    (RecoveryMenu).embedPolicy (RecoveryPrior) horizon (RecoveryScheduler) agent.1
      (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights agent.1) agent.2.1 =
    SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program (runtime setup) leaks
      (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler agent.1
      (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
        le_one weights agent.1) agent.2.1 := by
  have represented := represented_of_clear setup leaks bounds horizon scheduler agent clear active
  obtain ⟨phase, clearPhase, same⟩ := represented
  have equality := comparisonPolicy_at_projected_clear setup leaks bounds horizon scheduler fallback
    assessment scale nonnegative le_one weights phase clearPhase
  cases agent with
  | mk who input =>
      cases phase with
      | mk owner phaseInput =>
          have owners := congrArg Sigma.fst same
          change owner = who at owners
          subst who
          have inputs := congrArg (fun other : (R).InformationAgent (R).playedInformation =>
            other.2.1) same
          change (projectedAgent setup leaks bounds horizon scheduler
            ⟨owner, phaseInput⟩ clearPhase).2.1 = input.1 at inputs
          rwa [inputs] at equality

/-- At every actual clear bounded recovery history, the comparison's raw
embedding agrees with the decoded phase policy for every player. -/
theorem comparisonPolicy_history
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (history : ((RecoveryMenu).protocol (RecoveryPrior) horizon (RecoveryScheduler)).History)
    (clear : ReactiveApplication.stateInvariant
      (fun state : RecoveryState (graph setup) => state.excluded = ∅) history.state)
    (who : Player) :
    (RecoveryMenu).embedPolicy (RecoveryPrior) horizon (RecoveryScheduler) who
      (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights who) ((A).observe who history.state) =
    SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program (runtime setup) leaks
      (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler who
      (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
        le_one weights who) ((A).observe who history.state) := by
  classical
  let first := (RecoveryMenu).embedPolicy (RecoveryPrior) horizon (RecoveryScheduler) who
    (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
      le_one weights who)
  let second := SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program (runtime setup) leaks
    (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler who
    (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
      le_one weights who)
  by_cases active : (A).actor history.state = some who
  · cases recoveryStateEq : history.state with
    | none => rw [recoveryStateEq] at active; cases active
    | some current =>
        have acting : current.actor = some who := by
          simpa only [recoveryStateEq, ReactiveApplication.actor, Option.bind_some] using active
        have empty : current.execution.application.excluded = ∅ := by rwa [recoveryStateEq] at clear
        have priors : RecoveryPrior = (Vegas.initialLaw setup).map
            (fun native => (⟨native, ∅⟩ : RecoveryState (graph setup))) := by
          simp only [recoveryInitialLaw, Vegas.initialLaw, serviceInitialLaw, PMF.map_comp,
            Function.comp_def]
        have recoveryTrace := Eq.mp (congrArg
          (fun prior : PMF (RecoveryState (graph setup)) =>
            ((RecoveryMenu).protocol prior horizon (RecoveryScheduler)).Trace (some current))
                priors)
          (recoveryStateEq ▸ history.trace)
        obtain ⟨phase, matched, _length⟩ := exists_canonical_phase_of_clear_recovery_trace setup
          leaks bounds horizon scheduler recoveryTrace empty
        have phaseRunning : ¬ (P).terminal phase.state := by
          have recoveryRunning : ¬ (A).terminal (some current) := by
            rintro ⟨_done, inactive⟩
            cases inactive.symm.trans acting
          rw [← matched] at recoveryRunning
          cases stateEq : phase.state with
          | none => rw [stateEq] at recoveryRunning; exact recoveryRunning
          | some phaseControl => rw [stateEq] at recoveryRunning; exact recoveryRunning
        let agent : (M).InformationAgent (M).playedInformation :=
          ⟨who, ⟨(M).infoOf who phase.trace, (M).mem_playedInformation phaseRunning⟩⟩
        have phaseObserved : agent.2.1 = (P).observe who phase.state :=
          (menu setup leaks bounds).info (phaseInitialLaw setup) horizon scheduler who phase.trace
        have phaseClear : ClearInput setup leaks agent.2.1 := by
          rw [phaseObserved]
          cases stateEq : phase.state with
          | none => rw [stateEq] at matched; cases matched
          | some phaseControl =>
              rw [stateEq] at matched
              have controls := Option.some.inj matched
              have owner : phaseControl.actor = some who :=
                (congrArg ReactiveApplication.Control.actor controls).trans acting
              have flags := congrArg (fun control : (A).Control =>
                control.execution.application.excluded) controls
              simp only [ReactiveApplication.observe, owner, ↓reduceIte]
              exact flags.trans empty
        have input : (projectedAgent setup leaks bounds horizon scheduler agent phaseClear).2.1 =
            (A).observe who history.state := by
          change PhaseRecoveryProjection.information (runtime setup) leaks (RecoveryLeaks)
            agent.2.1 = _
          rw [phaseObserved, recoveryStateEq]
          exact (PhaseRecoveryProjection.observe_state (runtime setup) leaks (RecoveryLeaks) who
            phase.state).symm.trans (congrArg ((A).observe who) matched)
        have equality := comparisonPolicy_at_projected_clear setup leaks bounds horizon scheduler
          fallback assessment scale nonnegative le_one weights agent phaseClear
        change first _ = second _ at equality
        rw [input] at equality
        dsimp only [first, second] at equality
        rw [recoveryStateEq] at equality
        exact equality
  · have rawTrace := (RecoveryMenu).toRawTrace (RecoveryPrior) horizon (RecoveryScheduler)
      history.trace
    have equality := (rawModel).behavioral_eq_of_not_active first second rawTrace active
    have information : (rawModel).infoOf who rawTrace = (A).observe who history.state :=
      (A).info (RecoveryPrior) horizon (RecoveryScheduler) who rawTrace
    rw [information] at equality
    exact equality

end Vegas.SequentialPhase
