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

/-- At every clear played phase input, the actual old comparison's embedded
raw policy is exactly the pure player-information decoding of the phase mixture. -/
theorem comparisonPolicy_at_projected_clear
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    (oldMenu).embedPolicy (oldInitial) horizon (oldScheduler) agent.1
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
  change ((oldMenu).embedPolicy (oldInitial) horizon (oldScheduler) agent.1
      (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights agent.1)
      (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1)).map
        Subtype.val = _
  have decoded : SequentialPhasePlayerInformation.information setup.program (runtime setup) leaks
      (PhaseNativeProjection.nativeLeaks leaks (sequentialRuntimePhasePlan setup.program))
      (projectedAgent setup leaks bounds horizon scheduler agent clear).2.1 = agent.2.1 :=
    decoded_projected_input setup leaks bounds horizon scheduler agent clear
  rw [decoded]
  have oldLaw := congrArg (PMF.map Subtype.val)
    (recoveryComparisonStrategy_at_clear setup leaks bounds horizon scheduler assessment scale
      nonnegative le_one weights agent clear)
  rw [PMF.map_comp] at oldLaw
  have phaseLaw : componentStrategy setup leaks bounds horizon scheduler fallback assessment
      scale
      nonnegative le_one weights agent.1 agent.2.1 =
      (weights (pool setup leaks bounds horizon scheduler agent)).bind
        (component setup leaks bounds horizon scheduler assessment scale nonnegative le_one
          agent) :=
    (M).agentBehavior_at (M).playedInformation fallback _ agent
  rw [phaseLaw]
  simp only [ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp]
  exact oldLaw

/-- Every active clear played old input has the same raw policy law, via the
actual reverse trace representation. -/
theorem comparisonPolicy_at_clear
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (R).InformationAgent (R).playedInformation)
    (clear : RecoveryProjection.ClearInput (runtime setup) (oldLeaks) agent.2.1)
    (active : agent.2.1 ≠ none) :
    (oldMenu).embedPolicy (oldInitial) horizon (oldScheduler) agent.1
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
    (history : ((oldMenu).protocol (oldInitial) horizon (oldScheduler)).History)
    (clear : ReactiveApplication.stateInvariant
      (fun state : RecoveryState (graph setup) => state.excluded = ∅) history.state)
    (who : Player) :
    (oldMenu).embedPolicy (oldInitial) horizon (oldScheduler) who
      (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights who) ((A).observe who history.state) =
    SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program (runtime setup) leaks
      (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler who
      (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
        le_one weights who) ((A).observe who history.state) := by
  classical
  let first := (oldMenu).embedPolicy (oldInitial) horizon (oldScheduler) who
    (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
      le_one weights who)
  let second := SequentialPhaseRecoveryPolicy.behavioralPolicy setup.program (runtime setup) leaks
    (menu setup leaks bounds) (setup.initialLaw.map setup.eventInputs) horizon scheduler who
    (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
      le_one weights who)
  by_cases active : (A).actor history.state = some who
  · cases oldAt : history.state with
    | none => rw [oldAt] at active; cases active
    | some current =>
        have acting : current.actor = some who := by
          simpa only [oldAt, ReactiveApplication.actor, Option.bind_some] using active
        have empty : current.execution.application.excluded = ∅ := by rwa [oldAt] at clear
        have priors : oldInitial = (Vegas.initialLaw setup).map
            (fun native => (⟨native, ∅⟩ : RecoveryState (graph setup))) := by
          simp only [recoveryInitialLaw, Vegas.initialLaw, serviceInitialLaw, PMF.map_comp,
            Function.comp_def]
        have oldTrace := Eq.mp (congrArg
          (fun prior : PMF (RecoveryState (graph setup)) =>
            ((oldMenu).protocol prior horizon (oldScheduler)).Trace (some current)) priors)
          (oldAt ▸ history.trace)
        obtain ⟨phase, matched, _length⟩ := exists_canonical_phase_of_clear_recovery_trace setup
          leaks bounds horizon scheduler oldTrace empty
        have phaseRunning : ¬ (P).terminal phase.state := by
          have oldRunning : ¬ (A).terminal (some current) := by
            rintro ⟨_done, inactive⟩
            cases inactive.symm.trans acting
          rw [← matched] at oldRunning
          cases stateEq : phase.state with
          | none => rw [stateEq] at oldRunning; exact oldRunning
          | some phaseControl => rw [stateEq] at oldRunning; exact oldRunning
        let agent : (M).InformationAgent (M).playedInformation :=
          ⟨who, ⟨(M).infoOf who phase.trace, (M).mem_playedInformation phaseRunning⟩⟩
        have phaseObserved : agent.2.1 = (P).observe who phase.state :=
          (menu setup leaks bounds).info (initialLaw setup) horizon scheduler who phase.trace
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
          change PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)
            agent.2.1 = _
          rw [phaseObserved, oldAt]
          exact (PhaseRecoveryProjection.observe_state (runtime setup) leaks (oldLeaks) who
            phase.state).symm.trans (congrArg ((A).observe who) matched)
        have equality := comparisonPolicy_at_projected_clear setup leaks bounds horizon scheduler
          fallback assessment scale nonnegative le_one weights agent phaseClear
        change first _ = second _ at equality
        rw [input] at equality
        dsimp only [first, second] at equality
        rw [oldAt] at equality
        exact equality
  · have rawTrace := (oldMenu).toRawTrace (oldInitial) horizon (oldScheduler) history.trace
    have equality := (rawModel).behavioral_eq_of_not_active first second rawTrace active
    have information : (rawModel).infoOf who rawTrace = (A).observe who history.state :=
      (A).info (oldInitial) horizon (oldScheduler) who rawTrace
    rw [information] at equality
    exact equality

end Vegas.SequentialPhase
