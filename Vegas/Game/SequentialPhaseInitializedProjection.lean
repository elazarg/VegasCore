/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryInitializedCoupling
import Vegas.Game.SequentialPhaseComparisonStopped
import GameTheoryExtensions.Analysis.Protocol.StoppedReadout
import Vegas.Game.PhaseExclusionPayoff
import Vegas.Game.RecoveryExclusionPayoff
import Vegas.Game.SequentialPhaseStoppedLaw
import Vegas.Game.SequentialPhaseBayesState
import Interaction.ReactiveLocalContinuation

/-! # Initialized phase comparison laws with excluded suffixes collapsed -/

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
local notation "RecoveryProtocol" => ReactiveApplication.ResponseMenu.protocol (RecoveryMenu)
    (RecoveryPrior)
  horizon (RecoveryScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (RecoveryPrior) horizon
    (RecoveryScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks
    RecoveryLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "RecoveryClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

omit [(P).FiniteNature (phaseInitialLaw setup) scheduler] in
private theorem phase_unclear_terminal
    (profile : ∀ who, (M).BehavioralPolicy who)
    (history : ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon
        scheduler).History)
    (unclear : ¬ phaseClear history.state)
    (final : ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History)
    (supported : final ∈ ((M).runBehavioralTerminalFrom
      ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
          scheduler).wellFoundedHistories
      profile history).support) : ¬ phaseClear final.state := by
  cases state : history.state with
  | none => exact (unclear (by simp [state, ReactiveApplication.stateInvariant])).elim
  | some control =>
    have nonempty : control.execution.application.current.excluded ≠ ∅ := by
      simpa only [state, ReactiveApplication.stateInvariant] using unclear
    obtain ⟨who, excluded⟩ := Finset.nonempty_iff_ne_empty.mpr nonempty
    have retained := (M).runBehavioralTerminalFrom_support_closed
      ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
          scheduler).wellFoundedHistories
      profile (PhaseExcluded setup .sequential (runtime setup) leaks who)
      (fun before joint _ after valid reached => phaseExcluded_transition setup .sequential
        (runtime setup) leaks (phaseInitialLaw setup) horizon scheduler before after joint valid
            reached)
      history (by simpa only [state, PhaseExcluded] using excluded) final supported
    intro clear
    cases target : final.state with
    | none => simp only [target, PhaseExcluded] at retained
    | some current =>
      have empty : current.execution.application.current.excluded = ∅ := by
        simpa only [target, ReactiveApplication.stateInvariant] using clear
      simp only [target, PhaseExcluded, empty, Finset.notMem_empty] at retained

omit [(P).FiniteNature (phaseInitialLaw setup) scheduler] in
private theorem recovery_unclear_terminal
    (profile : ∀ who, (R).BehavioralPolicy who) (history final : (RecoveryProtocol).History)
    (unclear : ¬ RecoveryClear history.state)
    (supported : final ∈ ((R).runBehavioralTerminalFrom
      ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
      profile history).support) : ¬ RecoveryClear final.state := by
  cases state : history.state with
  | none => exact (unclear (by simp [state, ReactiveApplication.stateInvariant])).elim
  | some control =>
    have nonempty : control.execution.application.excluded ≠ ∅ := by
      simpa only [state, ReactiveApplication.stateInvariant] using unclear
    obtain ⟨who, excluded⟩ := Finset.nonempty_iff_ne_empty.mpr nonempty
    have retained := (R).runBehavioralTerminalFrom_support_closed
      ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
          profile
      (RecoveryExcluded (setup := setup) (leaks := RecoveryLeaks) who)
      (fun before joint _ after valid reached => recoveryExcluded_transition
        (RecoveryPrior) horizon (RecoveryScheduler) before after joint valid reached)
      history (by simpa only [state, RecoveryExcluded] using excluded) final supported
    intro clear
    cases target : final.state with
    | none => simp only [target, RecoveryExcluded] at retained
    | some current =>
      have empty : current.execution.application.excluded = ∅ := by
        simpa only [target, ReactiveApplication.stateInvariant] using clear
      simp only [target, RecoveryExcluded, empty, Finset.notMem_empty] at retained

open Classical in
/-- Actual phase and comparison terminal states have the same law once each
excluded suffix is collapsed. No post-exclusion state or policy equality is used. -/
theorem component_initialized_masked_state_law
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) :
    (((M).runBehavioral
      (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
        le_one weights) (2 * horizon + 1)).map
      (fun final => if RecoveryClear (projection final.state) then some (projection final.state)
        else none)) =
    (((R).runBehavioral
      (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights) (2 * horizon + 1)).map
      (fun final => if RecoveryClear final.state then some final.state else none)) := by
  classical
  let phaseProfile := componentStrategy setup leaks bounds horizon scheduler fallback assessment
    scale nonnegative le_one weights
  let recoveryProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment
    scale nonnegative le_one weights
  let mask : (A).ProtocolState → Option (A).ProtocolState := fun state =>
    if RecoveryClear state then some state else none
  have clearEq (state : (P).ProtocolState) :
      phaseClear state ↔ RecoveryClear (projection state) := by cases state <;> rfl
  have phaseLaw := (M).runBehavioralTerminalFrom_map_eq_until_of_stable_readout
    ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon
        scheduler).wellFoundedHistories
    phaseProfile (fun history => ¬ phaseClear history.state)
    (fun history => mask (projection history.state)) (by
      intro history unclear final supported
      have later := phase_unclear_terminal setup leaks bounds horizon scheduler phaseProfile
        history unclear final supported
      have first : ¬ RecoveryClear (projection history.state) := by
        exact fun clear => unclear ((clearEq history.state).mpr clear)
      have last : ¬ RecoveryClear (projection final.state) := by
        exact fun clear => later ((clearEq final.state).mpr clear)
      simp only [mask, ite_eq_right first, ite_eq_right last])
    ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).initHistory
  have recoveryLaw := (R).runBehavioralTerminalFrom_map_eq_until_of_stable_readout
    ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler)).wellFoundedHistories
        recoveryProfile
    (fun history => ¬ RecoveryClear history.state) (fun history => mask history.state) (by
      intro history unclear final supported
      have later := recovery_unclear_terminal setup leaks bounds horizon scheduler recoveryProfile
        history final unclear supported
      simp only [mask, ite_eq_right unclear, ite_eq_right later]) (RecoveryProtocol).initHistory
  have exactStop := component_comparison_run_until_exclusion_or_guard_map_state setup leaks bounds
    horizon scheduler fallback assessment scale nonnegative le_one weights (fun _ => False)
    ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).initHistory
    (RecoveryProtocol).initHistory rfl
  simp only [or_false] at exactStop
  have masked := congrArg (PMF.map mask) exactStop
  simp only [PMF.map_comp, Function.comp_def] at masked
  rw [(M).runBehavioralTerminalFrom_initHistory _ phaseProfile
    ((menu setup leaks bounds).bounded (phaseInitialLaw setup) horizon scheduler)] at phaseLaw
  rw [(R).runBehavioralTerminalFrom_initHistory _ recoveryProfile
    ((RecoveryMenu).bounded (RecoveryPrior) horizon (RecoveryScheduler))] at recoveryLaw
  exact phaseLaw.trans (masked.trans recoveryLaw.symm)

open Classical in
/-- The actual projected native comparison controls the clear phase readout;
all excluded continuations are collapsed to the same failure atom. -/
theorem component_initialized_masked_native_readout_withinTV
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    {Outcome : Type} (nativeRead : (application setup (RecoveryLeaks)).ProtocolState → Outcome) :
    PMF.WithinTV
      (((onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) (RecoveryLeaks)
          (RecoveryScheduler))).runBehavioral
        (RecoveryOnePacket.sourceNativeProfile setup (RecoveryLeaks) bounds horizon
            (RecoveryScheduler)
          (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
            nonnegative le_one weights)) (2 * horizon + 1)).toOuterMeasure
        {history | ¬ ReactiveApplication.stateInvariant
          (app := application setup (RecoveryLeaks))
          (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk state ∅)) history.state}).toReal
      (((M).runBehavioral
        (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale
          nonnegative le_one weights) (2 * horizon + 1)).map (fun final => if
            ReactiveApplication.stateInvariant
          (app := A) (fun state => state.excluded = ∅) (projection final.state) then
            some (nativeRead (RecoveryProjection.protocolState (runtime setup) (RecoveryLeaks)
              (projection final.state))) else none))
      (((onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) (RecoveryLeaks)
          (RecoveryScheduler))).runBehavioral
        (RecoveryOnePacket.sourceNativeProfile setup (RecoveryLeaks) bounds horizon
            (RecoveryScheduler)
          (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
            nonnegative le_one weights)) (2 * horizon + 1)).map (fun final => some
              (nativeRead final.state)))
        := by
  classical
  let mask : (A).ProtocolState → Option Outcome := fun state =>
    if RecoveryClear state then
      some (nativeRead (RecoveryProjection.protocolState (runtime setup) (RecoveryLeaks) state))
    else none
  have exactMask := component_initialized_masked_state_law setup leaks bounds horizon scheduler
    fallback assessment scale nonnegative le_one weights
  have mapped := congrArg (PMF.map (Option.map fun state =>
    nativeRead (RecoveryProjection.protocolState (runtime setup) (RecoveryLeaks) state))) exactMask
  simp only [PMF.map_comp, Function.comp_def] at mapped
  have masked :
      (((M).runBehavioral
        (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale
          nonnegative le_one weights) (2 * horizon + 1)).map
          (fun final => mask (projection final.state))) =
      (((R).runBehavioral
        (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
          nonnegative le_one weights) (2 * horizon + 1)).map (fun final => mask final.state)) := by
    simpa only [mask, apply_ite (Option.map _), Option.map_some, Option.map_none] using mapped
  have close := RecoveryOnePacket.recovery_initialized_projection_withinTV setup (RecoveryLeaks)
    bounds horizon (RecoveryScheduler)
    (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
      le_one weights) (fun state => some (nativeRead state)) mask (by
      intro state clear
      have valid : RecoveryClear state := by
        cases state with
        | none => trivial
        | some control => exact clear control rfl
      simp only [mask, ite_eq_left valid])
  erw [← masked] at close
  exact close

/-- Actual phase initialization differs from its actual native comparison
projection only on the native terminal public-failure mass. The readouts need
agree only on genuine clear phase histories. -/
theorem component_initialized_projection_withinTV
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    {Outcome : Type} (nativeRead : (application setup (RecoveryLeaks)).ProtocolState → Outcome)
    (phaseRead : (P).ProtocolState → Outcome)
    (agree : ∀ history : ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon
      scheduler).History, phaseClear history.state →
      phaseRead history.state = nativeRead
        (RecoveryProjection.protocolState (runtime setup) (RecoveryLeaks) (projection
            history.state))) :
    PMF.WithinTV
      (((onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) (RecoveryLeaks)
          (RecoveryScheduler))).runBehavioral
        (RecoveryOnePacket.sourceNativeProfile setup (RecoveryLeaks) bounds horizon
            (RecoveryScheduler)
          (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
            nonnegative le_one weights)) (2 * horizon + 1)).toOuterMeasure
        {history | ¬ ReactiveApplication.stateInvariant
          (app := application setup (RecoveryLeaks))
          (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk state ∅)) history.state}).toReal
      (((M).runBehavioral
        (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale
          nonnegative le_one weights) (2 * horizon + 1)).map (fun final => phaseRead final.state))
      (((onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) (RecoveryLeaks)
          (RecoveryScheduler))).runBehavioral
        (RecoveryOnePacket.sourceNativeProfile setup (RecoveryLeaks) bounds horizon
            (RecoveryScheduler)
          (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
            nonnegative le_one weights)) (2 * horizon + 1)).map (fun final => nativeRead
              final.state))
         := by
  classical
  let mask : (A).ProtocolState → Option Outcome := fun state =>
    if RecoveryClear state then
      some (nativeRead (RecoveryProjection.protocolState (runtime setup) (RecoveryLeaks) state))
    else none
  have close := component_initialized_masked_native_readout_withinTV setup leaks bounds horizon
    scheduler fallback assessment scale nonnegative le_one weights nativeRead
  have classified : ∀ history ∈ (((M).runBehavioral
      (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
        le_one weights) (2 * horizon + 1))).support, ∀ value,
      mask (projection history.state) = some value → phaseRead history.state = value := by
    intro history supported value reading
    dsimp only [mask] at reading
    split_ifs at reading with clear
    · cases Option.some.inj reading
      have clearEq (state : (P).ProtocolState) :
          phaseClear state ↔ RecoveryClear (projection state) := by cases state <;> rfl
      exact agree history ((clearEq history.state).mpr clear)
  let reference : PMF Outcome :=
    ((onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) (RecoveryLeaks)
          (RecoveryScheduler))).runBehavioral
      (RecoveryOnePacket.sourceNativeProfile setup (RecoveryLeaks) bounds horizon
          (RecoveryScheduler)
        (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
          nonnegative le_one weights)) (2 * horizon + 1)).map (fun final => nativeRead final.state)
  have estimate := withinTV_map_of_partial_classes
    ((M).runBehavioral
      (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale nonnegative
        le_one weights) (2 * horizon + 1))
    (fun final => phaseRead final.state) (fun final => mask (projection final.state)) id reference
    classified (by
      simpa only [reference, PMF.map_comp, Function.comp_def] using close)
  simpa only [PMF.map_id] using estimate

end Vegas.SequentialPhase
