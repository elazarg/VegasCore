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
local notation "oldProtocol" => ReactiveApplication.ResponseMenu.protocol (oldMenu) (oldInitial)
  horizon (oldScheduler)
local notation "rawProtocol" => ReactiveApplication.protocol (A) (oldInitial) horizon (oldScheduler)
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks oldLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "oldClear" => ReactiveApplication.stateInvariant (app := A)
  (fun state => RecoveryState.excluded state = ∅)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq


omit [(P).FiniteNature (initialLaw setup) scheduler] in
private theorem phase_unclear_terminal
    (profile : ∀ who, (M).BehavioralPolicy who)
    (history : ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).History)
    (unclear : ¬ phaseClear history.state)
    (final : ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).History)
    (supported : final ∈ ((M).runBehavioralTerminalFrom
      ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
      profile history).support) : ¬ phaseClear final.state := by
  cases state : history.state with
  | none => exact (unclear (by simp [state, ReactiveApplication.stateInvariant])).elim
  | some control =>
    have nonempty : control.execution.application.current.excluded ≠ ∅ := by
      simpa only [state, ReactiveApplication.stateInvariant] using unclear
    obtain ⟨who, excluded⟩ := Finset.nonempty_iff_ne_empty.mpr nonempty
    have retained := (M).runBehavioralTerminalFrom_support_closed
      ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
      profile (PhaseExcluded setup .sequential (runtime setup) leaks who)
      (fun before joint _ after valid reached => phaseExcluded_transition setup .sequential
        (runtime setup) leaks (initialLaw setup) horizon scheduler before after joint valid reached)
      history (by simpa only [state, PhaseExcluded] using excluded) final supported
    intro clear
    cases target : final.state with
    | none => simp only [target, PhaseExcluded] at retained
    | some current =>
      have empty : current.execution.application.current.excluded = ∅ := by
        simpa only [target, ReactiveApplication.stateInvariant] using clear
      simp only [target, PhaseExcluded, empty, Finset.notMem_empty] at retained

omit [(P).FiniteNature (initialLaw setup) scheduler] in
private theorem recovery_unclear_terminal
    (profile : ∀ who, (R).BehavioralPolicy who) (history final : (oldProtocol).History)
    (unclear : ¬ oldClear history.state)
    (supported : final ∈ ((R).runBehavioralTerminalFrom
      ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories
      profile history).support) : ¬ oldClear final.state := by
  cases state : history.state with
  | none => exact (unclear (by simp [state, ReactiveApplication.stateInvariant])).elim
  | some control =>
    have nonempty : control.execution.application.excluded ≠ ∅ := by
      simpa only [state, ReactiveApplication.stateInvariant] using unclear
    obtain ⟨who, excluded⟩ := Finset.nonempty_iff_ne_empty.mpr nonempty
    have retained := (R).runBehavioralTerminalFrom_support_closed
      ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories profile
      (RecoveryExcluded (setup := setup) (leaks := oldLeaks) who)
      (fun before joint _ after valid reached => recoveryExcluded_transition
        (oldInitial) horizon (oldScheduler) before after joint valid reached)
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
      (fun final => if oldClear (projection final.state) then some (projection final.state)
        else none)) =
    (((R).runBehavioral
      (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
        le_one weights) (2 * horizon + 1)).map
      (fun final => if oldClear final.state then some final.state else none)) := by
  classical
  let phaseProfile := componentStrategy setup leaks bounds horizon scheduler fallback assessment
    scale nonnegative le_one weights
  let oldProfile := recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment
    scale nonnegative le_one weights
  let mask : (A).ProtocolState → Option (A).ProtocolState := fun state =>
    if oldClear state then some state else none
  have clearEq (state : (P).ProtocolState) :
      phaseClear state ↔ oldClear (projection state) := by cases state <;> rfl
  have phaseLaw := (M).runBehavioralTerminalFrom_map_eq_until_of_stable_readout
    ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
    phaseProfile (fun history => ¬ phaseClear history.state)
    (fun history => mask (projection history.state)) (by
      intro history unclear final supported
      have later := phase_unclear_terminal setup leaks bounds horizon scheduler phaseProfile
        history unclear final supported
      have first : ¬ oldClear (projection history.state) := by
        exact fun clear => unclear ((clearEq history.state).mpr clear)
      have last : ¬ oldClear (projection final.state) := by
        exact fun clear => later ((clearEq final.state).mpr clear)
      simp only [mask, ite_eq_right first, ite_eq_right last])
    ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).initHistory
  have oldLaw := (R).runBehavioralTerminalFrom_map_eq_until_of_stable_readout
    ((oldMenu).bounded (oldInitial) horizon (oldScheduler)).wellFoundedHistories oldProfile
    (fun history => ¬ oldClear history.state) (fun history => mask history.state) (by
      intro history unclear final supported
      have later := recovery_unclear_terminal setup leaks bounds horizon scheduler oldProfile
        history final unclear supported
      simp only [mask, ite_eq_right unclear, ite_eq_right later]) (oldProtocol).initHistory
  have exactStop := component_comparison_run_until_exclusion_or_guard_map_state setup leaks bounds
    horizon scheduler fallback assessment scale nonnegative le_one weights (fun _ => False)
    ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).initHistory
    (oldProtocol).initHistory rfl
  simp only [or_false] at exactStop
  have masked := congrArg (PMF.map mask) exactStop
  simp only [PMF.map_comp, Function.comp_def] at masked
  rw [(M).runBehavioralTerminalFrom_initHistory _ phaseProfile
    ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler)] at phaseLaw
  rw [(R).runBehavioralTerminalFrom_initHistory _ oldProfile
    ((oldMenu).bounded (oldInitial) horizon (oldScheduler))] at oldLaw
  exact phaseLaw.trans (masked.trans oldLaw.symm)

open Classical in
/-- The actual projected native comparison controls the clear phase readout;
all excluded continuations are collapsed to the same failure atom. -/
theorem component_initialized_masked_native_readout_withinTV
    (fallback : ∀ who, (M).Policy who)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    {Outcome : Type} (nativeRead : (application setup (oldLeaks)).ProtocolState → Outcome) :
    PMF.WithinTV
      (((onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
          (oldScheduler))).runBehavioral
        (RecoveryOnePacket.sourceNativeProfile setup (oldLeaks) bounds horizon (oldScheduler)
          (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
            nonnegative le_one weights)) (2 * horizon + 1)).toOuterMeasure
        {history | ¬ ReactiveApplication.stateInvariant
          (app := application setup (oldLeaks))
          (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk state ∅)) history.state}).toReal
      (((M).runBehavioral
        (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale
          nonnegative le_one weights) (2 * horizon + 1)).map (fun final => if
            ReactiveApplication.stateInvariant
          (app := A) (fun state => state.excluded = ∅) (projection final.state) then
            some (nativeRead (RecoveryProjection.protocolState (runtime setup) (oldLeaks)
              (projection final.state))) else none))
      (((onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
          (oldScheduler))).runBehavioral
        (RecoveryOnePacket.sourceNativeProfile setup (oldLeaks) bounds horizon (oldScheduler)
          (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
            nonnegative le_one weights)) (2 * horizon + 1)).map (fun final => some
              (nativeRead final.state)))
        := by
  classical
  let mask : (A).ProtocolState → Option Outcome := fun state =>
    if oldClear state then
      some (nativeRead (RecoveryProjection.protocolState (runtime setup) (oldLeaks) state))
    else none
  have exactMask := component_initialized_masked_state_law setup leaks bounds horizon scheduler
    fallback assessment scale nonnegative le_one weights
  have mapped := congrArg (PMF.map (Option.map fun state =>
    nativeRead (RecoveryProjection.protocolState (runtime setup) (oldLeaks) state))) exactMask
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
  have close := RecoveryOnePacket.recovery_initialized_projection_withinTV setup (oldLeaks)
    bounds horizon (oldScheduler)
    (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale nonnegative
      le_one weights) (fun state => some (nativeRead state)) mask (by
      intro state clear
      have valid : oldClear state := by
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
    {Outcome : Type} (nativeRead : (application setup (oldLeaks)).ProtocolState → Outcome)
    (phaseRead : (P).ProtocolState → Outcome)
    (agree : ∀ history : ((menu setup leaks bounds).protocol (initialLaw setup) horizon
      scheduler).History, phaseClear history.state →
      phaseRead history.state = nativeRead
        (RecoveryProjection.protocolState (runtime setup) (oldLeaks) (projection history.state))) :
    PMF.WithinTV
      (((onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
          (oldScheduler))).runBehavioral
        (RecoveryOnePacket.sourceNativeProfile setup (oldLeaks) bounds horizon (oldScheduler)
          (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
            nonnegative le_one weights)) (2 * horizon + 1)).toOuterMeasure
        {history | ¬ ReactiveApplication.stateInvariant
          (app := application setup (oldLeaks))
          (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk state ∅)) history.state}).toReal
      (((M).runBehavioral
        (componentStrategy setup leaks bounds horizon scheduler fallback assessment scale
          nonnegative le_one weights) (2 * horizon + 1)).map (fun final => phaseRead final.state))
      (((onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
          (oldScheduler))).runBehavioral
        (RecoveryOnePacket.sourceNativeProfile setup (oldLeaks) bounds horizon (oldScheduler)
          (recoveryComparisonStrategy setup leaks bounds horizon scheduler assessment scale
            nonnegative le_one weights)) (2 * horizon + 1)).map (fun final => nativeRead
              final.state))
         := by
  classical
  let mask : (A).ProtocolState → Option Outcome := fun state =>
    if oldClear state then
      some (nativeRead (RecoveryProjection.protocolState (runtime setup) (oldLeaks) state))
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
          phaseClear state ↔ oldClear (projection state) := by cases state <;> rfl
      exact agree history ((clearEq history.state).mpr clear)
  let reference : PMF Outcome :=
    ((onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks) (oldScheduler))).runBehavioral
      (RecoveryOnePacket.sourceNativeProfile setup (oldLeaks) bounds horizon (oldScheduler)
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
