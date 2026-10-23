/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryComparisonRetention
import Vegas.Game.SourceServiceSiteBridge

/-! # Initialized source laws under the actual recovery service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {horizon : Nat} {scheduler : (application setup leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler

private theorem first_native_state_law (players : ∀ who, (N).BehavioralPolicy who) :
    ((N).runBehavioralFrom players 1 (E).initHistory).map History.state =
      (initialLaw setup).map (fun native =>
        some ⟨horizon, none, ReactiveApplication.Execution.initial (application setup leaks)
          native⟩) := by
  classical
  have running : ¬ (E).terminal (E).initHistory.state := by change ¬ False; trivial
  rw [(N).runBehavioralFrom_succ_of_not_terminal players 0 running,
    (N).behavioralJoint_eq_pure_of_no_active players (E).initHistory.trace running
      (by intro who; change ¬ ((none : Option Player) = some who); simp),
    PMF.pure_bind, map_bindOnSupport]
  simp only [InformationModel.runBehavioralFrom, runRandomizedFor_zero, PMF.pure_map]
  change ((initialLaw setup).map (fun native =>
      some (⟨horizon, none, ReactiveApplication.Execution.initial (application setup leaks)
        native⟩ : (application setup leaks).Control))).bindOnSupport
      (fun state _ => PMF.pure state) = _
  exact PMF.bindOnSupport_pure _

private theorem initial_native_boundary (wellFormed : setup.WellFormed)
    (profile : BehavioralProfile setup.program)
    (native : (application setup leaks).State) (member : native ∈ (initialLaw setup).support)
    (start : (E).History)
    (state : start.state = some ⟨horizon, none,
      ReactiveApplication.Execution.initial (application setup leaks) native⟩) :
    let execution := ReactiveApplication.Execution.initial (application setup leaks) native
    ∃ point, ReachedBoundary setup leaks horizon scheduler 0 execution ∧
      sourceServicePrefix? setup 0 native.config = some point ∧
      ProtocolState.Intended setup.program point := by
  intro execution
  obtain ⟨inputs, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  let residual := SourceResidual.initial setup profile inputs
  have intended : ProtocolState.Intended setup.program
      (ProtocolState.entry setup.program (setup.initialConfig inputs)) :=
    ProtocolState.intended_entry setup.program _
      (setup.initialConfig_intended wellFormed supported)
      (wellFormed.guardsSatisfiable inputs supported)
  refine ⟨_, ?_, residual.decode, intended⟩
  apply reachedBoundary_of_onePacket bounds start
    (by simpa only [execution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.sub_zero] using state) (by simp [execution, ReactiveApplication.Execution.initial])
    residual.checkpoint.ordered ?_ _ residual.decode intended
  intro event beyond who entry recalled
  simp [execution, ReactiveApplication.Execution.initial] at recalled

private theorem initial_native_boundary_of_step (wellFormed : setup.WellFormed)
    (profile : BehavioralProfile setup.program) (players : ∀ who, (N).BehavioralPolicy who)
    (start : (E).History)
    (supported : start ∈ ((N).runBehavioralFrom players 1 (E).initHistory).support) :
    ∃ native ∈ (initialLaw setup).support,
      start.state = some ⟨horizon, none,
        ReactiveApplication.Execution.initial (application setup leaks) native⟩ ∧
      ∃ point, ReachedBoundary setup leaks horizon scheduler 0
          (ReactiveApplication.Execution.initial (application setup leaks) native) ∧
        sourceServicePrefix? setup 0 native.config = some point ∧
        ProtocolState.Intended setup.program point := by
  have inState := (PMF.mem_support_map_iff History.state _ _).mpr ⟨start, supported, rfl⟩
  rw [first_native_state_law] at inState
  obtain ⟨native, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp inState
  refine ⟨native, member, same.symm, ?_⟩
  exact initial_native_boundary wellFormed profile native member start same.symm

variable {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler delay)
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "NativeModel" => onePacketModel setup leaks bounds (initialLaw setup) horizon
  nativeScheduler
local notation "NativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon nativeScheduler

include initialized nativeLaw opportunity inclusion timely completes in
/-- Actual recovery service makes initialized honest native play preserve the
entire intended terminal store law, with its private setup draw. -/
theorem recovery_honest_initialized_readout_law
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    (((NativeModel).runBehavioralTerminalFrom certificate
      (honestProfile setup leaks bounds (initialLaw setup) horizon nativeScheduler source)
        (NativeProtocol).initHistory).map (fun final => sourceReadout setup leaks final.state)) =
      (setup.intendedModel.runBehavioral source.strategy
        (instructionCount setup.program + 1)).map
          (fun final => setup.protocolReadout final.state) :=
    by
  classical
  let players := honestProfile setup leaks bounds (initialLaw setup) horizon nativeScheduler source
  let profile := setup.intendedOpeningProfile source.strategy
  let continuation : (application setup leaks).ProtocolState →
      PMF (Option (State L setup.program.terminalCtx)) := fun state =>
    state.elim ((setup.run profile).map some) (fun control =>
      sourceContinuation setup profile 0 control.execution.application.config)
  rw [setup.intendedOpeningProfile_run wellFormed source.strategy,
    ← initialLaw_bind_sourceContinuation setup profile]
  rw [(NativeModel).runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate players 1,
    PMF.map_bind]
  calc
    _ = ((NativeModel).runBehavioralFrom players 1 (NativeProtocol).initHistory).bind
        (fun start => continuation start.state) := by
      apply bind_congr_on_support _
      intro start supported
      obtain ⟨native, member, state, point, boundary, decoded, intended⟩ :=
        initial_native_boundary_of_step wellFormed profile players start supported
      have result := recovery_honest_boundary_readout_law initialized nativeLaw opportunity
        inclusion
        timely completes wellFormed covers capacity source certificate 0 start
          (ReactiveApplication.Execution.initial (application setup leaks) native)
          (by simpa [ReactiveApplication.Execution.initial] using state) boundary point decoded
            intended
      simpa only [continuation, state, Option.elim_some] using result
    _ = _ := by
      have changed := congrArg (fun law : PMF (application setup leaks).ProtocolState =>
        law.bind continuation)
        (first_native_state_law players)
      simpa only [continuation, PMF.bind_map, Function.comp_def, Option.elim_some,
        ReactiveApplication.Execution.initial] using changed

include initialized nativeLaw opportunity inclusion timely completes in
/-- Every initialized supported honest native input is a first activation or
already has its event packet recorded. -/
theorem recovery_honest_initialized_not_late
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    ∀ fuel history, history ∈ ((NativeModel).runBehavioralFrom
      (honestProfile setup leaks bounds (initialLaw setup) horizon nativeScheduler source) fuel
        (NativeProtocol).initHistory).support →
      ∀ who, ¬ LateDelivery setup leaks who ((NativeModel).infoOf who history.trace) := by
  classical
  let players := honestProfile setup leaks bounds (initialLaw setup) horizon nativeScheduler source
  intro fuel history supported who
  cases fuel with
  | zero =>
      change history ∈ (PMF.pure _).support at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rintro ⟨past, view, event, same, pending, _⟩
      cases same
  | succ fuel =>
      rw [show fuel + 1 = 1 + fuel by omega,
        (NativeModel).runBehavioralFrom_add players 1 fuel] at supported
      obtain ⟨start, initialMem, continued⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      obtain ⟨native, member, state, point, boundary, decoded, intended⟩ :=
        initial_native_boundary_of_step wellFormed (setup.intendedOpeningProfile source.strategy)
          players start initialMem
      exact recovery_honest_reached_not_late initialized nativeLaw opportunity timely inclusion
        completes wellFormed covers capacity source certificate 0 start
        (ReactiveApplication.Execution.initial (application setup leaks) native)
        (by simpa [ReactiveApplication.Execution.initial] using state) boundary point decoded
        intended fuel history continued who

include initialized nativeLaw opportunity inclusion timely completes in
/-- Every initialized honest native execution decodes to an intended source
point under the actual recovery service. -/
theorem recovery_honest_initialized_intended
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    ∀ fuel history, history ∈ ((NativeModel).runBehavioralFrom
      (honestProfile setup leaks bounds (initialLaw setup) horizon nativeScheduler source) fuel
        (NativeProtocol).initHistory).support →
      ∀ control : (application setup leaks).Control, history.state = some control →
        ∃ point, decodedPoint setup control.execution.application.config = some point ∧
          ProtocolState.Intended setup.program point := by
  classical
  let players := honestProfile setup leaks bounds (initialLaw setup) horizon nativeScheduler source
  intro fuel history supported control current
  cases fuel with
  | zero =>
      change history ∈ (PMF.pure _).support at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      cases current
  | succ fuel =>
      rw [show fuel + 1 = 1 + fuel by omega,
        (NativeModel).runBehavioralFrom_add players 1 fuel] at supported
      obtain ⟨start, initialMem, continued⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      obtain ⟨native, member, state, point, boundary, decoded, intended⟩ :=
        initial_native_boundary_of_step wellFormed (setup.intendedOpeningProfile source.strategy)
          players start initialMem
      have sourceLaw := recovery_honest_boundary_readout_law initialized nativeLaw opportunity
        inclusion timely completes wellFormed covers capacity source certificate 0 start
          (ReactiveApplication.Execution.initial (application setup leaks) native)
          (by simpa [ReactiveApplication.Execution.initial] using state) boundary point decoded
            intended
      have sourceEq : sourceContinuation setup (setup.intendedOpeningProfile source.strategy) 0
          native.config =
            (setup.continuationLaw (setup.intendedOpeningProfile source.strategy)
              (some point)).map some :=
        congrArg (fun point =>
          (setup.continuationLaw (setup.intendedOpeningProfile source.strategy) point).map some)
          decoded
      exact honest_reached_intended_of_readout_law bounds wellFormed source certificate start point
        (decodedPoint_staticAt ((decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded))
        intended (sourceLaw.trans sourceEq) fuel history continued control current

end Vegas

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)

/-- The unchanged common recovery weights retain initialized honest native
play, including its setup draw, under actual recovery service. -/
theorem nativeComparison_dominatesHonestFrom_initialized [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (certificate : (NP).WellFoundedHistories) :
    DominatesHonestFrom setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
      (sequence n) (slotRetention (scale n))
      (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n) (NP).initHistory := by
  classical
  let players := honestProfile setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
    (sequence n)
  intro fuel history reached who choice
  by_cases empty : history.state = none
  · have observed : (N).infoOf who history.trace = none := by
      change ((bounds.onePacketMenu (runtime setup) leaks).signals (initialLaw setup) horizon
        (NativeScheduler)).infoOf who history.trace = none
      rw [ReactiveApplication.ResponseMenu.info, empty]
      rfl
    revert choice
    rw [observed]
    intro choice
    have : Subsingleton ((N).Choice who none) :=
      InformationModel.subsingleton_choice_of_menu_subsingleton _ _ Set.subsingleton_singleton
    have unit (law : PMF ((N).Choice who none)) : law choice = 1 := by
      rw [← law.tsum_coe, tsum_eq_single choice (fun other different =>
        (different (Subsingleton.elim other choice)).elim)]
    rw [unit, unit, ENNReal.toReal_one, mul_one]
    exact slotRetention_le_one (positive n).le (le_one n)
  · obtain ⟨control, current⟩ := Option.ne_none_iff_exists'.mp empty
    obtain ⟨point, decoded, intended⟩ := recovery_honest_initialized_intended
      (initialLaw_initialized setup) (initialLaw_native setup) opportunity inclusion timely
      completes
      wellFormed covers capacity (sequence n) certificate fuel history reached control
        current
    have forced : Vegas.forcedAgent (bounds.onePacketMenu (runtime setup) leaks)
        (initialLaw setup) horizon (NativeScheduler) who ((N).infoOf who history.trace) := by
      apply forcedAgent_of_history history
      rw [current]
      exact (forcedState_iff_decodedPoint control).mpr
        ⟨point, decoded, forcedPoint_of_intended who intended⟩
    have notLate := recovery_honest_initialized_not_late (initialLaw_initialized setup)
      (initialLaw_native setup) opportunity inclusion timely completes wellFormed covers capacity
      (sequence n) certificate fuel history reached who
    exact onePacketMixture_ge_honest_of_not_late setup leaks bounds horizon (NativeScheduler)
      sequence scale positive le_one n
      (nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
      notLate ⟨history, rfl⟩ forced choice

end Vegas.RecoveryOnePacket
