/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketHonestRecall
import Vegas.Game.SourceServiceSiteBridge
import Vegas.Game.SourceDebtObservation

/-! # Initialized source laws under the counted native service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler

private theorem first_native_state_law (players : ∀ who, (N).BehavioralPolicy who) :
    ((N).runBehavioralFrom players 1 (E).initHistory).map History.state =
      (initialLaw setup).map (fun native =>
        some ⟨horizon, none, ReactiveApplication.Execution.initial (application setup runtime leaks)
          native⟩) := by
  classical
  have running : ¬ (E).terminal (E).initHistory.state := by change ¬ False; trivial
  rw [(N).runBehavioralFrom_succ_of_not_terminal players 0 running,
    (N).behavioralJoint_eq_pure_of_no_active players (E).initHistory.trace running
      (by intro who; change ¬ ((none : Option Player) = some who); simp),
    PMF.pure_bind, map_bindOnSupport]
  simp only [InformationModel.runBehavioralFrom, runRandomizedFor_zero, PMF.pure_map]
  change ((initialLaw setup).map (fun native =>
      some (⟨horizon, none, ReactiveApplication.Execution.initial (application setup runtime leaks)
        native⟩ : (application setup runtime leaks).Control))).bindOnSupport
      (fun state _ => PMF.pure state) = _
  exact PMF.bindOnSupport_pure _

private theorem initial_native_boundary (wellFormed : setup.WellFormed)
    (profile : BehavioralProfile setup.program)
    (native : (application setup runtime leaks).State) (member : native ∈ (initialLaw
      setup).support)
    (start : (E).History)
    (state : start.state = some ⟨horizon, none,
      ReactiveApplication.Execution.initial (application setup runtime leaks) native⟩) :
    let execution := ReactiveApplication.Execution.initial (application setup runtime leaks) native
    ∃ point, ReachedBoundary setup runtime leaks horizon scheduler 0 execution ∧
      sourceServicePrefix? setup 0 native.config = some point ∧
      ProtocolState.Intended setup.program point := by
  intro execution
  obtain ⟨inputs, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  let residual := SourceResidual.initial setup profile inputs
  have intended : ProtocolState.Intended setup.program
      (ProtocolState.entry setup.program (Config.initial inputs)) :=
    ProtocolState.intended_entry setup.program _
      (Config.initial_intended wellFormed supported)
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
        ReactiveApplication.Execution.initial (application setup runtime leaks) native⟩ ∧
      ∃ point, ReachedBoundary setup runtime leaks horizon scheduler 0
          (ReactiveApplication.Execution.initial (application setup runtime leaks) native) ∧
        sourceServicePrefix? setup 0 native.config = some point ∧
        ProtocolState.Intended setup.program point := by
  have inState := (PMF.mem_support_map_iff History.state _ _).mpr ⟨start, supported, rfl⟩
  rw [first_native_state_law] at inState
  obtain ⟨native, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp inState
  refine ⟨native, member, same.symm, ?_⟩
  exact initial_native_boundary (runtime := runtime) wellFormed profile native member start
    same.symm

variable {delay bound : (graph setup).EventId → Nat}
  (opportunity : ∀ control : (application setup runtime leaks).Control,
    (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    OpportunityAt runtime leaks control.execution delay)
  (inclusion : ∀ control : (application setup runtime leaks).Control,
    (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    ProtectedInclusionAt runtime leaks control.execution bound)
  (timely : runtime.AsyncTimely delay bound)
  (completes : ∀ control : (application setup runtime leaks).Control,
    (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    (application setup runtime leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)

local notation "NativeModel" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  scheduler
local notation "NativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler

include opportunity inclusion timely completes in
/-- Counted native service makes initialized honest native play preserve the
entire intended terminal store law, with its private setup draw. -/
theorem counted_honest_initialized_readout_law
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    (((NativeModel).runBehavioralTerminalFrom certificate
      (honestProfile setup runtime leaks bounds (initialLaw setup) horizon scheduler source)
        (NativeProtocol).initHistory).map (fun final => sourceReadout setup runtime leaks
          final.state)) =
      (setup.intendedModel.runBehavioral source.strategy
        (instructionCount setup.program + 1)).map
          (fun final => setup.protocolReadout final.state) :=
    by
  classical
  let players := honestProfile setup runtime leaks bounds (initialLaw setup) horizon scheduler
    source
  let profile := setup.intendedOpeningProfile source.strategy
  let continuation : (application setup runtime leaks).ProtocolState →
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
        initial_native_boundary_of_step (runtime := runtime) wellFormed profile players start
          supported
      have result := counted_honest_boundary_readout_law (runtime := runtime) opportunity
        inclusion
        timely completes wellFormed covers capacity source certificate 0 start
          (ReactiveApplication.Execution.initial (application setup runtime leaks) native)
          (by simpa [ReactiveApplication.Execution.initial] using state) boundary point decoded
            intended
      simpa only [continuation, state, Option.elim_some] using result
    _ = _ := by
      have changed := congrArg (fun law : PMF (application setup runtime leaks).ProtocolState =>
        law.bind continuation)
        (first_native_state_law (runtime := runtime) players)
      simpa only [continuation, PMF.bind_map, Function.comp_def, Option.elim_some,
        ReactiveApplication.Execution.initial] using changed

include opportunity inclusion timely completes in
/-- Every initialized supported honest native input is a first activation or
already has its event packet recorded. -/
theorem counted_honest_initialized_not_late
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    ∀ fuel history, history ∈ ((NativeModel).runBehavioralFrom
      (honestProfile setup runtime leaks bounds (initialLaw setup) horizon scheduler source) fuel
        (NativeProtocol).initHistory).support →
      ∀ who, ¬ LateDelivery setup runtime leaks who ((NativeModel).infoOf who history.trace) := by
  classical
  let players := honestProfile setup runtime leaks bounds (initialLaw setup) horizon scheduler
    source
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
        initial_native_boundary_of_step (runtime := runtime) wellFormed
          (setup.intendedOpeningProfile source.strategy)
          players start initialMem
      exact counted_honest_reached_not_late (runtime := runtime) opportunity timely inclusion
        completes wellFormed covers capacity source certificate 0 start
        (ReactiveApplication.Execution.initial (application setup runtime leaks) native)
        (by simpa [ReactiveApplication.Execution.initial] using state) boundary point decoded
        intended fuel history continued who

include opportunity inclusion timely completes in
/-- Every initialized honest native execution decodes to an intended source
point under the counted native service. -/
theorem counted_honest_initialized_intended
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (NativeProtocol).WellFoundedHistories) :
    ∀ fuel history, history ∈ ((NativeModel).runBehavioralFrom
      (honestProfile setup runtime leaks bounds (initialLaw setup) horizon scheduler source) fuel
        (NativeProtocol).initHistory).support →
      ∀ control : (application setup runtime leaks).Control, history.state = some control →
        ∃ point, decodedPoint setup control.execution.application.config = some point ∧
          ProtocolState.Intended setup.program point := by
  classical
  let players := honestProfile setup runtime leaks bounds (initialLaw setup) horizon scheduler
    source
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
        initial_native_boundary_of_step (runtime := runtime) wellFormed
          (setup.intendedOpeningProfile source.strategy)
          players start initialMem
      have sourceLaw := counted_honest_boundary_readout_law (runtime := runtime) opportunity
        inclusion timely completes wellFormed covers capacity source certificate 0 start
          (ReactiveApplication.Execution.initial (application setup runtime leaks) native)
          (by simpa [ReactiveApplication.Execution.initial] using state) boundary point decoded
            intended
      have sourceEq : sourceContinuation setup (setup.intendedOpeningProfile source.strategy) 0
          native.config =
            (setup.continuationLaw (setup.intendedOpeningProfile source.strategy)
              (some point)).map some :=
        congrArg (fun point =>
          (setup.continuationLaw (setup.intendedOpeningProfile source.strategy) point).map some)
          decoded
      exact honest_reached_intended_of_readout_law bounds wellFormed source
        certificate start point
        (decodedPoint_staticAt ((decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded))
        intended (sourceLaw.trans sourceEq) fuel history continued control current

end Vegas
