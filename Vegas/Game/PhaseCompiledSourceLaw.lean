/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCompiledRun
import Vegas.Pending.PhaseNativeFrontierLaw
import Vegas.Pending.PhaseNativeInitialRounds
import Vegas.Compile.EventGraphDisclosurePolicy

/-! # Original initialized source laws for the canonical compiled phase policy -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (assessment.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (phaseScheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (values : ∀ event who payload,
    ((serviceGraph setup mode).outputLayout event = .binding who payload ∨
      (serviceGraph setup mode).outputLayout event = .publication payload) →
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "players" => phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
local notation "structural" => setup.decodeBehavioralProfile
  (CommitmentInterface.values setup.program) (setup.openingExtension source)
local notation "copied" => EventGraph.toModeProfile (toEventGraph setup.program) mode
  (compileEventProfile setup.program structural)
local notation "nativeLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "nativeApp" => runtime.reactiveApplication nativeLeaks
local notation "prescribed" => fun who => runtime.prescribedReactivePolicy nativeLeaks who
  (copied who)
local notation "nativeScheduler" => PhaseNativeProjection.nativeScheduler runtime leaks plan
  phaseScheduler

include copies continuing maximal capacity values phaseScheduler

/-- For each supported encoded input, the actual prescribed native run has
its original canonical graph store law. All local matching and frontier
conditions are derived from the concrete canonical phase policy. -/
theorem phaseSourcePolicy_native_initial_store_law
    (safe : ∀ (current : (phaseApplication runtime leaks).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (completes : PhaseService.CompletesPlay runtime leaks
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler)
    (initial : (serviceGraph setup mode).Inputs) (supported : initial ∈ (inputs).support) :
    ((nativeApp).runRounds nativeScheduler prescribed horizon
      (ReactiveApplication.Execution.initial (nativeApp) (State.initial initial))).map
        (fun next => next.application.config.store) =
      ((serviceGraph setup mode).canonicalContinuation copied (Config.initial initial)).map
        (fun key => key.2.1) := by
  exact PhaseNativeProjection.initial_terminal_store_of_physical_safety runtime leaks plan copied
    bounds (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon phaseScheduler
      players (phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment)
        safe (fun current trace clear phaseFaithful nativeFaithful who active =>
          (phaseSourcePolicy_prescribed_of_clear_history setup mode runtime leaks source bounds
            wellFormed assessment copies continuing plan maximal horizon phaseScheduler capacity
              trace clear phaseFaithful nativeFaithful values who active).symm.trans
            (PhaseNativeProjection.nativePolicy_at_clear runtime leaks plan bounds inputs horizon
              phaseScheduler trace clear who (players who)).symm)
        (compiled_openingExtension_readyIndependent setup mode source) completes initial supported

/-- Binding the pointwise store law retains the original source initial draw,
without reconstructing it from its encoding or assuming encoding injectivity. -/
theorem phaseSourcePolicy_native_joint_store_law
    (safe : ∀ (current : (phaseApplication runtime leaks).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (completes : PhaseService.CompletesPlay runtime leaks
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler) :
    setup.initialLaw.bind (fun initial =>
      ((nativeApp).runRounds nativeScheduler prescribed horizon
        (ReactiveApplication.Execution.initial (nativeApp)
          (State.initial (setup.eventInputs initial)))).map
            (fun next => (initial, next.application.config.store))) =
      setup.initialLaw.bind (fun initial =>
        ((serviceGraph setup mode).canonicalContinuation copied
          (Config.initial (setup.eventInputs initial))).map (fun key => (initial, key.2.1))) := by
  apply bind_congr_on_support
  intro initial positive
  have supported : setup.eventInputs initial ∈ (inputs).support := by
    rw [PMF.support_map]
    exact ⟨initial, positive, rfl⟩
  have law := phaseSourcePolicy_native_initial_store_law setup mode runtime leaks source bounds
    wellFormed assessment copies continuing plan maximal horizon phaseScheduler capacity values safe
      completes (setup.eventInputs initial) supported
  have tagged := congrArg (fun distribution => distribution.map (fun store => (initial, store))) law
  simpa only [PMF.map_comp, Function.comp_def] using tagged

/-- The complete source readout and the original initial draw have exactly
their original joint law in the actual prescribed-native execution. -/
theorem phaseSourcePolicy_native_joint_source_law
    (safe : ∀ (current : (phaseApplication runtime leaks).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (completes : PhaseService.CompletesPlay runtime leaks
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler) :
    setup.initialLaw.bind (fun initial =>
      ((nativeApp).runRounds nativeScheduler prescribed horizon
        (ReactiveApplication.Execution.initial (nativeApp)
          (State.initial (setup.eventInputs initial)))).map
            (fun next => (initial, decodeState? (terminalRefs setup.program)
              next.application.config.store))) =
      setup.initialLaw.bind (fun initial =>
        (SourceProgram.run setup.program structural initial).map
          (fun final => (initial, some final))) := by
  have storeLaw := phaseSourcePolicy_native_joint_store_law setup mode runtime leaks source bounds
    wellFormed assessment copies continuing plan maximal horizon phaseScheduler capacity values safe
      completes
  have decoded := congrArg (fun distribution => distribution.map
    (fun pair => (pair.1, decodeState? (terminalRefs setup.program) pair.2))) storeLaw
  rw [PMF.map_bind, PMF.map_bind] at decoded
  simp only [PMF.map_comp, Function.comp_def] at decoded
  rw [decoded]
  apply bind_congr_on_support
  intro initial _
  have projected := congrArg (fun distribution => distribution.map (fun final => (initial, final)))
    (canonicalContinuation_mode_source_decode setup.program structural mode initial)
  simpa only [serviceGraph, Setup.eventGraph, Setup.eventInputs, PMF.map_comp, Function.comp_def]
    using projected

/-- Any realized payoff vector is preserved jointly with the complete typed
source readout and original input, including all of their correlations. -/
theorem phaseSourcePolicy_native_joint_payoff_law
    (safe : ∀ (current : (phaseApplication runtime leaks).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (completes : PhaseService.CompletesPlay runtime leaks
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler)
    (utility : State L setup.context → State L setup.program.terminalCtx → Player → ℝ) :
    setup.initialLaw.bind (fun initial =>
      ((nativeApp).runRounds nativeScheduler prescribed horizon
        (ReactiveApplication.Execution.initial (nativeApp)
          (State.initial (setup.eventInputs initial)))).map (fun next =>
            let final := decodeState? (terminalRefs setup.program) next.application.config.store
            (initial, final, fun who => final.elim 0 (fun state => utility initial state who)))) =
      setup.initialLaw.bind (fun initial =>
        (SourceProgram.run setup.program structural initial).map
          (fun final => (initial, some final, fun who => utility initial final who))) := by
  have law := phaseSourcePolicy_native_joint_source_law setup mode runtime leaks source bounds
    wellFormed assessment copies continuing plan maximal horizon phaseScheduler capacity values safe
      completes
  have projected := congrArg (fun distribution => distribution.map
    (fun pair => (pair.1, pair.2, fun who => pair.2.elim 0
      (fun terminal => utility pair.1 terminal who)))) law
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.elim_some] using projected

/-- Pointwise restriction to each supported original input retains its full
physical/native terminal-store correlation before averaging the original draw. -/
theorem phaseSourcePolicy_physical_native_joint_store_law
    (safe : ∀ (current : (phaseApplication runtime leaks).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅) :
    setup.initialLaw.bind (fun initial =>
      ((phaseApplication runtime leaks).runRounds phaseScheduler players horizon
        (ReactiveApplication.Execution.initial (phaseApplication runtime leaks)
          (PhaseRuntimeState.initial plan (setup.eventInputs initial)))).map
            (fun next => (initial, next.application.current.native.config.store))) =
      setup.initialLaw.bind (fun initial =>
        ((nativeApp).runRounds nativeScheduler prescribed horizon
          (ReactiveApplication.Execution.initial (nativeApp)
            (State.initial (setup.eventInputs initial)))).map
              (fun next => (initial, next.application.config.store))) := by
  apply bind_congr_on_support
  intro initial positive
  have supported : setup.eventInputs initial ∈ (inputs).support := by
    rw [PMF.support_map]
    exact ⟨initial, positive, rfl⟩
  have projected :=
    PhaseNativeProjection.rounds_projection_of_local_agreement_of_supported_input runtime leaks
      plan bounds (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon
        phaseScheduler players prescribed
        (phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment) safe
        (fun current trace clear phaseFaithful nativeFaithful who active =>
          (phaseSourcePolicy_prescribed_of_clear_history setup mode runtime leaks source bounds
            wellFormed assessment copies continuing plan maximal horizon phaseScheduler capacity
              trace clear phaseFaithful nativeFaithful values who active).symm.trans
            (PhaseNativeProjection.nativePolicy_at_clear runtime leaks plan bounds inputs horizon
              phaseScheduler trace clear who (players who)).symm)
        (setup.eventInputs initial) supported
  have tagged := congrArg (fun distribution => distribution.map
    (fun next => (initial, next.application.config.store))) projected
  simpa only [ReactiveApplication.roundsFrom, PMF.pure_map, PMF.pure_bind, PMF.map_comp,
    Function.comp_def, PhaseNativeProjection.execution] using tagged

/-- The actual canonical physical execution preserves the original joint
initial-draw and complete typed source-readout law. The proof restricts actual
histories to each supported input before binding the original initial law. -/
theorem phaseSourcePolicy_physical_joint_source_law
    (safe : ∀ (current : (phaseApplication runtime leaks).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (completes : PhaseService.CompletesPlay runtime leaks
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler) :
    setup.initialLaw.bind (fun initial =>
      ((phaseApplication runtime leaks).runRounds phaseScheduler players horizon
        (ReactiveApplication.Execution.initial (phaseApplication runtime leaks)
          (PhaseRuntimeState.initial plan (setup.eventInputs initial)))).map
            (fun next => (initial, decodeState? (terminalRefs setup.program)
              next.application.current.native.config.store))) =
      setup.initialLaw.bind (fun initial =>
        (SourceProgram.run setup.program structural initial).map
          (fun final => (initial, some final))) := by
  have storeLaw := phaseSourcePolicy_physical_native_joint_store_law setup mode runtime leaks
    source bounds wellFormed assessment copies continuing plan maximal horizon phaseScheduler
      capacity values safe
  have decoded := congrArg (fun distribution => distribution.map
    (fun pair => (pair.1, decodeState? (terminalRefs setup.program) pair.2))) storeLaw
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at decoded
  exact decoded.trans (phaseSourcePolicy_native_joint_source_law setup mode runtime leaks source
    bounds wellFormed assessment copies continuing plan maximal horizon phaseScheduler capacity
      values safe completes)

/-- Realized payoff vectors are preserved jointly with the full source readout
and original initial draw in the actual canonical physical execution. -/
theorem phaseSourcePolicy_physical_joint_payoff_law
    (safe : ∀ (current : (phaseApplication runtime leaks).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace
          (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (completes : PhaseService.CompletesPlay runtime leaks
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler)
    (utility : State L setup.context → State L setup.program.terminalCtx → Player → ℝ) :
    setup.initialLaw.bind (fun initial =>
      ((phaseApplication runtime leaks).runRounds phaseScheduler players horizon
        (ReactiveApplication.Execution.initial (phaseApplication runtime leaks)
          (PhaseRuntimeState.initial plan (setup.eventInputs initial)))).map (fun next =>
            let final := decodeState? (terminalRefs setup.program)
              next.application.current.native.config.store
            (initial, final, fun who => final.elim 0 (fun state => utility initial state who)))) =
      setup.initialLaw.bind (fun initial =>
        (SourceProgram.run setup.program structural initial).map
          (fun final => (initial, some final, fun who => utility initial final who))) := by
  have law := phaseSourcePolicy_physical_joint_source_law setup mode runtime leaks source bounds
    wellFormed assessment copies continuing plan maximal horizon phaseScheduler capacity values safe
      completes
  have projected := congrArg (fun distribution => distribution.map
    (fun pair => (pair.1, pair.2, fun who => pair.2.elim 0
      (fun terminal => utility pair.1 terminal who)))) law
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.elim_some] using projected

end Vegas
