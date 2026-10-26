/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingSampleReplay
import Vegas.Compile.EventGraphStep
import Vegas.Source.CommitRecoveryWordMass
import Vegas.Game.SourcePhaseRevealCursor

/-! # Actual phase sampling and original source kernels

The original source draw is shared with the actual native sample command.
Both distributions and actual physical normalization are retained, without
substituting a fixed source policy or an assumed simulation law.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual native sample command couples to one original source sample,
for every source strategy, at any genuine typed source sample cursor. -/
theorem sourcePhase_sample_coupling
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (suffix : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (lift : ProtocolState (.sample name fresh law suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.sample name fresh law suffix) lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (point : current.point = lift (.inl source))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (native : EventGraphRuntime.State (serviceGraph setup mode))
    (agrees : refs.Agrees source.state native.config.store)
    (event : (serviceGraph setup mode).EventId) (ready : native.config.cut.Ready event)
    (output : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode (graphLayout setup.program)) output)
      ((serviceGraph setup mode).nodes event) = .sample payload (compilePublicDist refs law))
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∃ joint : PMF (setup.commitRecoveryProtocol.History ×
        EventGraphRuntime.State (serviceGraph setup mode)),
      joint.map Prod.fst = setup.commitRecoveryModel.runBehavioralFrom
        profile 1 ⟨some current, trace⟩ ∧
      joint.map Prod.snd = environmentStep runtime native (.executeSample event) ∧
      ∀ pair ∈ joint.support, ∃ value ∈ (L.evalDist law (sourcePublicEnv source.state)).support,
        pair.1.state = some (CommitRecoveryState.atPoint
          (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
          current.excluded current.generation) ∧
        TracePrefix trace pair.1.trace ∧
        pair.2 = native.complete event ready
          (cast (congrArg EventField.Action output.symm) PUnit.unit)
          (cast (congrArg EventField.Value output.symm) value) := by
  let history : setup.commitRecoveryProtocol.History := ⟨some current, trace⟩
  let draw := L.evalDist law (sourcePublicEnv source.state)
  let successor := fun value => some (CommitRecoveryState.atPoint
    (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
      current.excluded current.generation)
  have actor : ProtocolState.actor setup.program current.point = none := by
    rw [point, origin.actor_lift]
    rfl
  have notCommit : ProtocolState.atCommit setup.program current.point = false := by
    rw [point, origin.atCommit_lift]
    rfl
  have running : ¬ setup.commitRecoveryProtocol.terminal (some current) := by
    intro stopped
    have zero := (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr
      stopped
    rw [point, origin.remaining_lift] at zero
    change instructionCount suffix + 1 = 0 at zero
    omega
  have inactive : ∀ who, ¬ setup.commitRecoveryProtocol.active (some current) who := by
    intro who active
    change ProtocolState.actor setup.program current.point = some who ∧
      who ∉ current.excluded at active
    rw [actor] at active
    cases active.1
  let legal : setup.commitRecoveryProtocol.Legal (some current) (fun _ => none) :=
    ExecutionProtocol.legal_of_legalOption running inactive
  have sourceStep : setup.commitRecoveryProtocol.step (some current)
      ⟨fun _ => none, legal⟩ = draw.map successor := by
    change (current.step (fun _ => none)).map some = _
    rw [current.step_noncommit_law
      (setup.commitRecovery_blockFrontier trace) notCommit,
      point, origin.recoveryStep_lift]
    simp only [ProtocolState.recoveryStep, Sum.elim_inl, PMF.map_comp, Function.comp_def]
    rfl
  let sourceImage : ∀ value ∈ draw.support, setup.commitRecoveryProtocol.History :=
    fun value supported => history.extend legal (by
      rw [sourceStep]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, supported, rfl⟩)
  let nativeImage := fun value => native.complete event ready
    (cast (congrArg EventField.Action output.symm) PUnit.unit)
    (cast (congrArg EventField.Value output.symm) value)
  let joint := draw.bindOnSupport fun value supported =>
    PMF.pure (sourceImage value supported, nativeImage value)
  have sourceLaw : setup.commitRecoveryModel.runBehavioralFrom profile 1 history =
      draw.bindOnSupport (fun value supported => PMF.pure (sourceImage value supported)) := by
    rw [setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile 0 running,
      setup.commitRecoveryModel.behavioralJoint_eq_pure_of_no_active profile trace running
        inactive, PMF.pure_bind]
    change (setup.commitRecoveryProtocol.step (some current)
      ⟨fun _ => none, legal⟩).bindOnSupport
        (fun target supported => PMF.pure (history.extend legal supported)) = _
    calc
      _ = (draw.map successor).bindOnSupport (fun target supported => PMF.pure
          (history.extend legal (by rw [sourceStep]; exact supported))) := by
        apply bindOnSupport_congr_measure sourceStep
        intro target first second
        rfl
      _ = _ := by rw [bindOnSupport_map]
  have nativeLaw : environmentStep runtime native (.executeSample event) = draw.map nativeImage :=
    by
      rw [environmentStep_executeSample_eq runtime native event ready payload
        (compilePublicDist refs law) output code (nodeView_eq_sample output code),
        sample_step native.config event ready output refs law code source.state agrees,
        PMF.map_comp]
      rfl
  refine ⟨joint, ?_, ?_, ?_⟩
  · change (draw.bindOnSupport _).map Prod.fst = _
    rw [map_bindOnSupport]
    simpa only [PMF.pure_map] using sourceLaw.symm
  · change (draw.bindOnSupport _).map Prod.snd = _
    rw [map_bindOnSupport, nativeLaw]
    simp only [PMF.pure_map]
    rw [PMF.bindOnSupport_eq_bind]
    exact PMF.bind_pure_comp _ _
  · intro pair supported
    obtain ⟨value, member, landed⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp supported
    cases (PMF.mem_support_pure_iff _ _).mp landed
    exact ⟨value, member, rfl, .extend .refl _ _ _, rfl⟩


/-- The full physical execution law retains normalization and environment recall. -/
theorem sourcePhase_sample_application_coupling
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (suffix : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (lift : ProtocolState (.sample name fresh law suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.sample name fresh law suffix) lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (point : current.point = lift (.inl source))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (physical : (phaseApplication runtime leaks).Execution)
    (agrees : refs.Agrees source.state physical.application.current.native.config.store)
    (event : (serviceGraph setup mode).EventId)
    (ready : physical.application.current.native.config.cut.Ready event)
    (output : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode (graphLayout setup.program)) output)
      ((serviceGraph setup mode).nodes event) = .sample payload (compilePublicDist refs law))
    (allowed : physical.application.commandAllowed (.executeSample event) = true)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∃ joint : PMF (setup.commitRecoveryProtocol.History ×
        (phaseApplication runtime leaks).Execution),
      joint.map Prod.fst = setup.commitRecoveryModel.runBehavioralFrom
        profile 1 ⟨some current, trace⟩ ∧
      joint.map Prod.snd = physical.environmentStep (phaseApplication runtime leaks)
        (.application (.executeSample event)) ∧
      ∀ pair ∈ joint.support, ∃ value ∈ (L.evalDist law (sourcePublicEnv source.state)).support,
        pair.1.state = some (CommitRecoveryState.atPoint
          (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
          current.excluded current.generation) ∧
        TracePrefix trace pair.1.trace ∧
        pair.2 = PhaseRuntimeState.normalizeExecution runtime leaks
          (PhaseBindingRepair.rawSample runtime leaks physical event payload output ready
            value) := by
  obtain ⟨localJoint, sourceLaw, nativeLaw, supported⟩ :=
    sourcePhase_sample_coupling setup mode runtime fresh law suffix lift origin source
      current trace point refs physical.application.current.native agrees event ready output code
        profile
  let install := fun native : EventGraphRuntime.State (serviceGraph setup mode) =>
    PhaseRuntimeState.normalizeExecution runtime leaks {
      physical with
      application := { physical.application with
        current := physical.application.current.environmentResult (.executeSample event) native }
      environmentRecall := physical.environmentRecall ++
        [⟨physical.observeEnvironment (phaseApplication runtime leaks),
          .application (.executeSample event)⟩] }
  have actual : (environmentStep runtime physical.application.current.native
      (.executeSample event)).map install =
        physical.environmentStep (phaseApplication runtime leaks)
        (.application (.executeSample event)) := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change _ = (physical.application.environment runtime (.executeSample event)).map _
    rw [PhaseRuntimeState.environment, ite_eq_left allowed, PMF.map_comp]
    rfl
  let joint := localJoint.map fun pair => (pair.1, install pair.2)
  refine ⟨joint, ?_, ?_, ?_⟩
  · simpa only [joint, PMF.map_comp, Function.comp_def] using sourceLaw
  · simpa only [joint, PMF.map_comp, Function.comp_def] using
      (congrArg (PMF.map install) nativeLaw).trans actual
  · intro pair member
    obtain ⟨original, originalSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    subst pair
    obtain ⟨value, valueSupport, state, kept, native⟩ := supported original originalSupport
    refine ⟨value, valueSupport, state, kept, ?_⟩
    rw [native]
    rfl


/-- At an actual initialized raw sequential Nature site, compiler metadata
and the genuine source checkpoint supply the complete shared-draw coupling.
The source profile is arbitrary; no counterpart, source law, or honesty
certificate is supplied by the caller. -/
theorem sourcePhase_sample_application_coupling_of_history
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (serviceGraph setup .sequential))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup .sequential)))
    (plan : RuntimePhasePlan (serviceGraph setup .sequential))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (phase : RuntimePhase (serviceGraph setup .sequential))
    (remaining : List (RuntimePhase (serviceGraph setup .sequential)))
    (installed : control.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .sample)
    (event : (serviceGraph setup .sequential).EventId) (rank : event.val = phase.low)
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∃ (Γ : SourceCtx Player L) (O : Finset VarId) (name : VarId) (payload : L.Ty)
      (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
      (suffix : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
      (lift : ProtocolState (.sample name fresh law suffix) → ProtocolState setup.program)
      (_origin : ProtocolSuffix setup.program (.sample name fresh law suffix) lift)
      (source : SourceProgram.Config Player L Γ)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some current))
      (output : (serviceGraph setup .sequential).outputLayout event = .publicData payload)
      (_code : cast (congrArg (EventCode (graphLayout setup.program)) output)
        ((serviceGraph setup .sequential).nodes event) =
          .sample payload (compilePublicDist refs law))
      (joint : PMF (setup.commitRecoveryProtocol.History ×
        (phaseApplication runtime leaks).Execution)),
      current.point = lift (.inl source) ∧
      current.excluded = control.execution.application.current.excluded ∧
      current.generation = control.execution.application.generation ∧
      refs.Agrees source.state control.execution.application.current.native.config.store ∧
      joint.map Prod.fst = setup.commitRecoveryModel.runBehavioralFrom profile
        1 ⟨some current, sourceTrace⟩ ∧
      joint.map Prod.snd = control.execution.environmentStep (phaseApplication runtime leaks)
        (.application (.executeSample event)) ∧
      ∀ pair ∈ joint.support, ∃ value ∈ (L.evalDist law (sourcePublicEnv source.state)).support,
        pair.1.state = some (CommitRecoveryState.atPoint
          (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
          current.excluded current.generation) ∧
        TracePrefix sourceTrace pair.1.trace ∧
        pair.2 = PhaseRuntimeState.normalizeExecution runtime leaks
          (PhaseBindingRepair.rawSample runtime leaks control.execution event payload output ready
            value) := by
  classical
  let inputs : PMF (serviceGraph setup .sequential).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨checkpoint, _aligned, _chronology, _origins⟩ := recoverySourceCheckpoint_history setup
    .sequential runtime leaks plan maximal horizon scheduler trace
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
    physicalTrace
  have member : phase ∈ control.execution.application.phases.head? := by
    rw [installed]
    exact Option.mem_some_iff.mpr rfl
  have low : phase.low = control.execution.application.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have excluded : control.execution.application.entry.excluded =
      control.execution.application.current.excluded := by
    ext owner
    rw [(exclusion.installed phase member).excluded]
    constructor
    · exact Or.inl
    · rintro (old | ⟨failed, lower, _acting, failure⟩)
      · exact old
      · have upper := ((toEventGraph setup.program).sequentialize_mem_completed_iff_lt_of_ready
          control.execution.application.current.native.config.cut ready).mp failure.completed
        omega
  have agree : checkpoint.refs.Agrees checkpoint.source.state
      control.execution.application.current.native.config.store := checkpoint.current_agrees stored
  have total := checkpoint.compiled.countEq
  have positive : 0 < eventCount checkpoint.residual.tail := by
    have bounded := event.isLt
    change event.val < eventCount setup.program at bounded
    omega
  let selected : Fin (eventCount checkpoint.residual.tail) := ⟨0, positive⟩
  have selectedEq : checkpoint.embedding.event selected = event := by
    apply Fin.ext
    rw [checkpoint.compiled.rankEq, rank, low]
    exact Nat.add_zero _
  have inside : event ∈ phase.events := (phase.mem_events event).mpr
    ⟨rank.ge, by have nonempty := phase.nonempty; omega⟩
  have shape := phase.fields event ((phase.mem_events event).mp inside).1
    ((phase.mem_events event).mp inside).2
  rw [kind] at shape
  obtain ⟨value, output⟩ := shape
  have sourceShape := (checkpoint.embedding.layout_eq selected).symm.trans
    (selectedEq.symm ▸ output)
  have allowed : control.execution.application.commandAllowed (.executeSample event) = true := by
    simp only [PhaseRuntimeState.commandAllowed, installed, List.head?_cons, Option.any_some,
      inside, decide_true]
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, source, refs, registry, embedding, before,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, histories, memories, steps, menus, readout, initialized, views,
    _savedHistory, origin⟩
  dsimp only at positive agree selected selectedEq sourceShape ⊢
  cases program with
  | ret => simp only [eventCount] at positive; omega
  | commit =>
      simp only [selected, outputLayout, Fin.mk_zero, Fin.cases_zero] at sourceShape
      cases sourceShape
  | reveal =>
      simp only [selected, outputLayout, Fin.mk_zero, Fin.cases_zero] at sourceShape
      cases sourceShape
  | @sample _ _ name payload fresh law suffix =>
      have atEvent : ∃ output : (serviceGraph setup .sequential).outputLayout event =
          .publicData payload,
          cast (congrArg (EventCode (graphLayout setup.program)) output)
            ((serviceGraph setup .sequential).nodes event) =
              .sample payload (compilePublicDist refs law) := by
        rw [← selectedEq]
        exact ⟨embedding.layout_eq selected, compiled.nodeEq selected⟩
      obtain ⟨actualOutput, code⟩ := atEvent
      obtain ⟨joint, sourceLaw, nativeLaw, supported⟩ :=
        sourcePhase_sample_application_coupling setup .sequential runtime leaks fresh law suffix
          lift origin source _ initialized rfl refs control.execution agree event ready actualOutput
            code allowed profile
      exact ⟨Γ, O, name, payload, fresh, law, suffix, lift, origin, source, refs, _, initialized,
        actualOutput, code, joint, rfl, excluded, rfl, agree, sourceLaw, nativeLaw, supported⟩

end Vegas
