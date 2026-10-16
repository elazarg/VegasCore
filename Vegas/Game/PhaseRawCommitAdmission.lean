/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitPrefixAdmission
import Vegas.Game.RecoverySettledCommitCheckpoint
import Vegas.Pending.PhasePlanSuffix

/-! # Admission of completed raw commitment images at their real source checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

include source copies maximal

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- A finished native image is admitted at the same saved source checkpoint.
All image facts are physical invariants; source admission is reconstructed from
the actual earlier policy draws, without assigning a trace to the image. -/
theorem phase_finished_commit_admitted
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (image : RecoveryState (serviceGraph setup mode))
    (imageClear : image.excluded = ∅) (imageCoverage : image.FailureCoverage)
    (imageBindings : image.native.BindingInvariant)
    (results : ∀ handle payload, image.native.bindingResult handle payload =
      control.execution.application.current.native.bindingResult handle payload)
    (stamped : BindingStamp (fun owner => (app).outputs (control.execution.recall owner))
      control.execution.application.attempt image.native)
    (preserved : KeepsStore control.execution.application.current.native image.native)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : control.execution.application.phases = phase :: remaining)
    (finished : phase.Finished image)
    (consistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))) :
    checkpoint.commitAdmitted image := by
  let fixed := checkpoint
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have frontier := (phaseApplication_frontier runtime leaks).history initial horizon scheduler (by
    intro state positive
    obtain ⟨draw, _positive, rfl⟩ := PMF.support_map .. ▸ positive
    exact PhaseRuntimeState.initial_frontier plan draw) raw
  have adjacent := frontier.adjacent
  have last := frontier.last
  have currentMaximal := (phasePlanGeometry_history runtime leaks plan maximal inputs horizon
    scheduler raw).2.2
  rcases checkpoint with ⟨⟨Γ, O, program, lift⟩, sourceEntry, refs, registry, embedding, beforeCut,
    compiled, terminalAlignment, agrees, guards, failures, unique, ranks, actors, commits, owners,
    endpoints, automatic, sourceHistories, memories, steps, menus, readout, initializedSource,
    views, savedHistory, origin⟩
  dsimp only [RecoverySourceCheckpoint.commitAdmitted]
  generalize _decomposition : commitPhase program = segment at ⊢
  rcases segment with ⟨Δ, P, suffix, block, reconstruct, boundary⟩
  subst program
  have positive : 0 < block.length := by
    cases block with
    | nil =>
        cases suffix with
        | ret => cases committing
        | sample => cases committing
        | reveal => cases committing
        | commit => cases boundary
    | commit => simp only [SourceProgram.CommitPrefix.length]; omega
  have low : phase.low = control.execution.application.attempt.phase := by
    rw [PhaseRuntimeState.attempt, installed]
    rfl
  rw [installed] at adjacent last currentMaximal
  have phaseEq := compiledCommitPhase_eq_of_maximal setup.program mode block suffix embedding
    compiled positive boundary phase remaining adjacent last currentMaximal low
  subst phase
  intro who
  apply phase_commitPrefix_image_admitted setup mode runtime leaks bounds wellFormed source
    assessment copies plan inputs horizon scheduler trace clear fixed block suffix rfl who
      (consistent who) savedIntended image imageClear imageCoverage imageBindings results stamped
        preserved
  dsimp only
  intro index inside _owned
  exact finished ((compiledCommitPhase_mem_iff setup.program mode block suffix embedding
    compiled positive _).mpr ⟨index, inside, rfl⟩)

/-- Actual native inclusion supplies all physical image premises internally.
The accepted completion may be the last cell that immediately closes its phase. -/
theorem phase_handle_commit_admitted
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (message : Message Player (CommitAttemptPacket (serviceGraph setup mode)))
    (authentic : message ∈ control.execution.network.inputs)
    (current : message.payload.attempt = control.execution.application.attempt)
    (native : EventGraphRuntime.State (serviceGraph setup mode))
    (accepted : EventGraphRuntime.handle runtime control.execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native)
    (imageClear : (control.execution.application.current.inclusionResult
      message.payload.packet.call native).excluded = ∅)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : control.execution.application.phases = phase :: remaining)
    (consistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (finished : phase.Finished (control.execution.application.current.inclusionResult
      message.payload.packet.call native)) :
    checkpoint.commitAdmitted (control.execution.application.current.inclusionResult
      message.payload.packet.call native) := by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw
  have stamped := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw
  have issued := ((app).history_provenance initial horizon scheduler raw).inputs message authentic
  exact phase_finished_commit_admitted setup mode runtime leaks bounds wellFormed source assessment
    copies plan maximal inputs horizon scheduler trace clear checkpoint _ imageClear
      (coverage.active.inclusionResult runtime _ native accepted)
      (handle_bindingInvariant runtime _ native _ bindings.active accepted)
      (raw_handle_bindingResult runtime _ native _ accepted)
      (raw_handle_bindingStamp runtime leaks control.execution native message stamped issued
        current accepted)
      (handle_store_of_some runtime _ native _ accepted) committing phase remaining installed
      finished consistent savedIntended

/-- Actual environment completion likewise retains the old checkpoint's
admitted filled image before any normalization or checkpoint replacement. -/
theorem phase_environment_commit_admitted
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (checkpoint : RecoverySourceCheckpoint setup mode control.execution.application)
    (command : EnvironmentCommand (serviceGraph setup mode))
    (native : EventGraphRuntime.State (serviceGraph setup mode))
    (reached : native ∈ (environmentStep runtime
      control.execution.application.current.native command).support)
    (imageClear : (control.execution.application.current.environmentResult
      command native).excluded = ∅)
    (committing : ProtocolState.atCommit checkpoint.residual.tail
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : control.execution.application.phases = phase :: remaining)
    (consistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
      who).Consistent (control.execution.recall who))
    (savedIntended : ProtocolState.Intended setup.program
      (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (finished : phase.Finished (control.execution.application.current.environmentResult
      command native)) :
    checkpoint.commitAdmitted (control.execution.application.current.environmentResult
      command native) := by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw
  have stamped := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw
  have tables := environmentStep_tables runtime control.execution.application.current.native
    native command reached
  apply phase_finished_commit_admitted setup mode runtime leaks bounds wellFormed source assessment
    copies plan maximal inputs horizon scheduler trace clear checkpoint _ imageClear
      (coverage.active.environmentResult runtime command native reached)
      (environmentStep_bindingInvariant runtime _ native command bindings.active reached)
      _ (stamped.copy tables.1) (environmentStep_store_of_some runtime _ native command reached)
      committing phase remaining installed finished consistent savedIntended
  intro handle payload
  change native.bindingResult handle payload = _
  unfold EventGraphRuntime.State.bindingResult
  rw [tables.2]

end Vegas
