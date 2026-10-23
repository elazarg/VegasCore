/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySameAttemptWitness
import Vegas.Game.RecoveryRetryWitness

/-! # The selected retry witness at an original raw closing operation -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The original close and its supplied selected retry path produce a full
archived witness at THAT retry checkpoint. The old source word and surviving
own-history extension are the actual bare retry producer's outputs. -/
theorem RecoverySourceWitness.original_retry_archived_source
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before ending : (phaseApplication runtime leaks).Control)
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some before))
    (witness : RecoverySourceWitness setup mode plan before.execution.application)
    (archived : witness.checkpoint.ArchivedProposals before.execution.network.inputs)
    (raw : RecoveryState (serviceGraph setup mode))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup mode)).normalize)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : before.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .commitment)
    (committing : ProtocolState.atCommit witness.checkpoint.residual.tail
      (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source) = true)
    (finished : phase.Finished (phase.drain raw))
    (missed : (((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
      phase.owners).Nonempty)
    (survives : (phase.owners \ (phase.drain raw).excluded).Nonempty) :
    ∀ (selected : RecoverySourceCheckpoint setup mode ending.execution.application) (fuel : Nat),
      setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, witness.checkpoint.trace⟩ ⟨_, selected.trace⟩ →
      setup.recoveryJointRecall selected.trace =
        (witness.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
          setup.recoveryJointRecall witness.checkpoint.trace →
      (∀ owner, owner ∉ (phase.drain raw).excluded →
        selected.source.history owner = witness.checkpoint.source.history owner ++
          (decodeHistory setup.program ((phase.drain raw).native.config.history.map
            ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
              (decodeHistory setup.program
                (before.execution.application.entry.native.config.history.map
                  ((toEventGraph setup.program).fromModeCompletion mode)) owner).length) →
      ∃ next : RecoverySourceWitness setup mode plan ending.execution.application,
        next.checkpoint = selected ∧
          next.checkpoint.ArchivedProposals ending.execution.network.inputs := by
  let state : PhaseRuntimeState (serviceGraph setup mode) :=
    { before.execution.application with current := raw }
  rw [normalized]
  intro selected fuel path instructions word
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
  obtain ⟨rawWitness, rawCheckpoint, rawHistory⟩ :=
    RecoverySourceWitness.raw_closing_checkpoint setup mode runtime leaks plan before ending
      witness raw effect changed
  have sourcePath : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, rawWitness.checkpoint.trace⟩ ⟨_, selected.trace⟩ := by
    rwa [rawHistory]
  have rawInstructions : setup.recoveryJointRecall selected.trace =
      (rawWitness.checkpoint.commitInstructionWord (phase.drain raw).native).reverse ++
        setup.recoveryJointRecall rawWitness.checkpoint.trace := by
    rw [rawCheckpoint]
    exact instructions
  have rawCommitting : ProtocolState.atCommit rawWitness.checkpoint.residual.tail
      (ProtocolState.entry rawWitness.checkpoint.residual.tail rawWitness.checkpoint.source) =
        true := by
    rw [rawCheckpoint]
    exact committing
  have rawWord : ∀ owner, owner ∉ (phase.drain raw).excluded →
      selected.source.history owner = rawWitness.checkpoint.source.history owner ++
        (decodeHistory setup.program ((phase.drain raw).native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) owner).drop
            (decodeHistory setup.program (state.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) owner).length := by
    rw [rawCheckpoint]
    exact word
  have inherited : before.execution.application.current.excluded ⊆ raw.excluded := by
    rcases effect with ⟨id, message, native, _found, _moved, _handled, rfl⟩ |
        ⟨command, native, _moved, _supported, rfl⟩
    · exact before.execution.application.current.inclusionResult_excluded_subset _ _
    · exact before.execution.application.current.environmentResult_excluded_subset _ _
  have rawArchived : rawWitness.checkpoint.ArchivedProposals before.execution.network.inputs := by
    rw [rawCheckpoint]
    intro owner active
    exact archived owner (fun excluded => active (inherited excluded))
  have origins := PhaseProposal.openingOrigins_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler before
      ((menu).toRawTrace initial horizon scheduler prior)
  have frame : PhaseProposal.NormalizationFrame runtime leaks before state := by
    rcases effect with ⟨id, message, native, found, _moved, handled, rawEq⟩ |
        ⟨command, native, _moved, supported, rawEq⟩
    · have present := ((app).retained_envelopes_mem_inputs before.execution
        ((app).history_provenance initial horizon scheduler
          ((menu).toRawTrace initial horizon scheduler prior))
        ((app).history_inputRecall initial horizon scheduler
          ((menu).toRawTrace initial horizon scheduler prior))).lookup id message found
      change PhaseProposal.NormalizationFrame runtime leaks before
        ({ before.execution.application with current := raw } :
          PhaseRuntimeState (serviceGraph setup mode))
      rw [rawEq]
      exact PhaseProposal.NormalizationFrame.inclusion runtime leaks before origins message
        present native handled
    · change PhaseProposal.NormalizationFrame runtime leaks before
        ({ before.execution.application with current := raw } :
          PhaseRuntimeState (serviceGraph setup mode))
      rw [rawEq]
      exact PhaseProposal.NormalizationFrame.environment runtime leaks before origins command
        native supported
  obtain ⟨next, exactCheckpoint, nextArchived, _delta⟩ :=
    rawWitness.retry_checkpoint_archived_source maximal phase remaining installed kind rawCommitting
      finished missed survives selected sourcePath rawInstructions rawWord runtime leaks bounds
        (setup.initialLaw.map encodeInputs) horizon scheduler before prior frame rawArchived
  have sameInputs : ending.execution.network.inputs = before.execution.network.inputs := by
    rcases effect with ⟨id, message, native, _found, moved, _handled, _rawEq⟩ |
        ⟨command, native, moved, _supported, _rawEq⟩
    · exact (app).environmentStep_inputs _ _ (.include id) moved
    · exact (app).environmentStep_inputs _ _ (.application command) moved
  exact ⟨next, exactCheckpoint, sameInputs.symm ▸ nextArchived⟩

end Vegas
