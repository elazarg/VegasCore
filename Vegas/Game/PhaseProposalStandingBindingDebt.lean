/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCurrentBindingRetention
import Vegas.Game.PhaseProposalBindingWitness
import Vegas.Game.PhaseProposalFreshTerminal
import Vegas.Game.PhaseProposalAttemptArchive
import Vegas.Game.RecoverySameAttemptWitness

/-! # Standing accepted binding failures at the original clean boundary -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual clean dispatcher checkpoints its completed unresolved failure.
The normalizer then follows the same selected intermediate witness, retaining
the original source path and its complete terminal law. -/
theorem RecoverySourceWitness.completed_binding_checkpointDebt
    {setup : Setup (Player := Player) (L := L)} (mode : ExecutionMode)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (witness : RecoverySourceWitness setup mode plan state)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (finished : phase.Finished (phase.drain state.current))
    (clean : ¬ (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty)
    (who : Player)
    (failed : ProtocolState.FailedBinding who setup.program
      (witness.checkpoint.commitResultPoint (phase.drain state.current)))
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    ∃ next : RecoverySourceWitness setup mode plan state.normalize,
      next.CheckpointDebt who ∧
      ∃ intermediate : RecoverySourceWitness setup mode plan
          (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
            state.retired⟩ : PhaseRuntimeState (serviceGraph setup mode)),
        intermediate.checkpoint.residual.lift
            (ProtocolState.entry intermediate.checkpoint.residual.tail
              intermediate.checkpoint.source) =
          witness.checkpoint.commitResultPoint (phase.drain state.current) ∧
        (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
            ⟨_, witness.checkpoint.trace⟩ ⟨_, intermediate.checkpoint.trace⟩ ∧
          setup.recoveryJointRecall intermediate.checkpoint.trace =
            (witness.checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
              setup.recoveryJointRecall witness.checkpoint.trace) ∧
        (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, intermediate.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩) ∧
        setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile
            ⟨_, setup.proposalRecoveryLiftTrace labels intermediate.checkpoint.trace⟩ =
          setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile
            ⟨_, setup.proposalRecoveryLiftTrace labels next.checkpoint.trace⟩ ∧
        witness.checkpoint.ProposalDelta plan intermediate.checkpoint ∧
        intermediate.checkpoint.ProposalDelta plan next.checkpoint := by
  obtain ⟨intermediate, point, path, delta, normalized⟩ :=
    witness.completed_binding_history maximal phase remaining installed kind finished clean
  have owed : intermediate.CheckpointDebt who := by
    refine Or.inr (Or.inr ?_)
    rwa [point]
  obtain ⟨next, ⟨fuel, normalization⟩, law, nextDelta⟩ :=
    intermediate.fresh_normalized_terminal_law mode plan maximal remaining state.generation
      (phase.drain state.current) state.retired certificate profile labels
  have retained := intermediate.checkpointDebt_of_source_reaches who owed next fuel normalization
  rw [normalized]
  exact ⟨next, retained, intermediate, point, path, ⟨fuel, normalization⟩, law, delta,
    nextDelta⟩

/-- A current accepted unusable binding becomes actual checkpoint debt when
the original attempt closes cleanly. The preclosing full witness is retained
at its real location; only its source checkpoint is transferred back to the
initialized callback to read the history-independent failed cell. -/
theorem phaseProposal_current_binding_failure_checkpointed_at_original_close
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current before ending : (phaseApplication runtime leaks).Control)
    (currentTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some current))
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some before))
    (kept : TracePrefix currentTrace prior)
    (same : current.execution.application.attempt = before.execution.application.attempt)
    (witness : RecoverySourceWitness setup mode plan before.execution.application)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : current.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .commitment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : current.execution.application.SeedRequest who
      ⟨current.execution.application.attempt, event⟩)
    (failed : phaseProposalCurrentBindingFailure setup mode runtime leaks who event
      (current.execution.observe (phaseApplication runtime leaks) who))
    (raw : RecoveryState (serviceGraph setup mode))
    (effect : PhaseClosingEffect runtime leaks before.execution ending.execution raw)
    (changed : ending.execution.application.attempt ≠ before.execution.application.attempt)
    (finished : phase.Finished (phase.drain raw))
    (clean : ¬ (((phase.drain raw).excluded \ before.execution.application.entry.excluded) ∩
      phase.owners).Nonempty)
    (normalized : ending.execution.application =
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup mode)).normalize)
    (sourceProfile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner) :
    PhaseCheckpointDebt setup mode plan who ending.execution.application := by
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨draw, _member, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler currentTrace)
  have entry := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
    scheduler current before currentTrace prior kept ordered).2.2 same
  have generation := congrArg CommitAttemptId.generation same
  have offset := congrArg CommitAttemptId.phase same
  let back := witness.checkpoint.transfer (other := current.execution.application) entry
    generation offset
  have phases := (phaseProposal_same_attempt_archive_metadata setup mode runtime leaks bounds
    plan horizon scheduler current before currentTrace prior kept same).1
  have beforeInstalled : before.execution.application.phases = phase :: remaining :=
    phases.trans installed
  obtain ⟨rawWitness, checkpointEq, _rawHistory⟩ :=
    RecoverySourceWitness.raw_closing_checkpoint setup mode runtime leaks plan before ending
      witness raw effect changed
  have member : phase ∈
      ({ before.execution.application with current := raw } :
        PhaseRuntimeState (serviceGraph setup mode)).phases.head? := by
    simp only [beforeInstalled, List.head?_cons, Option.mem_some_iff]
  have receiptOrder := (rawWitness.receipts.ordered phase member kind).congr
    (phase.drain_tables raw).1
  have low : current.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have actualOrder : BindingReceiptOrder current.execution.application.attempt.phase
      current.execution.application.entry.excluded (phase.drain raw).native.accepted := by
    simpa only [low, entry] using receiptOrder
  have progress := PhaseProposal.same_attempt_prefix_keeps_store runtime leaks menu initial
    initialized horizon scheduler current before currentTrace prior kept same
  have rawProgress : KeepsStore before.execution.application.current.native raw.native := by
    rcases effect with ⟨id, message, native, _found, _moved, handled, rfl⟩ |
        ⟨command, native, _moved, supported, rfl⟩
    · exact handle_store_of_some runtime _ native _ handled
    · exact environmentStep_store_of_some runtime _ native command supported
  have preserved : ∀ field value,
      current.execution.application.current.native.config.store field = some value →
        (phase.drain raw).native.config.store field = some value := by
    intro field value present
    exact phase.drain_keepsStore raw field value
      (rawProgress field value (progress field value present))
  have callbackTrace : ((app).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
        horizon scheduler).Trace (some current) := by
    have equal : initial = setup.initialLaw.map
        (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
    exact equal ▸ (menu).toRawTrace initial horizon scheduler currentTrace
  have resultFailure := back.current_binding_failure_in_result setup mode runtime leaks plan
    maximal horizon scheduler callbackTrace phase remaining installed kind who event payload
      binding request failed (phase.drain raw)
        (phase.drain_bindingInvariant raw rawWitness.binding.active) actualOrder
          (fun _selected inside => finished inside) preserved
  have failedResult : ProtocolState.FailedBinding who setup.program
      (rawWitness.checkpoint.commitResultPoint (phase.drain raw)) := by
    have oldFailure : ProtocolState.FailedBinding who setup.program
        (witness.checkpoint.commitResultPoint (phase.drain raw)) := by
      simpa only [back, (witness.checkpoint.transfer_binding_readback entry generation offset
        (phase.drain raw)).1] using resultFailure
    rw [checkpointEq]
    exact (witness.checkpoint.transfer_binding_readback
      (other := { before.execution.application with current := raw })
      rfl rfl rfl (phase.drain raw)).1.symm ▸ oldFailure
  obtain ⟨next, debt, _rest⟩ := rawWitness.completed_binding_checkpointDebt mode plan maximal
    phase remaining beforeInstalled kind finished clean who failedResult
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories sourceProfile (fun _ _ => false)
  rw [normalized]
  exact ⟨next, debt⟩

end Vegas
