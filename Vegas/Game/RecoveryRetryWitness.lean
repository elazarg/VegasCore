/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalTransition
import Vegas.Game.PhaseProposalExecution

/-! # Full source witnesses at the selected actual retry checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The selected surviving-retry checkpoint carries every witness invariant
and the unchanged physical proposal archive. No endpoint checkpoint is chosen
independently of the supplied failed-attempt path. -/
theorem RecoverySourceWitness.retry_checkpoint_archived_source
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (witness : RecoverySourceWitness setup mode plan state)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (committing : ProtocolState.atCommit witness.checkpoint.residual.tail
      (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source) = true)
    (finished : phase.Finished (phase.drain state.current))
    (missed : (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty)
    (survives : (phase.owners \ (phase.drain state.current).excluded).Nonempty)
    (selected : RecoverySourceCheckpoint setup mode state.normalize)
    {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, witness.checkpoint.trace⟩ ⟨_, selected.trace⟩)
    (instructions : setup.recoveryJointRecall selected.trace =
      (witness.checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
        setup.recoveryJointRecall witness.checkpoint.trace)
    (word : ∀ who, who ∉ (phase.drain state.current).excluded →
      selected.source.history who = witness.checkpoint.source.history who ++
        (decodeHistory setup.program ((phase.drain state.current).native.config.history.map
          ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
            (decodeHistory setup.program (state.entry.native.config.history.map
              ((toEventGraph setup.program).fromModeCompletion mode)) who).length)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some anchor))
    (frame : PhaseProposal.NormalizationFrame runtime leaks anchor state)
    (prior : witness.checkpoint.ArchivedProposals anchor.execution.network.inputs) :
    ∃ next : RecoverySourceWitness setup mode plan state.normalize,
      next.checkpoint = selected ∧
      next.checkpoint.ArchivedProposals anchor.execution.network.inputs ∧
      witness.checkpoint.ProposalDelta plan next.checkpoint := by
  have chain := (plan.suffix_geometry maximal state.phases witness.suffix).2.2
  have member : phase ∈ plan.phases := witness.suffix.subset (by simp only [installed]; simp)
  obtain ⟨aligned, chronology, origins, delta⟩ := witness.checkpoint.retry_phase_archive
    plan phase remaining installed member chain kind committing witness.aligned
      witness.chronology witness.origins witness.exclusions witness.failures witness.archives
        witness.receipts witness.stored witness.remembered finished missed survives selected
          path instructions word
  have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
    (toEventGraph_barrierOrdered setup.program) mode
  obtain ⟨initial, native⟩ := witness.native
  let next : RecoverySourceWitness setup mode plan state.normalize := {
    checkpoint := selected
    aligned := aligned
    chronology := chronology
    origins := origins
    native := ⟨initial, PhaseRuntimeState.settle_invariant _ _ _ _ _ native.saved native.active⟩
    binding := PhaseRuntimeState.settle_bindingRecord _ _ _ _ _
      witness.binding.saved witness.binding.active witness.binding.fixed
    receipts := PhaseRuntimeState.settle_receiptRecord _ _ _ _ _ witness.receipts
    stored := PhaseRuntimeState.settle_storedCheckpoint _ _ _ _ _ witness.stored
    remembered := PhaseRuntimeState.settle_historyCheckpoint _ _ _ _ _ witness.remembered
    order := PhaseRuntimeState.settle_publicFailureOrder graphOrder _ _ _ _ _ witness.order
    suffix := (PhaseRuntimeState.settle_suffix _ _ _ _ _).trans witness.suffix
    archives := PhaseRuntimeState.settle_archivesBefore _ _ _ _ _
      witness.order.frontier.adjacent witness.archives
    exclusions := PhaseRuntimeState.settle_archivedExclusions _ _ _ _ _ witness.exclusions
    failures := PhaseRuntimeState.settle_publicFailureCheckpoint _ _ _ _ _ witness.failures }
  refine ⟨next, rfl, ?_, delta⟩
  exact RecoverySourceCheckpoint.ArchivedProposals.normalize plan witness.checkpoint selected
    runtime leaks bounds inputs horizon scheduler anchor trace frame witness.order.frontier.adjacent
      prior delta

end Vegas
