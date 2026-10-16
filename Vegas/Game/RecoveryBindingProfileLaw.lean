/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryBindingWordPrediction

/-! # The same residual profile at actual ready binding callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The fixed source profile supplied by the checkpoint origin has the actual
nonmissing AUX kernel at the actual filled view. The premise is the structural
raw-step law at ALL residual points, not a target posterior identity. -/
theorem RecoverySourceCheckpoint.binding_kernel_source_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (execution : (phaseApplication runtime leaks).Execution)
    (checkpoint : RecoverySourceCheckpoint setup mode execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (residual : SourceProgram.BehavioralProfile checkpoint.residual.tail)
    (raw : ∀ owner point,
      (residual owner).protocolAction checkpoint.residual.tail
          (ProtocolState.observe owner checkpoint.residual.tail point) =
        (setup.commitRecoveryNonmissingProfile assessment.strategy owner
          (setup.commitRecoveryClearInformation wellFormed owner
            (some (ProtocolState.observe owner setup.program
              (checkpoint.residual.lift point))))).map
                (fun choice => CommitRecoveryMove.underlying choice.1))
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard (later.prepend suffix)) =
      checkpoint.residual.tail)
    (clear : execution.application.entry.excluded = ∅)
    (stored : execution.application.StoredCheckpoint)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : execution.application.current.native.config.cut.Ready
      (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : execution.application.current.native.BindingInvariant) {inputs}
    (reachable : execution.application.current.native.config.Reachable inputs)
    (retained : execution.application.HistoryCheckpoint)
    (saved : execution.application.entry.native.config.cut.IsPrefix
      execution.application.attempt.phase) :
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    let embedding := cast (congrArg
      (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) reconstruct.symm) checkpoint.embedding
    let filled := fillCommitPrefix setup.program earlier
      (.commit name owner fresh guard (later.prepend suffix)) embedding
      execution.application.current.native.config.store checkpoint.source
    let current := earlier.tailProfile
      (.commit name owner fresh guard (later.prepend suffix)) typed
    (commitKernel current (filled.view owner)).map
        (fun result => some (OwnAction.commit owner name payload result)) =
      (setup.commitRecoveryNonmissingProfile assessment.strategy owner
        (setup.commitRecoveryClearInformation wellFormed owner
          (phaseSourceView? setup mode runtime leaks owner (checkpoint.embedding.event selected)
            (execution.observe (phaseApplication runtime leaks) owner)))).map
              (fun choice => CommitRecoveryMove.underlying choice.1) := by
  intro typed embedding filled current
  let point := cast (congrArg ProtocolState reconstruct)
    (earlier.liftPoint (.commit name owner fresh guard (later.prepend suffix))
      (ProtocolState.entry (.commit name owner fresh guard (later.prepend suffix)) filled))
  have localLaw := earlier.binding_kernel_protocolAction fresh guard (later.prepend suffix)
    typed filled
  have castLaw := protocolAction_cast _ _ reconstruct residual owner
    (earlier.liftPoint (.commit name owner fresh guard (later.prepend suffix))
      (ProtocolState.entry (.commit name owner fresh guard (later.prepend suffix)) filled))
  have aligned := checkpoint.filled_prefix_history_of_ready fresh guard (later.prepend suffix)
    earlier reconstruct clear selected atEnd ready acting valid reachable retained saved
  have decoded := checkpoint.filled_prefix_view fresh guard (later.prepend suffix) earlier
    reconstruct stored selected atEnd ready acting notPublication _ aligned
  have actualDecoded : phaseSourceView? setup mode runtime leaks owner
      (checkpoint.embedding.event selected)
        (execution.observe (phaseApplication runtime leaks) owner) = some
      (ProtocolState.observe owner setup.program (checkpoint.residual.lift point)) :=
    (phaseSourceView?_observed setup mode runtime leaks execution owner
      (checkpoint.embedding.event selected)).trans decoded
  exact localLaw.trans (castLaw.trans (by rw [raw, actualDecoded]))

end Vegas
