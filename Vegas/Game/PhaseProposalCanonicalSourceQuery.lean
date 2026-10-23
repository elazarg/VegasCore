/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCanonicalReadback

/-! # The canonical binding query from the same compiled source prefix -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
/-- Advanced compiler references read the actual preceding source fields.
Foreign fields beyond that prefix are unrestricted. This uses the existing
typed decoder and residual-view embedding, not an alternative source replay. -/
theorem compiledCommitPrefix_erased_view_of_agrees
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (views : ProtocolViewSuffix setup.program (block.prepend suffix) refs embedding lift)
    (config : (serviceGraph setup mode).Config) (before : SourceProgram.Config Player L Δ)
    (agreement : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      before.state config.store)
    (who : Player) (selected : Fin (eventCount (block.prepend suffix)))
    (atEnd : selected.val = block.length) :
    decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who (embedding.event selected)
        ((serviceGraph setup mode).playerStore who config.store) [] =
      some (ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program
          (lift (block.liftPoint suffix (ProtocolState.entry suffix before))))) := by
  have decoded := decodeObservation?_eq_some
    (commitBlockRefs setup.program block suffix embedding refs) who before.state config.store
      agreement
  have masked : decodeObservation? who (commitBlockRefs setup.program block suffix embedding refs)
      ((toEventGraph setup.program).playerStore who config.store) =
        some (sourceObserve who before.state) :=
    (decodeObservation?_playerStore (graph := toEventGraph setup.program) who
      (commitBlockRefs setup.program block suffix embedding refs) config.store).trans decoded
  have localView := decodeEventView?_commitPrefix_entry setup.program block suffix embedding
    refs ((toEventGraph setup.program).playerStore who config.store) before who selected atEnd
      masked
  have wholeView := (views.decode who selected
    ((toEventGraph setup.program).playerStore who config.store) (before.history who)).trans
      ((congrArg (Option.map (views.view who)) localView).trans
        (congrArg some (views.observe who
          (block.liftPoint suffix (ProtocolState.entry suffix before)))).symm)
  change decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who (embedding.event selected)
      ((toEventGraph setup.program).playerStore who config.store) [] = _
  rw [decodeEventView?_eraseHistory (past := before.history who), wholeView, Option.map_some]

/-- Every consistent canonical prefix reads the key of the explicit source
history extending the selected entry. The ordinary source fields, numeric
controls, full public address word and proposal archive are all retained.
No actual-callback existential is used to choose its probability fiber. -/
theorem phaseProposalBindingGraphView_query_of_compiled_prefix
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some anchor))
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (lift : ProtocolState (block.prepend suffix) → ProtocolState setup.program)
    (views : ProtocolViewSuffix setup.program (block.prepend suffix) refs embedding lift)
    (config : (serviceGraph setup mode).Config) (before : SourceProgram.Config Player L Δ)
    (agreement : (commitBlockRefs setup.program block suffix embedding refs).Agrees
      before.state config.store)
    (who : Player) (selected : Fin (eventCount (block.prepend suffix)))
    (atEnd : selected.val = block.length)
    (current : CommitRecoveryState setup.program)
    (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift (block.liftPoint suffix (ProtocolState.entry suffix before)))
    (survives : who ∉ current.excluded)
    (ordinary : ProtocolState.BindingsHoldValues who setup.program current.point)
    (controls : setup.commitRecoveryPublic (some current) =
      ((anchor.execution.application.publicView.retired.map fun record =>
        record.2.sourceFailureFootprint.2).foldr (fun first last => first ∪ last) ∅ ∪
          anchor.execution.application.current.native.publicView.sourceFailureFootprint.1
            anchor.execution.application.attempt.phase,
        anchor.execution.application.attempt.generation,
        anchor.execution.application.attempt.phase))
    (addresses : (setup.attemptPublicRecall who
        (setup.proposalRecoveryEraseTrace sourceTrace)).map
          (setup.commitRecoveryPublicAddress who) =
      (anchor.execution.application.publicView.sourcePublicAddressWord plan
        (embedding.event selected).val).reverse ++ [(none, (∅, 0, 0))])
    (proposals : setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who sourceTrace) =
      PhaseProposal.sourceArchive anchor.execution.network.inputs) :
    phaseProposalQuery? setup mode runtime leaks plan who (embedding.event selected)
        (anchor.execution.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor.execution who
          ((serviceGraph setup mode).playerObserve who config)) =
      some (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryModel.infoOf who sourceTrace)) := by
  have decoded := compiledCommitPrefix_erased_view_of_agrees setup mode block suffix refs
    embedding lift views config before agreement who selected atEnd
  rw [← point] at decoded
  exact phaseProposalBindingGraphView_query_of_source_readback setup mode runtime leaks plan
    initial horizon scheduler anchor anchorTrace config who (embedding.event selected) current
      sourceTrace survives ordinary decoded controls addresses proposals

end Vegas
