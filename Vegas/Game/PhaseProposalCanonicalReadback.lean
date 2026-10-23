/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalBindingKernel
import Vegas.Source.ProposalRecoveryOrdinaryView

/-! # Source readback at a canonical current binding prefix -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The compiler's typed readback, original public address word and complete
proposal archive identify the literal source query without a synthetic native
history. These are state and trace coordinates, not a likelihood or kernel
equality premise. The selected source trace remains an explicit argument. -/
theorem phaseProposalBindingGraphView_query_of_source_readback
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some anchor))
    (config : (serviceGraph setup mode).Config) (who : Player)
    (event : (serviceGraph setup mode).EventId)
    (current : CommitRecoveryState setup.program)
    (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (survives : who ∉ current.excluded)
    (ordinary : ProtocolState.BindingsHoldValues who setup.program current.point)
    (decoded : decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who event
      ((serviceGraph setup mode).playerStore who config.store) [] =
        some (ProtocolView.eraseHistory who setup.program
          (ProtocolState.observe who setup.program current.point)))
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
      (anchor.execution.application.publicView.sourcePublicAddressWord plan event.val).reverse ++
        [(none, (∅, 0, 0))])
    (proposals : setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who sourceTrace) =
      PhaseProposal.sourceArchive anchor.execution.network.inputs) :
    phaseProposalQuery? setup mode runtime leaks plan who event (anchor.execution.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor.execution who
          ((serviceGraph setup mode).playerObserve who config)) =
      some (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryModel.infoOf who sourceTrace)) := by
  let view := phaseProposalBindingGraphView setup mode runtime leaks anchor.execution who
    ((serviceGraph setup mode).playerObserve who config)
  have typed : phaseVirtualSourceView? setup mode runtime leaks who event view =
      some (ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program current.point)) := by
    dsimp only [view, phaseVirtualSourceView?, phaseProposalBindingGraphView]
    rw [dite_eq_left rfl]
    change (decodeEventView? setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputEmbedding setup.program).ref who event
        ((serviceGraph setup mode).playerStore who config.store) []).map _ = _
    rw [decoded, Option.map_some, ProtocolView.virtualBindings_eraseHistory,
      ProtocolState.virtualBindings_observe_eq who (setup.context.map Prod.fst).toFinset
        setup.program current.point ordinary]
  have read := setup.commitRecovery_erasedInformation_read who current
    (setup.proposalRecoveryEraseTrace sourceTrace) survives
  rw [controls, addresses] at read
  have erasedRead : setup.commitRecoveryErasedRead who
      (ProtocolView.eraseHistory who setup.program
        (ProtocolState.observe who setup.program current.point))
      (setup.commitRecoveryPublic (some current))
      ((setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace sourceTrace)).map
        (setup.commitRecoveryPublicAddress who)) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who
          (setup.proposalRecoveryEraseTrace sourceTrace)) := by
    simpa only [Setup.commitRecoveryErasedRead, ProtocolView.eraseHistory_idempotent,
      ProtocolView.publicPadding_eraseHistory, controls, addresses] using read.symm
  have semantic : phaseVirtualSourceQuery? setup mode runtime leaks plan who event view =
      some (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who
          (setup.commitRecoveryModel.infoOf who
            (setup.proposalRecoveryEraseTrace sourceTrace)))) := by
    unfold phaseVirtualSourceQuery?
    rw [typed, Option.map_some]
    have projected := congrArg (fun information => some
      (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who information))) erasedRead
    simpa only [view, phaseProposalBindingGraphView, controls, addresses,
      PhaseRuntimeState.publicView, ← setup.commitRecoveryNoMissInformation_erased,
      setup.commitRecoveryErasedInformation_idempotent] using projected
  unfold phaseProposalQuery? Setup.proposalRecoveryQuery
  rw [semantic, Option.map_some, setup.proposalRecoveryEraseInfo_observed]
  rw [phaseProposalBindingGraphView_archive setup mode runtime leaks initial horizon scheduler
    anchor anchorTrace who, proposals]

end Vegas
