/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalBindingEmission
import Vegas.Game.PhaseProposalOrdinaryDraw

/-! # The literal source table at the frozen entry binding getter -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Keep the supplied checkpoint and its actual source prefix when reading
the frozen-entry graph kernel. The source trace is not chosen afresh after
admission; its erased information, complete controls and proposal archive
determine the ordinary table at this actual callback. -/
theorem RecoverySourceWitness.ordinary_frozen_binding_query
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (complete : leaks = MessageNetwork.completePendingObservation)
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (remaining : Nat) (who : Player)
    (execution anchor : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (witness : RecoverySourceWitness setup mode plan execution.application)
    (archived : witness.checkpoint.ArchivedProposals execution.network.inputs)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (attempt : execution.application.attempt = anchor.application.attempt)
    (retired : execution.application.retired = anchor.application.retired)
    (failures : ∀ rank ≤ execution.application.attempt.phase,
      execution.application.current.native.publicView.sourceFailureFootprint.1 rank =
        anchor.application.current.native.publicView.sourceFailureFootprint.1 rank)
    (archive : PhaseProposal.observedSourceArchive runtime leaks (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who) =
      PhaseProposal.observedSourceArchive runtime leaks (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who
          ((serviceGraph setup mode).playerObserve who
            execution.application.current.native.config))) :
    ∃ (original : CommitRecoveryState setup.program)
      (originalTrace : setup.commitRecoveryProtocol.Trace (some original)),
      let labels := nativeArchiveLabels setup (PhaseProposal.sourceArchive execution.network.inputs)
      let lifted := setup.proposalRecoveryLiftTrace labels originalTrace
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who lifted) =
        PhaseProposal.sourceArchive execution.network.inputs ∧
      (ProtocolState.BindingsHoldValues who setup.program original.point →
        phaseProposalQuery? setup mode runtime leaks plan who event (anchor.recall who)
            (phaseProposalBindingGraphView setup mode runtime leaks anchor who
              ((serviceGraph setup mode).playerObserve who
                execution.application.current.native.config)) =
          some (setup.proposalRecoveryQuery who
            (setup.proposalRecoveryModel.infoOf who lifted)) ∧
        phaseProposalBindingResults setup mode runtime leaks plan values PhaseProposalRates.zero
            who event payload binding (anchor.recall who)
            (phaseProposalBindingGraphView setup mode runtime leaks anchor who
              ((serviceGraph setup mode).playerObserve who
                execution.application.current.native.config)) =
          (values who (setup.proposalRecoveryQuery who
            (setup.proposalRecoveryModel.infoOf who lifted))).map
              (fun choice => PublicationResult.success
                (phaseRecoveryDomainValue setup mode event who payload binding
                  choice.val.val))) := by
  obtain ⟨original, originalTrace, proposed, ordinary⟩ :=
    RecoverySourceWitness.ordinary_binding_draw setup mode runtime leaks complete bounds plan
      maximal values horizon scheduler ⟨remaining, some who, execution⟩ trace witness archived who
        rfl event payload binding request
  have frozen := phaseProposalBindingGraphView_query_eq_current setup mode runtime leaks plan
    anchor execution who event attempt retired failures archive
  refine ⟨original, originalTrace, proposed, ?_⟩
  intro usable
  have current := ordinary usable
  refine ⟨frozen.symm.trans current.1, ?_⟩
  have law := phaseProposalBindingResults_eq_of_query setup mode runtime leaks plan values
    PhaseProposalRates.zero who event payload binding _ _ _ _ frozen
  exact law.symm.trans current.2

end Vegas
