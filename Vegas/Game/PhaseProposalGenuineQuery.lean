/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalHistory
import Vegas.Game.PhaseProposalQuery
import Vegas.Source.ProposalRecoveryVirtualLift

/-! # The actual counted binding input reads a genuine enriched source query -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Keep one chosen native checkpoint through partial commitment replay and
typed virtual repair. The actual enriched source history has the complete
submitted proposal archive, including proposals by authors later excluded.
No source counterpart or archive equality is supplied as a hypothesis. -/
theorem phaseProposalQuery?_genuine_of_counted_binding
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (complete : leaks = MessageNetwork.completePendingObservation)
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.proposalRecoveryProtocol.Trace (some current)),
      ProtocolState.actor setup.program current.point = some who ∧
      who ∉ current.excluded ∧
      instructionCount setup.program - ProtocolState.remaining setup.program current.point =
        event.val ∧
      setup.proposalRecoveryModel.IsDecisionInfo who
        (setup.proposalRecoveryModel.infoOf who sourceTrace) ∧
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who sourceTrace) =
        PhaseProposal.sourceArchive control.execution.network.inputs ∧
      phaseProposalQuery? setup mode runtime leaks plan who event
          (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) =
        some (setup.proposalRecoveryQuery who
          (setup.proposalRecoveryModel.infoOf who sourceTrace)) := by
  obtain ⟨witness, archived⟩ := recoverySourceCheckpoint_proposalArchive_history setup mode runtime
    leaks bounds plan maximal horizon scheduler trace
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨original, current, originalTrace, sourceTrace, actor, rank, _decision, queried,
      preserved, paired, survives⟩ :=
    RecoverySourceCheckpoint.virtual_source_query setup mode runtime leaks plan maximal horizon
      scheduler raw witness.checkpoint witness.aligned witness.chronology who event payload binding
        request
  let inputs := setup.initialLaw.map encodeInputs
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have rawMapped := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler
    counted
  obtain ⟨phase, remaining, installed, kind, _inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler rawMapped
      who event payload binding request.2.2.1
  have full := RecoverySourceCheckpoint.ArchivedProposals.binding runtime leaks bounds plan inputs
    horizon scheduler control counted witness.checkpoint archived phase
      (by rw [installed]; rfl) kind who request.2.2.2.2
  let labels := nativeArchiveLabels setup
    (PhaseProposal.sourceArchive control.execution.network.inputs)
  obtain ⟨lifted, erased, equivalent⟩ := setup.proposalRecovery_virtual_labeled_archive who
    originalTrace sourceTrace paired labels
  have liftedArchive : setup.proposalRecoveryArchive who
      (setup.proposalRecoveryModel.infoOf who lifted) =
        PhaseProposal.sourceArchive control.execution.network.inputs :=
    (equivalent who).trans ((preserved labels who).trans full)
  refine ⟨current, lifted, actor, survives, rank,
    setup.proposalRecovery_isDecisionInfo_of_surviving_actor current lifted who survives actor,
    liftedArchive, ?_⟩
  unfold phaseProposalQuery?
  rw [queried, Option.map_some,
    PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete _ horizon scheduler
      control raw who active]
  unfold Setup.proposalRecoveryQuery
  rw [setup.proposalRecoveryEraseInfo_observed, erased, liftedArchive]

end Vegas
