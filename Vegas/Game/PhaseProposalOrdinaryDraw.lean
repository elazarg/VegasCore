/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalGenuineQuery
import Vegas.Game.PhaseProposalUnflagged
import Vegas.Source.ProposalRecoveryOrdinaryQuery

/-! # The actual ordinary binding draw on one selected source replay

The checkpoint, partial replay, virtual pair and submitted archive are retained
together. This identifies the literal current draw, not its later admission or
the completed phase law.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- At an actual counted binding callback, the SAME selected checkpoint gives
one original source trace. On its ordinary live-binding branch the actual
unflagged result law is exactly its shared source domain table, with no
arbitrary choice of a source policy inside a hidden information fiber. -/
theorem RecoverySourceWitness.ordinary_binding_draw
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
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (witness : RecoverySourceWitness setup mode plan control.execution.application)
    (archived : witness.checkpoint.ArchivedProposals control.execution.network.inputs)
    (who : Player) (active : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (original : CommitRecoveryState setup.program)
      (originalTrace : setup.commitRecoveryProtocol.Trace (some original)),
      let labels := nativeArchiveLabels setup
        (PhaseProposal.sourceArchive control.execution.network.inputs)
      let lifted := setup.proposalRecoveryLiftTrace labels originalTrace
      setup.proposalRecoveryArchive who
          (setup.proposalRecoveryModel.infoOf who lifted) =
        PhaseProposal.sourceArchive control.execution.network.inputs ∧
      (ProtocolState.BindingsHoldValues who setup.program original.point →
        phaseProposalQuery? setup mode runtime leaks plan who event
            (control.execution.recall who)
            (control.execution.observe (phaseApplication runtime leaks) who) =
          some (setup.proposalRecoveryQuery who
            (setup.proposalRecoveryModel.infoOf who lifted)) ∧
        phaseProposalBindingResults setup mode runtime leaks plan values PhaseProposalRates.zero
            who event payload binding (control.execution.recall who)
            (control.execution.observe (phaseApplication runtime leaks) who) =
          (values who (setup.proposalRecoveryQuery who
            (setup.proposalRecoveryModel.infoOf who lifted))).map
            (fun choice => PublicationResult.success
              (phaseRecoveryDomainValue setup mode event who payload binding choice.val.val))) := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  obtain ⟨original, repaired, originalTrace, repairedTrace, _actor, _rank, _decision, queried,
      preserved, paired, _survives⟩ :=
    RecoverySourceCheckpoint.virtual_source_query setup mode runtime leaks plan maximal horizon
      scheduler raw witness.checkpoint witness.aligned witness.chronology who event payload binding
        request
  let inputs := setup.initialLaw.map encodeInputs
  have counted : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have mapped := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler
    counted
  obtain ⟨phase, remaining, installed, kind, _inside⟩ := phase_ready_binding_phase runtime leaks
    plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler mapped
      who event payload binding request.2.2.1
  have full := RecoverySourceCheckpoint.ArchivedProposals.binding runtime leaks bounds plan inputs
    horizon scheduler control counted witness.checkpoint archived phase
      (by rw [installed]; rfl) kind who request.2.2.2.2
  let labels := nativeArchiveLabels setup
    (PhaseProposal.sourceArchive control.execution.network.inputs)
  let lifted := setup.proposalRecoveryLiftTrace labels originalTrace
  have oldArchive : setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who lifted) =
      PhaseProposal.sourceArchive control.execution.network.inputs :=
    (preserved labels who).trans full
  refine ⟨original, originalTrace, oldArchive, ?_⟩
  intro ordinary
  have normalized := setup.commitRecovery_ordinary_virtual_normalized_info who original repaired
    originalTrace repairedTrace paired ordinary
  have key : phaseProposalQuery? setup mode runtime leaks plan who event
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who) =
      some (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryModel.infoOf who lifted)) := by
    unfold phaseProposalQuery?
    rw [queried, Option.map_some,
      PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete _ horizon scheduler
        control raw who active, normalized]
    unfold Setup.proposalRecoveryQuery
    rw [setup.proposalRecoveryEraseInfo_observed, setup.proposalRecoveryEraseTrace_lift,
      oldArchive]
  refine ⟨key, ?_⟩
  unfold phaseProposalBindingResults
  rw [key]
  simp only [PhaseProposalRates.zero, mix_zero]
  rfl

end Vegas
