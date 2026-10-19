/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalTransition
import Vegas.Game.PhaseProposalExecution
import Vegas.Game.RecoverySurvivingBindingSource
import Vegas.Game.PhaseProposalLabelFrame
import Vegas.Source.ProposalRecoveryLabelCongruence
import Vegas.Source.ProposalRecoveryPrefixRank
import Vegas.Source.ProposalRecoveryMenuKind

/-! # Real responses preserve the already consumed source proposal archive -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The real response may add a live current-phase proposal, but cannot alter
any proposal label of the same already consumed source prefix. No observer
forgets earlier packets, and no proposal is filtered by its author's survival. -/
theorem RecoverySourceWitness.respond_archivedProposals
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode)}
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (execution : (phaseApplication runtime leaks).Execution)
    (witness : RecoverySourceWitness setup mode plan execution.application)
    (prior : witness.checkpoint.ArchivedProposals execution.network.inputs)
    (owner : Player) (response : (phaseApplication runtime leaks).Action) :
    ∃ next : RecoverySourceWitness setup mode plan
        (execution.respond (phaseApplication runtime leaks) owner response).application,
      next.checkpoint.ArchivedProposals
        (execution.respond (phaseApplication runtime leaks) owner response).network.inputs := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨witness, prior⟩
  | some material =>
      let next := witness.submit runtime leaks owner material
      refine ⟨next, ?_⟩
      intro observer active
      let first := PhaseProposal.sourceArchive execution.network.inputs
      let second := PhaseProposal.sourceArchive
        (execution.respond (phaseApplication runtime leaks) owner ⟨some material⟩).network.inputs
      let current := CommitRecoveryState.atPoint
        (witness.checkpoint.residual.lift
          (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source))
        execution.application.entry.excluded execution.application.generation
      have oldActive : observer ∉ execution.application.current.excluded := active
      have sourceActive : observer ∉ current.excluded := by
        intro excluded
        exact oldActive (witness.order.coverage.inherited excluded)
      have filtered := PhaseProposal.sourceArchive_respond_before runtime leaks execution owner
        ⟨some material⟩
      have phaseRank : instructionCount setup.program -
          ProtocolState.remaining setup.program current.point =
            execution.application.attempt.phase :=
        witness.checkpoint.saved_position
      have lifted := setup.proposalRecoveryLiftTrace_eq_of_withheld_labels
        (nativeArchiveLabels setup first) (nativeArchiveLabels setup second)
          witness.checkpoint.trace
        (by
          intro before after priorTrace joint legal supported retained actor move selected revealing
          cases before with
          | none =>
              have offered := legal.2 actor
              rw [selected] at offered
              exact False.elim offered.1
          | some state =>
              have offered := legal.2 actor
              rw [selected] at offered
              obtain ⟨author, name, action⟩ := revealing
              have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal actor
                setup.program state.point move offered.2 ⟨author, name, false, action⟩
              have earlier := setup.proposalRecovery_noncommit_prefix_rank_lt observer state current
                priorTrace witness.checkpoint.trace joint legal supported retained notCommit
                  sourceActive
              apply nativeArchiveLabels_eq_of_earlier setup first second
                execution.application.attempt.phase filtered.symm _ actor state rfl
              exact earlier.2.trans_eq phaseRank)
      have archives := congrArg (fun trace => setup.proposalRecoveryArchive observer
        (setup.proposalRecoveryModel.infoOf observer trace)) lifted
      change setup.proposalRecoveryArchive observer
          (setup.proposalRecoveryModel.infoOf observer
            (setup.proposalRecoveryLiftTrace (nativeArchiveLabels setup second)
              witness.checkpoint.trace)) =
        second.filter (fun proposal => proposal.address.phase < execution.application.attempt.phase)
      exact archives.symm.trans ((prior observer oldActive).trans filtered.symm)

end Vegas
