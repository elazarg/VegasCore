/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Game.PhaseProposalLabels
import Vegas.Pending.PhaseProposalNormalizationFrame

/-! # Proposal increments of the same actual source normalization -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace RecoverySourceCheckpoint

/-- A universally framed consequence of the actual normalization producer.
It computes only newly consumed proposal buckets. The earlier lifted archive
is unrestricted; no global source/native archive correspondence is assumed. -/
def ProposalDelta {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    {before after : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode before)
    (next : RecoverySourceCheckpoint setup mode after) : Prop :=
  ∀ (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
    (bounds : MessageBounds ((toEventGraph setup.program).withMode mode))
    (inputs : PMF ((toEventGraph setup.program).withMode mode).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (anchor : (phaseApplication runtime leaks).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some anchor)),
    PhaseProposal.NormalizationFrame runtime leaks anchor before → ∀ who,
    let archive := PhaseProposal.sourceArchive anchor.execution.network.inputs
    let labels := nativeArchiveLabels setup archive
    setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who
          (setup.proposalRecoveryLiftTrace labels next.trace)) =
      setup.proposalRecoveryArchive who
        (setup.proposalRecoveryModel.infoOf who
          (setup.proposalRecoveryLiftTrace labels checkpoint.trace)) ∪
        archive.filter (fun proposal => before.attempt.phase ≤ proposal.address.phase ∧
          proposal.address.phase < after.attempt.phase)

/-- An unfinished native interval retains the SAME chosen source trace and
has no newly consumed proposal bucket. Live current-phase proposals stay separate. -/
theorem ProposalDelta.of_same_history
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    {before after : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode before)
    (next : RecoverySourceCheckpoint setup mode after)
    (history : (⟨_, checkpoint.trace⟩ : setup.commitRecoveryProtocol.History) = ⟨_, next.trace⟩)
    (phase : after.attempt.phase = before.attempt.phase) : ProposalDelta plan checkpoint next := by
  intro runtime leaks bounds inputs horizon scheduler anchor _trace _frame who
  dsimp only
  let archive := PhaseProposal.sourceArchive anchor.execution.network.inputs
  let labels := nativeArchiveLabels setup archive
  have observed := congrArg (fun prior : setup.commitRecoveryProtocol.History =>
    setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who
      (setup.proposalRecoveryLiftTrace labels prior.trace))) history
  have empty : archive.filter (fun proposal => before.attempt.phase ≤ proposal.address.phase ∧
      proposal.address.phase < after.attempt.phase) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro proposal member
    obtain ⟨_present, lower, upper⟩ := Finset.mem_filter.mp member
    omega
  change _ = _ ∪ archive.filter _
  rw [empty, Finset.union_empty]
  exact observed.symm

/-- Consecutive actual phase advances compose proposal increments. The
frame transformer is purely native origin/entry evidence, not a source-law
premise. In particular the same external submitted-input list is retained. -/
theorem ProposalDelta.trans
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    {before middle after : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode before)
    (next : RecoverySourceCheckpoint setup mode middle)
    (final : RecoverySourceCheckpoint setup mode after)
    (first : ProposalDelta plan checkpoint next) (second : ProposalDelta plan next final)
    (firstPhase : before.attempt.phase ≤ middle.attempt.phase)
    (lastPhase : middle.attempt.phase ≤ after.attempt.phase)
    (frames : ∀ (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode mode))
      (leaks : MessageNetwork.ObservationRule Player
        (CommitAttemptPacket ((toEventGraph setup.program).withMode mode)))
      (anchor : (phaseApplication runtime leaks).Control),
      PhaseProposal.NormalizationFrame runtime leaks anchor before →
        PhaseProposal.NormalizationFrame runtime leaks anchor middle) :
    ProposalDelta plan checkpoint final := by
  intro runtime leaks bounds inputs horizon scheduler anchor trace frame who
  dsimp only
  let archive := PhaseProposal.sourceArchive anchor.execution.network.inputs
  have firstEq := first runtime leaks bounds inputs horizon scheduler anchor trace frame who
  have secondEq := second runtime leaks bounds inputs horizon scheduler anchor trace
    (frames runtime leaks anchor frame) who
  have buckets :
      archive.filter (fun proposal => before.attempt.phase ≤ proposal.address.phase ∧
          proposal.address.phase < middle.attempt.phase) ∪
        archive.filter (fun proposal => middle.attempt.phase ≤ proposal.address.phase ∧
          proposal.address.phase < after.attempt.phase) =
      archive.filter (fun proposal => before.attempt.phase ≤ proposal.address.phase ∧
        proposal.address.phase < after.attempt.phase) := by
    apply Finset.ext
    intro proposal
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨member, lower, upper⟩ | ⟨member, lower, upper⟩)
      · exact ⟨member, lower, lt_of_lt_of_le upper lastPhase⟩
      · exact ⟨member, firstPhase.trans lower, upper⟩
    · rintro ⟨member, lower, upper⟩
      by_cases early : proposal.address.phase < middle.attempt.phase
      · exact Or.inl ⟨member, lower, early⟩
      · exact Or.inr ⟨member, Nat.le_of_not_gt early, upper⟩
  rw [secondEq, firstEq, Finset.union_assoc, buckets]

end RecoverySourceCheckpoint
end Vegas
