/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryCommitment
import Vegas.Source.ProposalRecoverySupportSplice

/-! # Actual commitment windows emit no proposal disclosures -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryLiftTrace_prefix
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    {first last : setup.commitRecoveryProtocol.State}
    {before : setup.commitRecoveryProtocol.Trace first}
    {after : setup.commitRecoveryProtocol.Trace last} (kept : TracePrefix before after) :
    TracePrefix (setup.proposalRecoveryLiftTrace labels before)
      (setup.proposalRecoveryLiftTrace labels after) := by
  induction kept with
  | refl => exact .refl
  | extend earlier joint legal supported ih => exact .extend ih _ _ _

/-- The existing semantic commitment-window classification applies to every
actual labeled prefix; no choice of proposal flags can disclose a value there. -/
theorem proposalRecoveryProposalOf_eq_none_in_commit_window
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) (kept : TracePrefix prior trace)
    (inside : trace.length + ProtocolState.commitEnd setup.program first.point <
      prior.length + ProtocolState.remaining setup.program first.point)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryProposalOf state joint = none := by
  obtain ⟨current, same, currentCommit, _end, _rank⟩ :=
    setup.commitRecovery_prefix_inside_commit first (setup.proposalRecoveryEraseTrace prior)
      committing (setup.proposalRecoveryEraseTrace trace)
      (setup.proposalRecoveryEraseTrace_prefix kept)
      (by simpa only [setup.proposalRecoveryEraseTrace_length] using inside)
  rw [same]
  exact setup.proposalRecoveryProposalOf_eq_none_of_atCommit current currentCommit joint

/-- The canonical archive is unchanged up to and including commitment close,
regardless of current hidden failures or the ensuing restore. -/
theorem proposalRecoveryArchive_eq_of_commit_window (who : Player)
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) (kept : TracePrefix prior trace)
    (within : trace.length + ProtocolState.commitEnd setup.program first.point ≤
      prior.length + ProtocolState.remaining setup.program first.point) :
    setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who trace) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who prior) := by
  apply setup.proposalRecoveryArchive_eq_of_silent_prefix who prior trace kept
  intro before after middle joint legal supported fromFirst toFinal
  apply setup.proposalRecoveryProposalOf_eq_none_in_commit_window first prior committing
    middle fromFirst _ joint
  have lower := toFinal.length_le
  simp only [Trace.length] at lower
  omega

/-- Silent steps themselves are retained in the actual public word. Their
number is determined by the original trace lengths, including a reset step. -/
theorem proposalRecoveryDeltaRecall_commit_window
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) (kept : TracePrefix prior trace)
    (within : trace.length + ProtocolState.commitEnd setup.program first.point ≤
      prior.length + ProtocolState.remaining setup.program first.point) :
    setup.proposalRecoveryDeltaRecall trace =
      List.replicate (trace.length - prior.length) none ++
        setup.proposalRecoveryDeltaRecall prior := by
  induction kept with
  | refl => simp only [Nat.sub_self, List.replicate_zero, List.nil_append]
  | @extend before after middle kept joint legal supported ih =>
      have inside : middle.length + ProtocolState.commitEnd setup.program first.point <
          prior.length + ProtocolState.remaining setup.program first.point := by
        simp only [Trace.length] at within
        omega
      have silent := setup.proposalRecoveryProposalOf_eq_none_in_commit_window first prior
        committing middle kept inside joint
      have previous : middle.length + ProtocolState.commitEnd setup.program first.point ≤
          prior.length + ProtocolState.remaining setup.program first.point := inside.le
      have difference : (middle.extend joint legal supported).length - prior.length =
          (middle.length - prior.length) + 1 := by
        have lower := kept.length_le
        simp only [Trace.length]
        omega
      rw [proposalRecoveryDeltaRecall, silent, ih previous, difference, List.replicate_succ,
        List.cons_append]

end Vegas.SourceProgram.Setup
