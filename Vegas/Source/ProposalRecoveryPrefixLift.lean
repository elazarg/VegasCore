/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryChronology

/-! # Actual labeled prefixes and lifts of retained semantic suffixes -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Select the literal retained prefix at an actual trace depth. -/
theorem proposalRecovery_prefix_at_depth
    {last : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace last) (depth : Nat)
    (bounded : depth ≤ trace.length) :
    ∃ (first : setup.proposalRecoveryProtocol.State)
      (prior : setup.proposalRecoveryProtocol.Trace first),
      TracePrefix prior trace ∧ prior.length = depth := by
  induction trace with
  | start =>
      have zero : depth = 0 := by simpa only [Trace.length, Nat.le_zero] using bounded
      exact ⟨_, .start, .refl, zero.symm⟩
  | extend earlier joint legal supported ih =>
      by_cases full : depth = (earlier.extend joint legal supported).length
      · exact ⟨_, earlier.extend joint legal supported, .refl, full.symm⟩
      · have lower : depth ≤ earlier.length := by simp only [Trace.length] at *; omega
        obtain ⟨first, prior, retained, length⟩ := ih lower
        exact ⟨first, prior, retained.extend joint legal supported, length⟩

/-- A literal semantic prefix of an erased labeled trace is the erasure of
an actual labeled prefix, with all its original labels retained. -/
theorem proposalRecoveryEraseTrace_prefix_inverse
    {last : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace last)
    {first : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace first)
    (kept : TracePrefix prior (setup.proposalRecoveryEraseTrace trace)) :
    ∃ labeled : setup.proposalRecoveryProtocol.Trace first,
      TracePrefix labeled trace ∧ setup.proposalRecoveryEraseTrace labeled = prior := by
  obtain ⟨state, labeled, retained, length⟩ :=
    setup.proposalRecovery_prefix_at_depth trace prior.length (by
    simpa only [setup.proposalRecoveryEraseTrace_length] using kept.length_le)
  have same := (setup.proposalRecoveryEraseTrace_prefix retained).eq_of_same_length kept (by
    simpa only [setup.proposalRecoveryEraseTrace_length] using length)
  have states : state = first := congrArg History.state same
  subst first
  have projected : setup.proposalRecoveryEraseTrace labeled = prior := by
    exact eq_of_heq (History.mk.inj same).2
  exact ⟨labeled, retained, projected⟩

end Vegas.SourceProgram.Setup
