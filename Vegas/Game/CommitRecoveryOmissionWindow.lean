/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNoMissContinuation

/-! # Original commitment-window laws determined by actual omission kernels

Typed choices may differ at every slot. The actual public omission scan is
enough to compare the original finite runners, and an already failed attempt
then has one erased terminal continuation law.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
theorem prefix_excluded
    {before after : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace before)
    (trace : setup.commitRecoveryProtocol.Trace after)
    (kept : TracePrefix prior trace) :
    (setup.commitRecoveryPublic before).1 ⊆ (setup.commitRecoveryPublic after).1 := by
  induction kept with
  | refl => exact Finset.Subset.refl _
  | extend _ joint legal reached ih =>
      exact ih.trans (setup.commitRecovery_step_excluded_subset joint legal reached)

end Vegas.SourceProgram.Setup
