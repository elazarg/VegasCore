/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitRecoveryFlagPlan
import Vegas.Game.CommitRecoveryNoMissContinuation

/-! # One initialized occurrence plan realizes the normalized original source

The domain table is the original table on genuine erased source queries.
Actual full-information policies read that same table at the normalized
query. Logical-clock preservation supplies nonrecurrence; the analytical
erased signal model is not used as a recursive normalized information model.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
/-- The selected domain prescription and separate source failure rates are
read at the genuine combined query in the ORIGINAL full source game. -/
def commitRecoveryNormalizedTrembledProfile
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info)) :
    ∀ owner, setup.commitRecoveryModel.BehavioralPolicy owner :=
  setup.commitRecoveryNoMissErasedProfile (fun owner info =>
    setup.commitRecoveryValueTremble owner info omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded (values owner info))

end Vegas.SourceProgram.Setup
