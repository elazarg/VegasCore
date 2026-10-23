/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryValueTremble

/-! # Original occurrence flags independent of reduced domain tables

Source logical time is public and strictly advances at each instruction.
Counterfactual private queries at the same occurrence share their failure
flags. Domain values remain independent coordinates of the original table.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Omission and accepted source failure are independent, fixed-rate draws. -/
def commitRecoveryFlagLaw
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1) : PMF (Bool × Bool) :=
  (mix omission omissionNonnegative omissionBounded (PMF.pure true) (PMF.pure false)).bind
    fun omitted =>
      (mix bad badNonnegative badBounded (PMF.pure true) (PMF.pure false)).map (Prod.mk omitted)

omit [Fintype Player] in
/-- At a single query the independent occurrence flags and ordinary domain
draw give exactly the original legal three-class source perturbation. -/
theorem commitRecoveryFlagLaw_choice (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who info)) :
    (commitRecoveryFlagLaw omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded).bind
        (fun flags => values.map (setup.commitRecoveryValueFlags who info flags.1 flags.2)) =
      setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values := by
  rw [commitRecoveryFlagLaw, PMF.bind_bind]
  simp only [PMF.bind_map]
  exact setup.commitRecoveryValueFlags_law who info omission omissionNonnegative omissionBounded
    bad badNonnegative badBounded values

end Vegas.SourceProgram.Setup
