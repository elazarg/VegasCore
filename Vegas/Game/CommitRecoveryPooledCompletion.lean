/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitRecoveryNormalizedFlagPlan
import GameTheoryExtensions.Analysis.Protocol.ComponentCompletion

/-! # Consistent source assessments with shared normalized domain laws

The original full-information agents share weights at their genuine normalized
queries. Omission, accepted failure and domain floors are fixed before those
weights are selected. Optional pins belong to the shared query, so every member
uses the same pin. Individual incentive bounds require the separate source
ancillary-likelihood and reset arguments.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- A domain reference is fixed independently of any optimized pool weights. -/
def commitRecoveryValueReference (finite : setup.program.FiniteBindingTypes)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    PMF (setup.CommitRecoveryValueChoice who info) := by
  let _ := setup.commitRecoveryValueChoice_finite finite who info
  let _ := Fintype.ofFinite (setup.CommitRecoveryValueChoice who info)
  let _ := setup.commitRecoveryValueChoice_nonempty who info
  exact PMF.uniformOfFintype _

omit [Fintype Player] in
theorem commitRecoveryValueReference_fullSupport (finite : setup.program.FiniteBindingTypes)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    FullSupport (setup.commitRecoveryValueReference finite who info) := by
  let _ := setup.commitRecoveryValueChoice_finite finite who info
  let _ := Fintype.ofFinite (setup.CommitRecoveryValueChoice who info)
  let _ := setup.commitRecoveryValueChoice_nonempty who info
  exact fun _ => PMF.mem_support_uniformOfFintype _

section Played

variable [setup.FiniteInitialLaw] [Fintype setup.commitRecoveryProtocol.History]

end Played

omit [Fintype Player] in
theorem commitRecoveryValueTremble_bind (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    {Part : Type} (weights : PMF Part)
    (values : Part → PMF (setup.CommitRecoveryValueChoice who info)) :
    weights.bind (fun part => setup.commitRecoveryValueTremble who info
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded (values part)) =
      setup.commitRecoveryValueTremble who info omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded (weights.bind values) := by
  simp only [← setup.commitRecoveryFlagLaw_choice, PMF.map_bind]
  exact PMF.bind_comm _ _ _

section Played

variable [setup.FiniteInitialLaw] [Fintype setup.commitRecoveryProtocol.History]

end Played

end Vegas.SourceProgram.Setup
