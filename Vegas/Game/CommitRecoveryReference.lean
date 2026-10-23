/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryFiniteness
import Mathlib.Probability.Distributions.Uniform

/-! # Full mixing and finite legal histories of the recovery source game -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- A uniform reference exists at every information value, including those
which no execution reaches. It does not resample any initial private inputs. -/
def commitRecoveryReference (finite : setup.program.FiniteBindingTypes) :
    setup.commitRecoveryModel.BehavioralAssessment :=
  .ofStrategy fun who information =>
    let := setup.commitRecovery_finite_choice finite who information
    let := Fintype.ofFinite (setup.commitRecoveryModel.Choice who information)
    let := setup.commitRecovery_choice_nonempty who information
    PMF.uniformOfFintype _

theorem commitRecoveryReference_fullSupport (finite : setup.program.FiniteBindingTypes)
    (who : Player) (information : setup.commitRecoveryModel.InfoState who)
    (choice : setup.commitRecoveryModel.Choice who information) :
    choice ∈ ((setup.commitRecoveryReference finite).strategy who information).support := by
  let := setup.commitRecovery_finite_choice finite who information
  let := Fintype.ofFinite (setup.commitRecoveryModel.Choice who information)
  let := setup.commitRecovery_choice_nonempty who information
  exact PMF.mem_support_uniformOfFintype choice

end Vegas.SourceProgram.Setup
