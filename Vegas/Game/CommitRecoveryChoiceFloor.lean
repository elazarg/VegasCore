/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryReference
import GameTheory.Protocol.FiniteInformation

/-! # A positive source-choice floor over every genuine auxiliary decision -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Finitely many genuine source decisions give one strictly positive floor
for every atom of a fully mixed auxiliary strategy. The floor covers hidden
failed bindings and arbitrary repeated-owner information histories. -/
theorem exists_commitRecovery_choice_floor (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) :
    ∃ floor : ℝ, 0 < floor ∧ floor ≤ 1 ∧
      ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
        (choice : setup.commitRecoveryModel.Choice who site.1),
        floor ≤ (assessment.strategy who site.1 choice).toReal := by
  classical
  let : Finite setup.commitRecoveryProtocol.History := setup.commitRecovery_finite_history finite
  let (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
      Finite (setup.commitRecoveryModel.Choice who info) :=
    setup.commitRecovery_finite_choice finite who info
  let Index := Σ who : Player, Σ site : setup.commitRecoveryModel.InformationSite who,
    setup.commitRecoveryModel.Choice who site.1
  let : Fintype Index := Fintype.ofFinite Index
  let mass : Index → ℝ := fun entry =>
    (assessment.strategy entry.1 entry.2.1.1 entry.2.2).toReal
  have positive (entry : Index) : 0 < mass entry :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp (mixed entry.1 entry.2.1 entry.2.2))
      (PMF.apply_ne_top _ _)
  let floor : ℝ := ∏ entry : Index, min 1 (mass entry)
  have floorPositive : 0 < floor :=
    Finset.prod_pos (fun entry _ => lt_min zero_lt_one (positive entry))
  have floorBounded : floor ≤ 1 :=
    Finset.prod_le_one₀ (fun entry _ => (lt_min zero_lt_one (positive entry)).le)
      (fun _ _ => min_le_left _ _)
  refine ⟨floor, floorPositive, floorBounded, ?_⟩
  intro who site choice
  let selected : Index := ⟨who, site, choice⟩
  have bound := Finset.prod_le_prod_of_subset_of_le_one₀
    (s := {selected}) (t := Finset.univ) (f := fun entry : Index => min 1 (mass entry))
    (Finset.subset_univ _) (fun entry _ => (lt_min zero_lt_one (positive entry)).le)
    (fun _ _ _ => min_le_left _ _)
  have single : floor ≤ min 1 (mass selected) := by
    simpa only [Finset.prod_singleton] using bound
  exact single.trans (min_le_right _ _)

end Vegas.SourceProgram.Setup
