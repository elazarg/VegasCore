/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ExclusionMoveExtension

/-! # Failure likelihood in the source completion witness

At a nonexcluded site every residual source law moves. Voluntary failure in
one common fully mixed approximation therefore comes only from its full-menu
reference tremble, with exactly the common tremble multiplier.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Every voluntary failure likelihood is its reference likelihood multiplied
by the common tremble scale, including at newly created information sets. -/
theorem exclusionMoveApproximation_failure_mass (wellFormed : setup.WellFormed)
    {reference target : setup.exclusionModel.BehavioralAssessment}
    (approximation : (setup.exclusionRestriction wellFormed).RestrictedExtensionApproximation
      reference target setup.exclusion_decisionRecall.decisionInformationAntichain
      (fun who info => setup.exclusionMoveRestriction.choice who info))
    (n : ℕ) (who : Player) (site : setup.exclusionModel.InformationSite who)
    (clear : site.1.2 = false) (choice : setup.exclusionModel.Choice who site.1)
    (action : OwnAction Player L) (selected : choice.1 = some action)
    (failure : action.IsFailure) :
    (approximation.sequence n).strategy who site.1 choice =
      ENNReal.ofReal (approximation.epsilon n) * reference.strategy who site.1 choice := by
  classical
  let restriction := setup.exclusionRestriction wellFormed
  by_cases retained : restriction.Retained who site.1
  · obtain ⟨original, observed⟩ := retained
    have same : restriction.site who original = site := Subtype.ext observed
    subst site
    obtain ⟨law, decomposition⟩ := approximation.retained n who original
    have zero : (law.map (restriction.choice who original.1)) choice = 0 := by
      rw [PMF.apply_eq_zero_iff]
      intro supported
      obtain ⟨sourceChoice, _sourceSupported, sameChoice⟩ :=
        (PMF.mem_support_map_iff _ _ _).mp supported
      have values : (restriction.choice who original.1 sourceChoice).1 = sourceChoice.1 := rfl
      exact setup.intendedMenu_not_failure who original.1 sourceChoice.1 sourceChoice.2 action
        (values.symm.trans ((congrArg Subtype.val sameChoice).trans selected)) failure
    calc
      _ = (mix (approximation.epsilon n) (approximation.positive n).le
          (approximation.small n).le
          (reference.strategy who (restriction.information who original.1))
          (law.map (restriction.choice who original.1))) choice :=
        congrArg (fun localLaw => localLaw choice) decomposition
      _ = _ := by
        have computed := congrArg (fun mass : ENNReal =>
          ENNReal.ofReal (approximation.epsilon n) *
              reference.strategy who (restriction.information who original.1) choice +
            ENNReal.ofReal (1 - approximation.epsilon n) * mass) zero
        convert computed using 1
        all_goals simp
  · obtain ⟨law, decomposition⟩ := approximation.fresh n who site retained
    have zero : (law.map (setup.exclusionMoveRestriction.choice who site.1)) choice = 0 := by
      rw [PMF.apply_eq_zero_iff]
      intro supported
      obtain ⟨move, _moveSupported, sameChoice⟩ :=
        (PMF.mem_support_map_iff _ _ _).mp supported
      exact setup.exclusionMove_choice_not_failure who site.1 clear move action
        ((congrArg Subtype.val sameChoice).trans selected) failure
    calc
      _ = (mix (approximation.epsilon n) (approximation.positive n).le
          (approximation.small n).le (reference.strategy who site.1)
          (law.map (setup.exclusionMoveRestriction.choice who site.1))) choice :=
        congrArg (fun localLaw => localLaw choice) decomposition
      _ = _ := by
        have computed := congrArg (fun mass : ENNReal =>
          ENNReal.ofReal (approximation.epsilon n) * reference.strategy who site.1 choice +
            ENNReal.ofReal (1 - approximation.epsilon n) * mass) zero
        convert computed using 1
        all_goals simp

end Vegas.SourceProgram.Setup
