/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryContinuingExtension

/-! # Exact voluntary-failure probabilities in source recovery approximants -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
theorem commitRecoveryChoice_continues (wellFormed : setup.WellFormed) (who : Player)
    (info : setup.intendedModel.InfoState who) (choice : setup.intendedModel.Choice who info) :
    setup.CommitRecoveryContinues who
      ((setup.commitRecoveryRestriction wellFormed).information who info)
      ((setup.commitRecoveryRestriction wellFormed).choice who info choice).1 := by
  intro move chosen
  have values : ((setup.commitRecoveryRestriction wellFormed).choice who info choice).1 =
      CommitRecoveryMove.lift choice.1 := rfl
  have selected := values.symm.trans chosen
  cases raw : choice.1 with
  | none => rw [raw] at selected; cases selected
  | some action =>
      rw [raw] at selected
      have sameMove : (⟨action, false⟩ : CommitRecoveryMove Player L) = move :=
        Option.some.inj selected
      subst move
      exact ⟨rfl, fun _ => setup.intendedMenu_not_failure who info choice.1
        choice.2 action raw⟩

variable (wellFormed : setup.WellFormed)
  (reference target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    reference target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)

open Classical in
/-- The entire voluntary-failure law at every genuine source site comes from
the same reference tremble. This includes sites outside the intended embedding. -/
theorem commitRecovery_approximation_continuing_law
    (n : ℕ) (who : Player) (site : setup.commitRecoveryModel.InformationSite who) :
    ((approximation.sequence n).strategy who site.1).map
        (fun choice => decide (setup.CommitRecoveryContinues who site.1 choice.1)) =
      mix (approximation.epsilon n) (approximation.positive n).le (approximation.small n).le
        ((reference.strategy who site.1).map
          (fun choice => decide (setup.CommitRecoveryContinues who site.1 choice.1)))
        (PMF.pure true) := by
  let restriction := setup.commitRecoveryRestriction wellFormed
  by_cases retained : restriction.Retained who site.1
  · obtain ⟨original, observed⟩ := retained
    have same : restriction.site who original = site := Subtype.ext observed
    subst site
    obtain ⟨law, mixture⟩ := approximation.retained n who original
    change PMF.map _ ((approximation.sequence n).strategy who
      ((setup.commitRecoveryRestriction wellFormed).information who original.1)) = _
    rw [mixture, mix_map, PMF.map_comp]
    congr 1
    calc
      _ = law.map (fun _ => true) := by
        apply congrArg (fun f => law.map f)
        funext choice
        simp only [Function.comp_apply, decide_eq_true_eq]
        exact setup.commitRecoveryChoice_continues wellFormed who original.1 choice
      _ = _ := PMF.map_const _ _
  · obtain ⟨law, mixture⟩ := approximation.fresh n who site retained
    rw [mixture, mix_map, PMF.map_comp]
    congr 1
    calc
      _ = law.map (fun _ => true) := by
        apply congrArg (fun f => law.map f)
        funext choice
        simp only [Function.comp_apply, decide_eq_true_eq]
        exact choice.2
      _ = _ := PMF.map_const _ _

open Classical in
/-- At every genuine source site the probability of omission or withholding
is at most the common source tremble rate, independently of its posterior. -/
theorem commitRecovery_approximation_failure_probability
    (n : ℕ) (who : Player) (site : setup.commitRecoveryModel.InformationSite who) :
    ((((approximation.sequence n).strategy who site.1).map
      (fun choice => decide (setup.CommitRecoveryContinues who site.1 choice.1))) false).toReal ≤
        approximation.epsilon n := by
  rw [setup.commitRecovery_approximation_continuing_law wellFormed reference target approximation,
    mix_apply_toReal, toReal_pure_apply]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
  calc
    _ ≤ approximation.epsilon n * 1 := mul_le_mul_of_nonneg_left
      (pmf_toReal_apply_le_one _ _) (approximation.positive n).le
    _ = _ := mul_one _

open Classical in
/-- The source omission flag alone has the same uniform upper bound. An
accepted unusable binding without omission is not counted in this probability. -/
theorem commitRecovery_approximation_missing_probability
    (n : ℕ) (who : Player) (site : setup.commitRecoveryModel.InformationSite who) :
    ((((approximation.sequence n).strategy who site.1).map
      (fun choice => choice.1.elim false (·.missing))) true).toReal ≤
        approximation.epsilon n := by
  apply le_trans _ (setup.commitRecovery_approximation_failure_probability
    wellFormed reference target approximation n who site)
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  rw [PMF.map_apply, PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro choice
  by_cases missing : true = choice.1.elim false (·.missing)
  · have notContinues : ¬ setup.CommitRecoveryContinues who site.1 choice.1 := by
      intro continues
      cases selected : choice.1 with
      | none => simp only [selected, Option.elim_none, Bool.true_eq_false] at missing
      | some move =>
          have noMiss := (continues move selected).1
          simp only [selected, Option.elim_some, noMiss, Bool.true_eq_false] at missing
    simp only [missing, notContinues, decide_false, ↓reduceIte]
    exact le_rfl
  · simp only [missing, ↓reduceIte, zero_le]

end Vegas.SourceProgram.Setup
