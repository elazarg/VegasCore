/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryFlags

/-! # Quantitative mass of ordinary proposal-recovery responses -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem map_atom_lower {α β : Type*} (law : PMF α) (map : α → β) (value : α) :
    (law value).toReal ≤ (law.map map (map value)).toReal := by
  classical
  apply ENNReal.toReal_mono ((law.map map).apply_ne_top _)
  rw [PMF.map_apply]
  exact (by simpa only [ite_true] using
    (ENNReal.le_tsum (f := fun source => if map value = map source then law source else 0)
      value))

private theorem bind_atom_lower {α β : Type*} (law : PMF α) (next : α → PMF β)
    (source : α) (target : β) :
    (law source).toReal * (next source target).toReal ≤ (law.bind next target).toReal := by
  rw [← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono ((law.bind next).apply_ne_top _)
  rw [PMF.bind_apply]
  exact ENNReal.le_tsum (f := fun value => law value * next value target) source

theorem proposalRecoverySemanticLaw_value_lower (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information)))
    (value : setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information)) :
    ((1 - omission) * (1 - bad)) * (values value).toReal ≤
      (setup.commitRecoveryValueTremble who (setup.proposalRecoveryEraseInfo who information)
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          values value.1).toReal := by
  have ordinary := map_atom_lower values Subtype.val value
  rw [commitRecoveryValueTremble, mix_apply_toReal]
  have noOmission : 0 ≤ 1 - omission := sub_nonneg.mpr omissionBounded
  have noBad : 0 ≤ 1 - bad := sub_nonneg.mpr badBounded
  have omitted : 0 ≤ omission *
      ((PMF.pure (setup.commitRecoveryFailureChoice who
        (setup.proposalRecoveryEraseInfo who information) true)) value.1).toReal :=
    mul_nonneg omissionNonnegative ENNReal.toReal_nonneg
  split
  · rw [mix_apply_toReal]
    have failed : 0 ≤ bad *
        ((PMF.pure (setup.commitRecoveryFailureChoice who
          (setup.proposalRecoveryEraseInfo who information) false)) value.1).toReal :=
      mul_nonneg badNonnegative ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_left ordinary (mul_nonneg noOmission noBad)]
  · have small : (1 - bad) * (values value).toReal ≤
        ((values.map Subtype.val) value.1).toReal := by
      exact (mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)).trans ordinary
    nlinarith [mul_le_mul_of_nonneg_left small noOmission]

/-- The complete ordinary response floor includes all independent flags.
The domain and label rates are fixed before the bad-preparation hierarchy. -/
theorem proposalRecoveryTrembledLaw_value_lower (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information)))
    (value : setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information)) :
    ((1 - delivery) * (1 - omission) * (1 - bad)) * (values value).toReal ≤
      (setup.proposalRecoveryTrembledLaw who information
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded values
          (setup.proposalRecoveryLabelChoice who information false value.1)).toReal := by
  let semantic := setup.commitRecoveryValueTremble who
    (setup.proposalRecoveryEraseInfo who information)
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded values
  let coin := mix delivery deliveryNonnegative deliveryBounded (PMF.pure true) (PMF.pure false)
  let target := setup.proposalRecoveryLabelChoice who information false value.1
  have labelLower : 1 - delivery ≤
      ((coin.map fun flag => setup.proposalRecoveryLabelChoice who information flag value.1)
        target).toReal := by
    have coinLower := map_atom_lower coin
      (fun flag => setup.proposalRecoveryLabelChoice who information flag value.1) false
    have coinExact : (coin false).toReal = 1 - delivery := by
      simp only [coin, mix_apply_toReal, PMF.pure_apply, Bool.false_eq_true, ite_false,
        ite_true, ENNReal.toReal_zero, ENNReal.toReal_one, mul_zero, mul_one, zero_add]
    rw [coinExact] at coinLower
    exact coinLower
  have branch := bind_atom_lower semantic
    (fun choice => coin.map fun flag =>
      setup.proposalRecoveryLabelChoice who information flag choice) value.1 target
  have domainLower := setup.proposalRecoverySemanticLaw_value_lower who information
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded values value
  have joined := mul_le_mul_of_nonneg_left labelLower
    (ENNReal.toReal_nonneg (a := semantic value.1))
  have domainScaled := mul_le_mul_of_nonneg_left domainLower
    (sub_nonneg.mpr deliveryBounded)
  change _ ≤ (semantic.bind (fun choice => coin.map fun flag =>
    setup.proposalRecoveryLabelChoice who information flag choice) target).toReal
  nlinarith

/-- A caller's domain floor gives a complete ordinary response floor even
when the optimized ordinary distribution assigns that value zero mass. -/
theorem proposalRecoveryTrembledDomainLaw_value_lower
    (finite : setup.program.FiniteBindingTypes) (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (floor : ℝ) (floorNonnegative : 0 ≤ floor) (floorBounded : floor ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information)))
    (value : setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryEraseInfo who information)) :
    ((1 - delivery) * (1 - omission) * (1 - bad)) *
        (floor / Nat.card (setup.CommitRecoveryValueChoice who
          (setup.proposalRecoveryEraseInfo who information))) ≤
      (setup.proposalRecoveryTrembledLaw who information
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded
        (setup.proposalRecoveryDomainLaw finite who information
          floor floorNonnegative floorBounded values)
        (setup.proposalRecoveryLabelChoice who information false value.1)).toReal := by
  have domain := setup.proposalRecoveryDomainLaw_lower finite who information
    floor floorNonnegative floorBounded values value
  have ordinary := setup.proposalRecoveryTrembledLaw_value_lower who information
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    delivery deliveryNonnegative deliveryBounded
    (setup.proposalRecoveryDomainLaw finite who information
      floor floorNonnegative floorBounded values) value
  exact (mul_le_mul_of_nonneg_left domain
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr deliveryBounded)
      (sub_nonneg.mpr omissionBounded)) (sub_nonneg.mpr badBounded))).trans ordinary

end Vegas.SourceProgram.Setup
