/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPerturbation
import GameTheoryExtensions.Analysis.Protocol.SupportedChoiceContinuation

/-! # Future source flags from an arbitrary retained history

Only prospective omission, preparation and proposal-label flags are removed.
The ordinary domain table and the entire initial history, including its actual
proposal labels and failure controls, are retained.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem mix_right_lower {A : Type*} (rate : ℝ)
    (nonnegative : 0 ≤ rate) (bounded : rate ≤ 1) (left right : PMF A) (value : A) :
    (1 - rate) * (right value).toReal ≤
      (mix rate nonnegative bounded left right value).toReal := by
  rw [mix_apply_toReal]
  exact le_add_of_nonneg_left (mul_nonneg nonnegative ENNReal.toReal_nonneg)

private theorem semantic_ordinary_lower (who : Player)
    (information : setup.commitRecoveryModel.InfoState who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who information))
    (choice : setup.commitRecoveryModel.Choice who information) :
    ((1 - omission) * (1 - bad)) * ((values.map Subtype.val) choice).toReal ≤
      (setup.commitRecoveryValueTremble who information
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        values choice).toReal := by
  have noOmission : 0 ≤ 1 - omission := sub_nonneg.mpr omissionBounded
  have inner : (1 - bad) * ((values.map Subtype.val) choice).toReal ≤
      ((if information.1.1.1.elim false (ProtocolView.atCommit who setup.program) then
        mix bad badNonnegative badBounded
          (PMF.pure (setup.commitRecoveryFailureChoice who information false))
          (values.map Subtype.val)
      else values.map Subtype.val) choice).toReal := by
    split
    · exact mix_right_lower bad badNonnegative badBounded _ _ choice
    · exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)
  calc
    _ = (1 - omission) * ((1 - bad) * ((values.map Subtype.val) choice).toReal) := by
      ring
    _ ≤ (1 - omission) *
        ((if information.1.1.1.elim false (ProtocolView.atCommit who setup.program) then
          mix bad badNonnegative badBounded
            (PMF.pure (setup.commitRecoveryFailureChoice who information false))
            (values.map Subtype.val)
        else values.map Subtype.val) choice).toReal :=
      mul_le_mul_of_nonneg_left inner noOmission
    _ ≤ _ := mix_right_lower omission omissionNonnegative omissionBounded _ _ choice

private theorem component_zero (who : Player) (key : setup.ProposalRecoveryComponent who)
    (values : PMF (setup.CommitRecoveryValueChoice who key.1)) :
    setup.proposalRecoveryComponentTrembledLaw who key
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values =
      (values.map Subtype.val).bind (fun choice =>
        PMF.pure (setup.proposalRecoveryComponentLabelChoice who key false choice)) := by
  simp only [proposalRecoveryComponentTrembledLaw, commitRecoveryValueTremble, mix_zero,
    ite_self, PMF.pure_map]

/-- Every ordinary component response retains its explicit no-flag fraction,
including at dirty or indebted information states. -/
theorem proposalRecoveryComponentTrembledLaw_ordinary_lower (who : Player)
    (key : setup.ProposalRecoveryComponent who)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : PMF (setup.CommitRecoveryValueChoice who key.1))
    (choice : setup.ProposalRecoveryComponentChoice who key) :
    ((1 - omission) * (1 - bad) * (1 - delivery)) *
        (setup.proposalRecoveryComponentTrembledLaw who key
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values choice).toReal ≤
      (setup.proposalRecoveryComponentTrembledLaw who key
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded values choice).toReal := by
  rw [setup.component_zero]
  apply bind_supported_domination _ _ _ _ ((1 - omission) * (1 - bad)) (1 - delivery)
    (mul_nonneg (sub_nonneg.mpr omissionBounded) (sub_nonneg.mpr badBounded))
    (fun selected => setup.semantic_ordinary_lower who key.1
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded values selected)
  intro selected _ value
  have lower := mix_right_lower delivery deliveryNonnegative deliveryBounded
    (PMF.pure (setup.proposalRecoveryComponentLabelChoice who key true selected))
    (PMF.pure (setup.proposalRecoveryComponentLabelChoice who key false selected)) value
  simpa only [mix_map, PMF.pure_map] using lower

/-- Normalized source prescriptions keep the same ordinary table when future
flags are removed. This bound is pointwise at every full information value. -/
theorem proposalRecoveryNormalizedTrembledProfile_ordinary_lower
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who)
    (choice : setup.proposalRecoveryModel.Choice who information) :
    ((1 - omission) * (1 - bad) * (1 - delivery)) *
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
          who information choice).toReal ≤
      (setup.proposalRecoveryNormalizedTrembledProfile
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        delivery deliveryNonnegative deliveryBounded values who information choice).toReal := by
  have lower := prob_bind_ge_mul
    (setup.proposalRecoveryComponentTrembledLaw who (setup.proposalRecoveryQuery who information)
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one
      (values who (setup.proposalRecoveryQuery who information)))
    (setup.proposalRecoveryComponentTrembledLaw who (setup.proposalRecoveryQuery who information)
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      (values who (setup.proposalRecoveryQuery who information)))
    ((1 - omission) * (1 - bad) * (1 - delivery))
    (fun selected => setup.proposalRecoveryComponentTrembledLaw_ordinary_lower who
      (setup.proposalRecoveryQuery who information)
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded
      (values who (setup.proposalRecoveryQuery who information)) selected)
    (fun selected => PMF.pure
      ((setup.proposalRecoveryComponentChoice who information).symm selected)) choice
  simpa only [← PMF.bind_pure_comp, Function.comp_def,
    proposalRecoveryNormalizedTrembledProfile, proposalRecoveryPrescribedProfile] using lower

private theorem no_flag_fraction_le_one
    (omission bad delivery : ℝ) (omissionNonnegative : 0 ≤ omission)
    (omissionBounded : omission ≤ 1) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (deliveryNonnegative : 0 ≤ delivery) :
    (1 - omission) * (1 - bad) * (1 - delivery) ≤ 1 := by
  exact (mul_le_of_le_one_right
    (mul_nonneg (sub_nonneg.mpr omissionBounded) (sub_nonneg.mpr badBounded))
    (by linarith)).trans
      ((mul_le_of_le_one_right (sub_nonneg.mpr omissionBounded) (by linarith)).trans
        (by linarith))

private theorem no_flag_error_le
    (omission bad delivery : ℝ) (omissionNonnegative : 0 ≤ omission)
    (omissionBounded : omission ≤ 1) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1) (count : ℕ) :
    1 - ((1 - omission) * (1 - bad) * (1 - delivery)) ^ count ≤
      count * (omission + bad + delivery) := by
  have fractionNonnegative : 0 ≤ (1 - omission) * (1 - bad) :=
    mul_nonneg (sub_nonneg.mpr omissionBounded) (sub_nonneg.mpr badBounded)
  have second : (1 - omission) * bad ≤ bad :=
    mul_le_of_le_one_left badNonnegative (by linarith)
  have third : ((1 - omission) * (1 - bad)) * delivery ≤ delivery :=
    mul_le_of_le_one_left deliveryNonnegative
      ((mul_le_of_le_one_right (sub_nonneg.mpr omissionBounded) (by linarith)).trans
        (by linarith))
  have missing : 1 - (1 - omission) * (1 - bad) * (1 - delivery) ≤
      omission + bad + delivery := by
    calc
      _ = omission + (1 - omission) * bad +
          ((1 - omission) * (1 - bad)) * delivery := by ring
      _ ≤ omission + bad + delivery := by linarith
  exact (one_sub_pow_le_mul
    (mul_nonneg fractionNonnegative (by linarith : 0 ≤ 1 - delivery)) count).trans
      (mul_le_mul_of_nonneg_left missing (Nat.cast_nonneg count))

section Continuations

variable [Fintype Player]

/-- The entire future history law is close from every genuine prefix, with
no division by that prefix's reach and no change to its past labels or debt. -/
theorem proposalRecovery_future_flags_withinTV
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (history : setup.proposalRecoveryProtocol.History) (fuel : Nat) :
    PMF.WithinTV ((Fintype.card Player * fuel : Nat) * (omission + bad + delivery))
      (setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values) fuel history)
      (setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          omission omissionNonnegative omissionBounded bad badNonnegative badBounded
          delivery deliveryNonnegative deliveryBounded values) fuel history) := by
  have close := setup.proposalRecoveryModel.runBehavioralFrom_withinTV_of_supported_choices
    _ _ ((1 - omission) * (1 - bad) * (1 - delivery))
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr omissionBounded) (sub_nonneg.mpr badBounded))
      (sub_nonneg.mpr deliveryBounded))
    (no_flag_fraction_le_one omission bad delivery omissionNonnegative omissionBounded
      badNonnegative badBounded deliveryNonnegative) history
    (fun _ next _ who choice => setup.proposalRecoveryNormalizedTrembledProfile_ordinary_lower
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      delivery deliveryNonnegative deliveryBounded values who
      (setup.proposalRecoveryModel.infoOf who next.trace) choice) fuel
  exact close.mono (no_flag_error_le omission bad delivery omissionNonnegative omissionBounded
    badNonnegative badBounded deliveryNonnegative deliveryBounded (Fintype.card Player * fuel))

end Continuations

end Vegas.SourceProgram.Setup
