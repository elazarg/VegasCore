/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryPreparationMenuInverse
import Vegas.Game.ProposalRecoveryPerturbation

/-! # Literal generated bad atoms in the actual source prescription -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- One semantic generated bad atom is bounded by its separate preparation
rate, independently of the ordinary value table and all prior reach factors. -/
theorem commitRecoveryValueTremble_generated_atom_le (who : Player)
    (information : setup.commitRecoveryModel.InfoState who)
    (omission bad : Set.Icc (0 : ℝ) 1)
    (values : PMF (setup.CommitRecoveryValueChoice who information))
    (choice : setup.commitRecoveryModel.Choice who information)
    (generated : ProposalRecoveryMove.GeneratedPreparationFailure
      (choice.val.map ProposalRecoveryMove.ordinary)) :
    (setup.commitRecoveryValueTremble who information omission.val omission.property.1
      omission.property.2 bad.val bad.property.1 bad.property.2 values choice).toReal ≤ bad.val
          := by
  classical
  have offered := choice.property
  change setup.commitRecoveryMenu who information choice.val at offered
  cases selected : choice.val with
  | none => simp only [selected, Option.map_none,
      ProposalRecoveryMove.GeneratedPreparationFailure, Option.elim_none] at generated
  | some move =>
      rw [selected] at offered generated
      have facts := ProposalRecoveryMove.generatedPreparationFailure_flags move generated
      have committing : information.1.1.1.elim false
          (ProtocolView.atCommit who setup.program) = true := by
        cases present : information.1.1.1 with
        | none =>
            have impossible : False := by
              simpa only [present, Option.elim_none] using offered.2
            exact impossible.elim
        | some view =>
            exact ProtocolView.atCommit_of_generatedPreparationFailure who setup.program view move
              (by simpa only [present, Option.elim_some] using offered.2) generated
      have different : setup.commitRecoveryFailureChoice who information true ≠ choice := by
        intro equal
        have omitted : (setup.commitRecoveryFailureChoice who information true).val = some move
            := by
          rw [equal]
          exact selected
        have flag := (setup.commitRecoveryFailureChoice_spec who information true move omitted).2
        rw [committing, Bool.true_and] at flag
        exact Bool.noConfusion (flag.symm.trans facts.1)
      have pureZero : ((PMF.pure (setup.commitRecoveryFailureChoice who information true))
          choice).toReal = 0 := by
        simp [PMF.pure_apply, Ne.symm different]
      have ordinaryZero : ((values.map Subtype.val) choice).toReal = 0 := by
        have absent : choice ∉ (values.map Subtype.val).support := by
          intro supported
          obtain ⟨value, _positive, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have chosen : value.val.val = some move := by rw [equal]; exact selected
          exact ((value.property move chosen).2 facts.2).elim
        rw [(PMF.apply_eq_zero_iff _ _).mpr absent]
        rfl
      simp only [commitRecoveryValueTremble, committing, ↓reduceIte]
      rw [mix_apply_toReal, pureZero, mix_apply_toReal, ordinaryZero]
      have bounded : ((PMF.pure (setup.commitRecoveryFailureChoice who information false))
          choice).toReal ≤ 1 := pmf_toReal_apply_le_one _ _
      have nonnegative : 0 ≤ ((PMF.pure
          (setup.commitRecoveryFailureChoice who information false)) choice).toReal :=
        ENNReal.toReal_nonneg
      have inner := mul_le_mul_of_nonneg_left bounded bad.property.1
      have outer := mul_le_mul_of_nonneg_left inner (sub_nonneg.mpr omission.property.2)
      have small : (1 - omission.val) * bad.val ≤ bad.val :=
        mul_le_of_le_one_left bad.property.1 (by linarith [omission.property.1])
      have outerBound : (1 - omission.val) * (bad.val *
          ((PMF.pure (setup.commitRecoveryFailureChoice who information false)) choice).toReal) ≤
          (1 - omission.val) * bad.val := by simpa only [mul_one] using outer
      simpa only [mul_zero, zero_add, zero_mul, add_zero] using outerBound.trans small

private theorem preparation_atom_le_map {A B : Type*} (law : PMF A) (encode : A → B)
    (value : A) : (law value).toReal ≤ ((law.map encode) (encode value)).toReal := by
  classical
  apply ENNReal.toReal_mono ((law.map encode).apply_ne_top _)
  rw [PMF.map_apply]
  simpa only [ite_true] using (ENNReal.le_tsum
    (f := fun source => if encode value = encode source then law source else 0) value)

/-- Proposal-label aggregation can only increase the matching semantic atom.
Thus failed disclosures do not add unaccounted preparation-noise mass. -/
theorem proposalRecoveryComponentTrembledLaw_generated_atom_le (who : Player)
    (key : setup.ProposalRecoveryComponent who) (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (values : PMF (setup.CommitRecoveryValueChoice who key.1))
    (choice : setup.ProposalRecoveryComponentChoice who key)
    (generated : ProposalRecoveryMove.GeneratedPreparationFailure choice.val) :
    (setup.proposalRecoveryComponentTrembledLaw who key omission.val omission.property.1
      omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val delivery.property.1
      delivery.property.2 values choice).toReal ≤ bad.val := by
  have semanticGenerated : ProposalRecoveryMove.GeneratedPreparationFailure
      ((setup.proposalRecoveryComponentSemanticChoice who key choice).val.map
        ProposalRecoveryMove.ordinary) := by
    have transformed :=
      (ProposalRecoveryMove.generatedPreparationFailure_ordinary choice.val).mpr generated
    simpa only [proposalRecoveryComponentSemanticChoice, Option.map_map, Function.comp_def] using
      transformed
  have mapped := preparation_atom_le_map
    (setup.proposalRecoveryComponentTrembledLaw who key omission.val omission.property.1
      omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val delivery.property.1
      delivery.property.2 values)
    (setup.proposalRecoveryComponentSemanticChoice who key) choice
  rw [setup.proposalRecoveryComponentTrembledLaw_semantic] at mapped
  exact mapped.trans (setup.commitRecoveryValueTremble_generated_atom_le who key.1 omission bad
    values _ semanticGenerated)

/-- The actual normalized full-information source choice has the same
atom; no chance or source-hidden-history conditioning enters this estimate. -/
theorem proposalRecoveryNormalizedTrembledProfile_generated_atom_le
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who)
    (choice : setup.proposalRecoveryModel.Choice who information)
    (generated : ProposalRecoveryMove.GeneratedPreparationFailure choice.val) :
    (setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
      omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val delivery.property.1
      delivery.property.2 values who information choice).toReal ≤ bad.val := by
  let component := setup.proposalRecoveryComponentChoice who information choice
  have atom := pmf_map_apply_of_injective
    (setup.proposalRecoveryComponentTrembledLaw who (setup.proposalRecoveryQuery who information)
      omission.val omission.property.1 omission.property.2 bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2
      (values who (setup.proposalRecoveryQuery who information)))
    (setup.proposalRecoveryComponentChoice who information).symm.injective component
  have lower := setup.proposalRecoveryComponentTrembledLaw_generated_atom_le who
    (setup.proposalRecoveryQuery who information) omission bad delivery
    (values who (setup.proposalRecoveryQuery who information)) component generated
  simpa only [proposalRecoveryNormalizedTrembledProfile, proposalRecoveryPrescribedProfile,
    component, Equiv.symm_apply_apply] using (congrArg ENNReal.toReal atom).trans_le lower

end Vegas.SourceProgram.Setup
