/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPreparationSupport

/-! # Positive surrogate responses on full enriched source information -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem preparation_label_reconstruct (who : Player)
    (key : setup.ProposalRecoveryComponent who)
    (choice : setup.ProposalRecoveryComponentChoice who key) :
    setup.proposalRecoveryComponentLabelChoice who key
      ((choice.1.map (·.proposed)).getD false)
      (setup.proposalRecoveryComponentSemanticChoice who key choice) = choice := by
  apply Subtype.ext
  change (choice.1.map (·.semantic)).map
    (fun move => ProposalRecoveryMove.label move ((choice.1.map (·.proposed)).getD false)) =
      choice.1
  have valid := choice.2.2
  cases selected : choice.1 with
  | none => rfl
  | some move =>
      simp only [selected, Option.elim_some] at valid
      simp only [Option.map_some, Option.getD_some,
        ProposalRecoveryMove.label_reconstruct move valid]

/-- Positive delivery and no-delivery labels remain available after only
unusable preparations are removed. This includes observed failed proposals. -/
theorem proposalRecoveryComponentTrembledLaw_prepared_support (who : Player)
    (key : setup.ProposalRecoveryComponent who) (omission delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionSmall : omission.val < 1)
    (deliveryPositive : 0 < delivery.val) (deliverySmall : delivery.val < 1)
    (values : PMF (setup.CommitRecoveryValueChoice who key.1)) (full : FullSupport values)
    (choice : setup.ProposalRecoveryComponentChoice who key)
    (prepared : ¬ ProposalRecoveryMove.GeneratedPreparationFailure choice.val) :
    choice ∈ (setup.proposalRecoveryComponentTrembledLaw who key omission.val omission.property.1
      omission.property.2 0 le_rfl zero_le_one delivery.val delivery.property.1
      delivery.property.2 values).support := by
  have semanticPrepared : ¬ ProposalRecoveryMove.GeneratedPreparationFailure
      ((setup.proposalRecoveryComponentSemanticChoice who key choice).val.map
        ProposalRecoveryMove.ordinary) := by
    intro generated
    apply prepared
    apply (ProposalRecoveryMove.generatedPreparationFailure_ordinary choice.val).mp
    simpa only [proposalRecoveryComponentSemanticChoice, Option.map_map, Function.comp_def] using
      generated
  refine (PMF.mem_support_bind_iff _ _ _).mpr
    ⟨setup.proposalRecoveryComponentSemanticChoice who key choice, ?_, ?_⟩
  · exact setup.commitRecoveryValueTremble_prepared_support who key.1 omission.val
      omissionPositive omissionSmall values full _ semanticPrepared
  · refine (PMF.mem_support_map_iff _ _ _).mpr
      ⟨((choice.1.map (·.proposed)).getD false), ?_,
        setup.preparation_label_reconstruct who key choice⟩
    cases ((choice.1.map (·.proposed)).getD false) with
    | false =>
        exact mem_support_mix_right _ _ _ deliverySmall
          ((PMF.mem_support_pure_iff _ _).mpr rfl)
    | true =>
        exact mem_support_mix_left _ _ _ deliveryPositive
          ((PMF.mem_support_pure_iff _ _).mpr rfl)

/-- The actual full-information surrogate supports every legal prepared
choice at every genuine or ambient source information value. -/
theorem proposalRecoveryNormalizedTrembledProfile_prepared_support
    (omission delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionSmall : omission.val < 1)
    (deliveryPositive : 0 < delivery.val) (deliverySmall : delivery.val < 1)
    (values : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (full : ∀ who key, FullSupport (values who key))
    (who : Player) (information : setup.proposalRecoveryModel.InfoState who)
    (choice : setup.proposalRecoveryModel.Choice who information)
    (prepared : ¬ ProposalRecoveryMove.GeneratedPreparationFailure choice.val) :
    choice ∈ (setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
      omission.property.2 0 le_rfl zero_le_one delivery.val delivery.property.1
      delivery.property.2 values who information).support := by
  unfold proposalRecoveryNormalizedTrembledProfile proposalRecoveryPrescribedProfile
  refine (PMF.mem_support_map_iff _ _ _).mpr
    ⟨setup.proposalRecoveryComponentChoice who information choice, ?_,
      (setup.proposalRecoveryComponentChoice who information).symm_apply_apply choice⟩
  exact setup.proposalRecoveryComponentTrembledLaw_prepared_support who
    (setup.proposalRecoveryQuery who information) omission delivery omissionPositive omissionSmall
    deliveryPositive deliverySmall _ (full who _) _ prepared

end Vegas.SourceProgram.Setup
