/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPreparationDomination
import Vegas.Game.ProposalRecoveryPreparationSupportProfile

/-! # A fixed source response floor before bad noise and pooled optimization -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

local notation "E" => Setup.proposalRecoveryProtocol setup
local notation "N" => Setup.proposalRecoveryModel setup

open Classical in
/-- The minimum ranges over ALL intrinsic actual source histories and legal
prepared choices, not just those reached by a selected optimized profile. -/
theorem exists_proposalRecoveryPreparation_response_floor
    (finite : setup.program.FiniteBindingTypes)
    (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1)
    (omission delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionSmall : omission.val < 1)
    (deliveryPositive : 0 < delivery.val) (deliverySmall : delivery.val < 1) :
    ∃ lower : ℝ, 0 < lower ∧ lower ≤ 1 ∧
      ∀ (bad : Set.Icc (0 : ℝ) 1), bad.val ≤ 1 / 2 →
      ∀ (pins : (pool : setup.ProposalRecoveryValuePool) →
          Option (PMF (setup.ProposalRecoveryPoolPart pool)))
        (weights : (pool : setup.ProposalRecoveryValuePool) →
          PMF (setup.ProposalRecoveryPoolPart pool))
        (who : Player) (history : (E).History)
        (choice : (N).Choice who ((N).infoOf who history.trace)),
      ¬ ProposalRecoveryMove.GeneratedPreparationFailure choice.val →
      lower ≤ (setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
        omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val delivery.property.1
        delivery.property.2
        (setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded pins
            weights)
        who ((N).infoOf who history.trace) choice).toReal := by
  classical
  let _ := Fintype.ofFinite Player
  let values := fun who (key : setup.ProposalRecoveryComponent who) =>
    setup.commitRecoveryValueReference finite who key.1
  let surrogate := setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
    omission.property.2 0 le_rfl zero_le_one delivery.val delivery.property.1 delivery.property.2
        values
  let atoms (who : Player) (history : (E).History) : Finset ℝ :=
    let _ := setup.proposalRecovery_finite_choice finite who ((N).infoOf who history.trace)
    let _ := Fintype.ofFinite ((N).Choice who ((N).infoOf who history.trace))
    (Finset.univ.filter fun choice : (N).Choice who ((N).infoOf who history.trace) =>
      ¬ ProposalRecoveryMove.GeneratedPreparationFailure choice.val).image fun choice =>
        (surrogate who ((N).infoOf who history.trace) choice).toReal
  let probabilities := insert (1 : ℝ) (Finset.univ.biUnion fun who : Player =>
    Finset.univ.biUnion fun history : (E).History => atoms who history)
  have nonempty : probabilities.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let minimum := probabilities.min' nonempty
  have minimumPositive : 0 < minimum := by
    change 0 < probabilities.min' nonempty
    have present := Finset.min'_mem probabilities nonempty
    rcases Finset.mem_insert.mp present with one | ordinary
    · rw [one]
      exact zero_lt_one
    · obtain ⟨who, _included, ordinary⟩ := Finset.mem_biUnion.mp ordinary
      obtain ⟨history, _included, ordinary⟩ := Finset.mem_biUnion.mp ordinary
      obtain ⟨choice, offered, same⟩ := Finset.mem_image.mp ordinary
      have prepared := (Finset.mem_filter.mp offered).2
      have supported := setup.proposalRecoveryNormalizedTrembledProfile_prepared_support
        omission delivery omissionPositive omissionSmall deliveryPositive deliverySmall values
        (fun owner key => setup.commitRecoveryValueReference_fullSupport finite owner key.1)
        who ((N).infoOf who history.trace) choice prepared
      rw [← same]
      exact pmf_toReal_pos_iff.mpr supported
  have minimumBounded : minimum ≤ 1 := Finset.min'_le probabilities _
    (Finset.mem_insert_self _ _)
  have minimumAt (who : Player) (history : (E).History)
      (choice : (N).Choice who ((N).infoOf who history.trace))
      (prepared : ¬ ProposalRecoveryMove.GeneratedPreparationFailure choice.val) :
      minimum ≤ (surrogate who ((N).infoOf who history.trace) choice).toReal := by
    let _ := setup.proposalRecovery_finite_choice finite who ((N).infoOf who history.trace)
    let _ := Fintype.ofFinite ((N).Choice who ((N).infoOf who history.trace))
    apply Finset.min'_le probabilities _
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨who, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
    refine ⟨history, Finset.mem_univ _, ?_⟩
    dsimp only [atoms]
    exact Finset.mem_image.mpr ⟨choice, Finset.mem_filter.mpr ⟨Finset.mem_univ _, prepared⟩, rfl⟩
  let lower := (floor / 2) * minimum
  have lowerPositive : 0 < lower := mul_pos (by positivity) minimumPositive
  have lowerBounded : lower ≤ 1 := by
    have first := mul_le_mul_of_nonneg_left minimumBounded (show 0 ≤ floor / 2 by positivity)
    dsimp only [lower]
    nlinarith
  refine ⟨lower, lowerPositive, lowerBounded, ?_⟩
  intro bad badSmall pins weights who history choice prepared
  let target := setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded
    pins weights
  have domain (owner : Player) (key : setup.ProposalRecoveryComponent owner)
      (value : setup.CommitRecoveryValueChoice owner key.1) :
      floor * (values owner key value).toReal ≤ (target owner key value).toReal := by
    dsimp only [target, proposalRecoveryPooledDomainLaw]
    rw [mix_apply_toReal]
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr floorBounded) ENNReal.toReal_nonneg)
  have actual := setup.proposalRecoveryNormalizedTrembledProfile_preparation_domination
    omission bad delivery values target floor floorPositive.le floorBounded domain who
      ((N).infoOf who history.trace) choice
  have factor : floor / 2 ≤ (1 - bad.val) * floor := by
    have half : (1 : ℝ) / 2 ≤ 1 - bad.val := by linarith
    have weighted := mul_le_mul_of_nonneg_right half floorPositive.le
    nlinarith [weighted]
  calc
    lower ≤ (floor / 2) * (surrogate who ((N).infoOf who history.trace) choice).toReal :=
      mul_le_mul_of_nonneg_left (minimumAt who history choice prepared) (by positivity)
    _ ≤ ((1 - bad.val) * floor) *
        (surrogate who ((N).infoOf who history.trace) choice).toReal :=
      mul_le_mul_of_nonneg_right factor ENNReal.toReal_nonneg
    _ ≤ _ := actual

end Vegas.SourceProgram.Setup
