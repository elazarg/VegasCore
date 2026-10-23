/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPreparationFloor
import Vegas.Game.ProposalRecoveryPreparationWord
import Vegas.Game.ProposalRecoveryPreparationLikelihood
import Vegas.Source.ProposalRecoveryPreparationRepairHistory
import GameTheoryExtensions.Analysis.Protocol.ProjectedBeliefTransport

/-! # Past foreign source preparation failures at full enriched information

The source game and original joint prior are fixed first. A selective actual
history repair retains the entire observer input, so only the designated
owner's generated bad atom is charged in the posterior estimate.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  [Fintype setup.proposalRecoveryProtocol.History]

local notation "protocol" => Setup.proposalRecoveryProtocol setup
local notation "model" => Setup.proposalRecoveryModel setup

open Classical in
/-- The response floor precedes the bad rate, source pins and free weights.
The conclusion is uniform at every positive FULL genuine source input. -/
theorem exists_proposalRecovery_generatedPreparation_posterior_bound
    (finite : setup.program.FiniteBindingTypes) :
    ∃ (chance : ℝ) (length : Nat), 0 < chance ∧ chance ≤ 1 ∧
      ∀ (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1),
      ∀ (omission delivery : Set.Icc (0 : ℝ) 1),
        0 < omission.val → omission.val < 1 → 0 < delivery.val → delivery.val < 1 →
      ∃ lower : ℝ, 0 < lower ∧ lower ≤ 1 ∧
        ∀ (bad : Set.Icc (0 : ℝ) 1), 0 < bad.val → bad.val ≤ 1 / 2 →
        ∀ (pins : (pool : setup.ProposalRecoveryValuePool) →
            Option (PMF (setup.ProposalRecoveryPoolPart pool)))
          (weights : (pool : setup.ProposalRecoveryValuePool) →
            PMF (setup.ProposalRecoveryPoolPart pool))
          (assessment : (model).BehavioralAssessment),
          (∀ who (history : (protocol).History) (_running : ¬ (protocol).terminal history.state),
            assessment.strategy who ((model).infoOf who history.trace) =
              setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
                omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val
                delivery.property.1 delivery.property.2
                (setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded
                  pins weights) who ((model).infoOf who history.trace)) →
          InformationModel.BehavioralAssessment.IsBayesConsistent (model) assessment
            setup.proposalRecoveryModel_decisionAntichain →
        ∀ (observer owner : Player), observer ≠ owner →
        ∀ (site : (model).InformationSite observer),
          0 < (model).informationMass assessment.strategy observer site →
          (∑ history : (model).InformationHistory observer site.1 with
            setup.GeneratedPreparationHistory owner history.val,
            (assessment.belief observer site history).toReal) ≤
            (Fintype.card (protocol).History : ℝ) * bad.val /
              (chance * lower ^ length) := by
  classical
  obtain ⟨chance, chancePositive, chanceBounded, chanceLower⟩ :=
    setup.exists_proposalRecovery_transitionMass_floor
  obtain ⟨length, lengthBound⟩ := setup.exists_proposalRecovery_ownPlay_length_bound
  refine ⟨chance, length, chancePositive, chanceBounded, ?_⟩
  intro floor floorPositive floorBounded omission delivery omissionPositive omissionSmall
    deliveryPositive deliverySmall
  obtain ⟨lower, lowerPositive, lowerBounded, lowerAt⟩ :=
    setup.exists_proposalRecoveryPreparation_response_floor finite floor floorPositive floorBounded
      omission delivery omissionPositive omissionSmall deliveryPositive deliverySmall
  refine ⟨lower, lowerPositive, lowerBounded, ?_⟩
  intro bad badPositive badSmall pins weights assessment prescribed bayes observer owner different
    site positive
  let values := setup.proposalRecoveryPooledDomainLaw finite floor floorPositive.le floorBounded
    pins weights
  let reference := setup.proposalRecoveryNormalizedTrembledProfile omission.val omission.property.1
    omission.property.2 bad.val bad.property.1 bad.property.2 delivery.val delivery.property.1
    delivery.property.2 values
  let ratio := bad.val / (chance * lower ^ length)
  have ratioNonnegative : 0 ≤ ratio :=
    div_nonneg bad.property.1 (mul_nonneg chancePositive.le (pow_nonneg lowerPositive.le _))
  have massFinite : (model).informationMass assessment.strategy observer site ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((model).informationMass_le_one assessment.strategy observer site
        (setup.proposalRecoveryModel_decisionAntichain observer site))
  have massPositive : 0 < ((model).informationMass assessment.strategy observer site).toReal :=
    ENNReal.toReal_pos positive.ne' massFinite
  have one (history : (model).InformationHistory observer site.1)
      (badHistory : setup.GeneratedPreparationHistory owner history.val) :
      (assessment.belief observer site history).toReal ≤ ratio := by
    obtain ⟨image, _length, _relation, information, prepared⟩ :=
      setup.proposalRecovery_preparation_history owner history.val.trace
    let repaired : (model).InformationHistory observer site.1 :=
      ⟨image, (information observer different).trans history.property⟩
    have words : ∀ who, who ≠ owner →
        (model).ownPlay who history.val.trace = (model).ownPlay who image.trace := by
      intro who foreign
      exact (setup.proposalRecoveryModel_perfectRecall who image.trace history.val.trace
        (information who foreign)).symm
    have originalWord := setup.proposalRecoveryGenerated_word_upper omission bad delivery
      values assessment.strategy prescribed owner history.val badHistory
    have imageWord := setup.proposalRecoveryPrepared_word_lower omission bad delivery
      values assessment.strategy prescribed lower lowerPositive lowerBounded
      (lowerAt bad badSmall pins weights) length lengthBound owner image prepared
    have reach := setup.proposalRecovery_historyReach_le_of_designated_word assessment.strategy
      owner history.val image words chance chancePositive (chanceLower image) bad.val
        bad.property.1 originalWord lower lowerPositive length imageWord
    have imageBound : ((model).historyReachWeight assessment.strategy image).toReal ≤
        ((model).informationMass assessment.strategy observer site).toReal :=
      ENNReal.toReal_mono massFinite
        ((model).historyReachWeight_le_informationMass assessment site repaired)
    have total := reach.trans (mul_le_mul_of_nonneg_left imageBound ratioNonnegative)
    rw [InformationModel.belief_toReal_eq_div bayes positive history, div_le_iff₀ massPositive]
    simpa only [ratio, mul_comm] using total
  have sumBound :
      (∑ history : (model).InformationHistory observer site.1 with
        setup.GeneratedPreparationHistory owner history.val,
        (assessment.belief observer site history).toReal) ≤
      ∑ history : (model).InformationHistory observer site.1 with
        setup.GeneratedPreparationHistory owner history.val, ratio :=
    Finset.sum_le_sum fun history included => one history (Finset.mem_filter.mp included).2
  have count : (Finset.univ.filter fun history : (model).InformationHistory observer site.1 =>
      setup.GeneratedPreparationHistory owner history.val).card ≤ Fintype.card (protocol).History :=
    (Finset.card_le_univ _).trans (Fintype.card_subtype_le _)
  calc
    _ ≤ _ := sumBound
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card (protocol).History : ℝ) * ratio :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast count) ratioNonnegative
    _ = _ := by dsimp only [ratio]; ring

end Vegas.SourceProgram.Setup
