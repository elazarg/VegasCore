/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryAncillaryFibers
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Exact original source Bayes cancellation

Counterfactual density is unchanged by the actual retired-word exchange.
The owner's constant positive reach cancels separately in each full
information fiber. No prior on reduced labels is introduced.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- At two genuine source decision sites with equal erased keys, an actual
full-history exchange transports the ORIGINAL Bayes belief exactly. Every
opponent's full information and the true public chronology are retained.
The original joint setup law may be correlated. -/
theorem commitRecovery_bayes_eq_of_erasedInformation_eq
    (strategy : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.commitRecoveryModel.InformationSite who) choice,
      choice ∈ (strategy who site.1).support)
    (focal : Player) (target source : setup.commitRecoveryModel.InformationSite focal)
    (same : setup.commitRecoveryErasedInformation focal target.1 =
      setup.commitRecoveryErasedInformation focal source.1) :
    ∃ exchange : setup.commitRecoveryModel.InformationHistory focal source.1 ≃
        setup.commitRecoveryModel.InformationHistory focal target.1,
      (∀ original,
        setup.attemptPublicRecall focal (exchange original).1.trace =
          setup.attemptPublicRecall focal original.1.trace ∧
        (∀ who, who ≠ focal → setup.commitRecoveryModel.infoOf who
          (exchange original).1.trace = setup.commitRecoveryModel.infoOf who original.1.trace) ∧
        setup.commitRecoveryErasedHistory (exchange original).1 =
          setup.commitRecoveryErasedHistory original.1) ∧
      (setup.commitRecoveryModel.bayesBelief strategy focal source
        (setup.commitRecoveryModel_decisionAntichain focal source)
        (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
          strategy mixed focal source)).map
          exchange =
        setup.commitRecoveryModel.bayesBelief strategy focal target
          (setup.commitRecoveryModel_decisionAntichain focal target)
          (setup.commitRecoveryModel.informationMass_pos_of_fullSupport
            strategy mixed focal target) := by
  classical
  obtain ⟨exchange, exchangeSpec⟩ :=
    setup.commitRecovery_information_fiber_equiv strategy focal target source same
  have remembered :=  setup.commitRecoveryModel.decisionRecall_of_perfectRecall
    setup.commitRecoveryModel_perfectRecall
  obtain ⟨sourceReach, sourceCommon⟩ :=
    setup.commitRecoveryModel.commonPlayerReachAt_of_decisionRecall
    remembered strategy focal source
  obtain ⟨targetReach, targetCommon⟩ :=
    setup.commitRecoveryModel.commonPlayerReachAt_of_decisionRecall
    remembered strategy focal target
  have sourcePositive := setup.commitRecoveryModel.informationMass_pos_of_fullSupport
    strategy mixed focal source
  have targetPositive := setup.commitRecoveryModel.informationMass_pos_of_fullSupport
    strategy mixed focal target
  have sourceReachPositive := setup.commitRecoveryModel.commonPlayerReach_pos
    sourceReach sourceCommon sourcePositive
  have targetReachPositive := setup.commitRecoveryModel.commonPlayerReach_pos
    targetReach targetCommon targetPositive
  have factor (site : setup.commitRecoveryModel.InformationSite focal) (reach : ℝ)
      (common : ∀ history : setup.commitRecoveryModel.InformationHistory focal site.1,
        setup.commitRecoveryModel.playerReachProbability strategy focal history.1.trace = reach) :
      (setup.commitRecoveryModel.informationMass strategy focal site).toReal = reach *
        ∑' history : setup.commitRecoveryModel.InformationHistory focal site.1,
          setup.commitRecoveryModel.counterfactualReachProbability strategy focal
            history.1.trace := by
    unfold InformationModel.informationMass
    rw [ENNReal.tsum_toReal_eq (f := fun history :
        setup.commitRecoveryModel.InformationHistory focal site.1 =>
          setup.commitRecoveryModel.historyReachWeight strategy history.1)
      fun history => PMF.apply_ne_top _ _, ← tsum_mul_left]
    apply tsum_congr
    intro history
    rw [setup.commitRecoveryModel.historyReachProbability_eq_player_mul_counterfactual
      strategy focal history.1.trace, common history]
  have sameCounterfactual :
      (∑' history : setup.commitRecoveryModel.InformationHistory focal target.1,
        setup.commitRecoveryModel.counterfactualReachProbability strategy focal history.1.trace) =
      ∑' history : setup.commitRecoveryModel.InformationHistory focal source.1,
        setup.commitRecoveryModel.counterfactualReachProbability strategy focal
          history.1.trace := by
    rw [← exchange.tsum_eq]
    exact tsum_congr fun history => (exchangeSpec history).2.2.1
  refine ⟨exchange, fun original => ⟨(exchangeSpec original).1,
    (exchangeSpec original).2.1, (exchangeSpec original).2.2.2⟩, ?_⟩
  apply pmf_ext_toReal
  intro targetHistory
  obtain ⟨original, rfl⟩ := exchange.surjective targetHistory
  rw [pmf_map_apply_of_injective _ exchange.injective original,
    setup.commitRecoveryModel.bayesBelief_apply,
    setup.commitRecoveryModel.bayesBelief_apply,
    ENNReal.toReal_div, ENNReal.toReal_div,
    setup.commitRecoveryModel.historyReachProbability_eq_player_mul_counterfactual,
    setup.commitRecoveryModel.historyReachProbability_eq_player_mul_counterfactual,
    sourceCommon original, targetCommon (exchange original),
    factor source sourceReach sourceCommon, factor target targetReach targetCommon,
    sameCounterfactual, (exchangeSpec original).2.2.1,
    mul_div_mul_left _ _ sourceReachPositive.ne',
    mul_div_mul_left _ _ targetReachPositive.ne']

end Vegas.SourceProgram.Setup
