/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryFibers
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Exact Bayes cancellation on full proposal-recovery fibers

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
The original joint setup law may be correlated. Canonical proposal archives are
matched explicitly, including disclosures whose semantic publication failed. -/
theorem proposalRecovery_bayes_eq_of_erased_information_archive
    (finite : setup.program.FiniteBindingTypes)
    (strategy : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (mixed : ∀ who (site : setup.proposalRecoveryModel.InformationSite who) choice,
      choice ∈ (strategy who site.1).support)
    (focal : Player) (target source : setup.proposalRecoveryModel.InformationSite focal)
    (semantic : setup.commitRecoveryErasedInformation focal
        (setup.proposalRecoveryEraseInfo focal target.1) =
      setup.commitRecoveryErasedInformation focal (setup.proposalRecoveryEraseInfo focal source.1))
    (archive : setup.proposalRecoveryArchive focal target.1 =
      setup.proposalRecoveryArchive focal source.1) :
    ∃ exchange : setup.proposalRecoveryModel.InformationHistory focal source.1 ≃
        setup.proposalRecoveryModel.InformationHistory focal target.1,
      (∀ original,
        (∀ who, setup.proposalRecoveryPublicRecall who (exchange original).1.trace =
          setup.proposalRecoveryPublicRecall who original.1.trace) ∧
        (∀ who, who ≠ focal → setup.proposalRecoveryModel.infoOf who
          (exchange original).1.trace = setup.proposalRecoveryModel.infoOf who original.1.trace) ∧
        setup.proposalRecoveryErasedHistory (exchange original).1 =
          setup.proposalRecoveryErasedHistory original.1) ∧
      (setup.proposalRecoveryModel.bayesBelief strategy focal source
        (setup.proposalRecoveryModel_decisionAntichain focal source)
        (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
          strategy mixed focal source)).map
          exchange =
        setup.proposalRecoveryModel.bayesBelief strategy focal target
          (setup.proposalRecoveryModel_decisionAntichain focal target)
          (setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
            strategy mixed focal target) := by
  classical
  obtain ⟨exchange, exchangeSpec⟩ :=
    setup.proposalRecovery_information_fiber_equiv finite strategy focal target source
      semantic archive
  have remembered :=  setup.proposalRecoveryModel.decisionRecall_of_perfectRecall
    setup.proposalRecoveryModel_perfectRecall
  obtain ⟨sourceReach, sourceCommon⟩ :=
    setup.proposalRecoveryModel.commonPlayerReachAt_of_decisionRecall
    remembered strategy focal source
  obtain ⟨targetReach, targetCommon⟩ :=
    setup.proposalRecoveryModel.commonPlayerReachAt_of_decisionRecall
    remembered strategy focal target
  have sourcePositive := setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
    strategy mixed focal source
  have targetPositive := setup.proposalRecoveryModel.informationMass_pos_of_fullSupport
    strategy mixed focal target
  have sourceReachPositive := setup.proposalRecoveryModel.commonPlayerReach_pos
    sourceReach sourceCommon sourcePositive
  have targetReachPositive := setup.proposalRecoveryModel.commonPlayerReach_pos
    targetReach targetCommon targetPositive
  have factor (site : setup.proposalRecoveryModel.InformationSite focal) (reach : ℝ)
      (common : ∀ history : setup.proposalRecoveryModel.InformationHistory focal site.1,
        setup.proposalRecoveryModel.playerReachProbability strategy focal history.1.trace = reach) :
      (setup.proposalRecoveryModel.informationMass strategy focal site).toReal = reach *
        ∑' history : setup.proposalRecoveryModel.InformationHistory focal site.1,
          setup.proposalRecoveryModel.counterfactualReachProbability strategy focal
            history.1.trace := by
    unfold InformationModel.informationMass
    rw [ENNReal.tsum_toReal_eq (f := fun history :
        setup.proposalRecoveryModel.InformationHistory focal site.1 =>
          setup.proposalRecoveryModel.historyReachWeight strategy history.1)
      fun history => PMF.apply_ne_top _ _, ← tsum_mul_left]
    apply tsum_congr
    intro history
    rw [setup.proposalRecoveryModel.historyReachProbability_eq_player_mul_counterfactual
      strategy focal history.1.trace, common history]
  have sameCounterfactual :
      (∑' history : setup.proposalRecoveryModel.InformationHistory focal target.1,
        setup.proposalRecoveryModel.counterfactualReachProbability strategy focal history.1.trace) =
      ∑' history : setup.proposalRecoveryModel.InformationHistory focal source.1,
        setup.proposalRecoveryModel.counterfactualReachProbability strategy focal
          history.1.trace := by
    rw [← exchange.tsum_eq]
    exact tsum_congr fun history => (exchangeSpec history).2.2.1
  refine ⟨exchange, fun original => ⟨(exchangeSpec original).1,
    (exchangeSpec original).2.1, (exchangeSpec original).2.2.2⟩, ?_⟩
  apply pmf_ext_toReal
  intro targetHistory
  obtain ⟨original, rfl⟩ := exchange.surjective targetHistory
  rw [pmf_map_apply_of_injective _ exchange.injective original,
    setup.proposalRecoveryModel.bayesBelief_apply,
    setup.proposalRecoveryModel.bayesBelief_apply,
    ENNReal.toReal_div, ENNReal.toReal_div,
    setup.proposalRecoveryModel.historyReachProbability_eq_player_mul_counterfactual,
    setup.proposalRecoveryModel.historyReachProbability_eq_player_mul_counterfactual,
    sourceCommon original, targetCommon (exchange original),
    factor source sourceReach sourceCommon, factor target targetReach targetCommon,
    sameCounterfactual, (exchangeSpec original).2.2.1,
    mul_div_mul_left _ _ sourceReachPositive.ne',
    mul_div_mul_left _ _ targetReachPositive.ne']

end Vegas.SourceProgram.Setup
