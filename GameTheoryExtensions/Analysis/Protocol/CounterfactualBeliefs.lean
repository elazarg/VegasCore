/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualRegret
import GameTheoryExtensions.Math.Probability.Support

/-! # A player's own strategy cancels from its Bayes beliefs

At an information site with constant own reach, two profiles differing only
in that player's strategy induce the same Bayes belief whenever both reach
the site with positive probability. The alternative need not be fully mixed.
This is used to compare private-alias perturbations with a selector for a
fixed recalled action sequence.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player]
  {E : ExecutionProtocol Player} (M : InformationModel E)

theorem bayesBelief_eq_of_eq_off
    (first second : ∀ who, M.BehavioralPolicy who)
    (who : Player) (site : M.InformationSite who)
    (antichain : site.IsHistoryAntichain)
    (agree : ∀ other, other ≠ who → first other = second other)
    (firstCommon : M.CommonPlayerReachAt first who site)
    (secondCommon : M.CommonPlayerReachAt second who site)
    (firstPositive : 0 < M.informationMass first who site)
    (secondPositive : 0 < M.informationMass second who site) :
    M.bayesBelief first who site antichain firstPositive =
      M.bayesBelief second who site antichain secondPositive := by
  classical
  obtain ⟨firstReach, firstCommon⟩ := firstCommon
  obtain ⟨secondReach, secondCommon⟩ := secondCommon
  have firstNonzero := (M.commonPlayerReach_pos firstReach firstCommon firstPositive).ne'
  have secondNonzero := (M.commonPlayerReach_pos secondReach secondCommon secondPositive).ne'
  have factor (profile : ∀ player, M.BehavioralPolicy player) (reach : ℝ)
      (common : ∀ history : M.InformationHistory who site.1,
        M.playerReachProbability profile who history.1.trace = reach) :
      (M.informationMass profile who site).toReal = reach *
        ∑' history : M.InformationHistory who site.1,
          M.counterfactualReachProbability profile who history.1.trace := by
    unfold informationMass
    rw [ENNReal.tsum_toReal_eq (f := fun history : M.InformationHistory who site.1 =>
      M.historyReachWeight profile history.1) fun history => PMF.apply_ne_top _ _,
      ← tsum_mul_left]
    apply tsum_congr
    intro history
    rw [M.historyReachProbability_eq_player_mul_counterfactual profile who history.1.trace,
      common history]
  have firstMass := factor first firstReach firstCommon
  have secondMass := factor second secondReach secondCommon
  simp_rw [← M.counterfactualReachProbability_eq_of_eq_off agree] at secondMass
  apply pmf_ext_toReal
  intro history
  rw [M.bayesBelief_apply first who site antichain firstPositive history,
    M.bayesBelief_apply second who site antichain secondPositive history,
    ENNReal.toReal_div, ENNReal.toReal_div,
    M.historyReachProbability_eq_player_mul_counterfactual first who history.1.trace,
    M.historyReachProbability_eq_player_mul_counterfactual second who history.1.trace,
    firstCommon history, secondCommon history, firstMass, secondMass,
    ← M.counterfactualReachProbability_eq_of_eq_off agree history.1.trace,
    mul_div_mul_left _ _ firstNonzero, mul_div_mul_left _ _ secondNonzero]

end GameTheory.Protocol.InformationModel
