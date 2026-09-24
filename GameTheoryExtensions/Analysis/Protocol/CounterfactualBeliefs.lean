/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualRegret

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
    [Fintype (M.InformationHistory who site.1)]
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
      M.informationMass profile who site = reach *
        ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability profile who history.1.trace := by
    unfold informationMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro history _
    rw [M.historyReachProbability_eq_player_mul_counterfactual profile who history.1.trace,
      common history]
  have firstMass := factor first firstReach firstCommon
  have secondMass := factor second secondReach secondCommon
  simp_rw [← M.counterfactualReachProbability_eq_of_eq_off agree] at secondMass
  apply FinDist.ext_of_prob
  intro history
  rw [M.bayesBelief_prob first who site antichain firstPositive history,
    M.bayesBelief_prob second who site antichain secondPositive history,
    M.historyReachProbability_eq_player_mul_counterfactual first who history.1.trace,
    M.historyReachProbability_eq_player_mul_counterfactual second who history.1.trace,
    firstCommon history, secondCommon history, firstMass, secondMass,
    ← M.counterfactualReachProbability_eq_of_eq_off agree history.1.trace,
    mul_div_mul_left _ _ firstNonzero, mul_div_mul_left _ _ secondNonzero]

end GameTheory.Protocol.InformationModel
