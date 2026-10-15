/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ProjectedBeliefTransport

/-! # Finite repair preimages for selected execution contributions -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open Finset

variable {Player : Type} [Fintype Player] {E : ExecutionProtocol Player}
  {M : InformationModel E} {who : Player} {site : M.InformationSite who}

open Classical in
/-- A selected component of each history's actual reach can be grouped by a
many-to-one repair. The number of preimages is exposed rather than discarded
by a pointwise likelihood estimate. -/
theorem sum_contribution_le_of_repair
    (profile : ∀ player, M.BehavioralPolicy player)
    (histories targets : Finset (M.InformationHistory who site.1))
    (repair : M.InformationHistory who site.1 → M.InformationHistory who site.1)
    (contribution : M.InformationHistory who site.1 → ℝ)
    (ratio : ℝ) (ratioNonnegative : 0 ≤ ratio) (multiplicity : Nat)
    (mapped : ∀ history ∈ histories, repair history ∈ targets)
    (preimages : ∀ target ∈ targets,
      (histories.filter fun history => repair history = target).card ≤ multiplicity)
    (dominated : ∀ history ∈ histories, contribution history ≤
      ratio * (M.historyReachWeight profile (repair history).1).toReal) :
    ∑ history ∈ histories, contribution history ≤
      (multiplicity : ℝ) * ratio * finiteHistoryReach profile who site targets := by
  classical
  let reach := fun history : M.InformationHistory who site.1 =>
    (M.historyReachWeight profile history.1).toReal
  have fibers : ∑ history ∈ histories, reach (repair history) =
      ∑ target ∈ targets,
        (histories.filter fun history => repair history = target).card * reach target := by
    rw [← sum_fiberwise_of_maps_to (g := repair) (t := targets) mapped]
    refine sum_congr rfl fun target _ => ?_
    rw [sum_congr rfl fun history member => by rw [(mem_filter.mp member).2],
      sum_const, nsmul_eq_mul]
  calc ∑ history ∈ histories, contribution history
      ≤ ∑ history ∈ histories, ratio * reach (repair history) :=
        sum_le_sum fun history member => dominated history member
    _ = ratio * ∑ target ∈ targets,
        (histories.filter fun history => repair history = target).card * reach target := by
      rw [← mul_sum, fibers]
    _ ≤ ratio * ∑ target ∈ targets, (multiplicity : ℝ) * reach target := by
      apply mul_le_mul_of_nonneg_left _ ratioNonnegative
      apply sum_le_sum
      intro target member
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast preimages target member)
        ENNReal.toReal_nonneg
    _ = (multiplicity : ℝ) * ratio * finiteHistoryReach profile who site targets := by
      unfold finiteHistoryReach
      rw [← mul_sum]
      ring

omit [Fintype Player] in
open Classical in
/-- Every repair on a fixed finite group has a rate-independent multiplicity
bound, even when its choice of target varies with the approximation. -/
theorem repair_preimages_card_le
    (histories : Finset (M.InformationHistory who site.1))
    (repair : M.InformationHistory who site.1 → M.InformationHistory who site.1)
    (target : M.InformationHistory who site.1) :
    (histories.filter fun history => repair history = target).card ≤ histories.card :=
  card_filter_le _ _

end GameTheory.Protocol.InformationModel
