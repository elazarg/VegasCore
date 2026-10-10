/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Bayes transport along proportional reach weights

Bayes beliefs are ratios of reach weights, so a history map transports them
whenever the reach weights summed over its fibers are one fixed positive finite
multiple of the target reach weights. The library's exact transport,
`GameTheory.Protocol.InformationModel.bayesBelief_projection_of_reach`, is the
case of multiplier one. Along a tremble sequence the weights of a history and
of its counterpart in another protocol are typically only proportional, for
instance when one of them passes through a tremble and the other does not.
No common decision depth is involved.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open scoped ENNReal

variable {ι : Type*} [Fintype ι] {E T : ExecutionProtocol ι}
  (M : InformationModel E) (N : InformationModel T)
  (raw : (i : ι) → M.BehavioralPolicy i) (source : (i : ι) → N.BehavioralPolicy i)
  (project : E.History → T.History) [DecidableEq T.History]
  (who : ι) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
  (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
    N.infoOf who (project history).trace = sourceSite.1)
  (scale : ℝ≥0∞)
  (fiber : ∀ history : N.InformationHistory who sourceSite.1,
    scale * N.historyReachWeight source history.1 =
      ∑' original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then M.historyReachWeight raw original.1 else 0)

include maps fiber in
/-- Proportional fiber sums scale the site's mass by the same multiplier. -/
theorem informationMass_projection_of_proportional_reach :
    M.informationMass raw who rawSite = scale * N.informationMass source who sourceSite := by
  classical
  unfold informationMass
  rw [← ENNReal.tsum_mul_left]
  simp_rw [fiber]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro original
  let image : N.InformationHistory who sourceSite.1 :=
    ⟨project original.1, maps original.1 original.2⟩
  have equal (target : N.InformationHistory who sourceSite.1) :
      project original.1 = target.1 ↔ target = image := by
    change image.1 = target.1 ↔ target = image
    exact ⟨fun same => (Subtype.ext same).symm, fun same => by rw [same]⟩
  simp only [equal, tsum_ite_eq]

include fiber in
/-- **Proportional Bayes projection.** A history map whose fiber sums of reach
weights are a fixed positive finite multiple of the target reach weights
transports the Bayes belief. -/
theorem bayesBelief_projection_of_proportional_reach
    (scaleNonzero : scale ≠ 0) (scaleFinite : scale ≠ ∞)
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief raw who rawSite rawAntichain (by
      rw [M.informationMass_projection_of_proportional_reach N raw source project who
        rawSite sourceSite maps scale fiber]
      exact ENNReal.mul_pos scaleNonzero sourcePositive.ne')).map
      (fun original : M.InformationHistory who rawSite.1 =>
        (⟨project original.1, maps original.1 original.2⟩ :
          N.InformationHistory who sourceSite.1)) =
      N.bayesBelief source who sourceSite sourceAntichain sourcePositive := by
  classical
  have mass := M.informationMass_projection_of_proportional_reach N raw source project who
    rawSite sourceSite maps scale fiber
  ext history
  rw [PMF.map_apply, N.bayesBelief_apply]
  simp_rw [M.bayesBelief_apply]
  rw [
    ← ENNReal.mul_div_mul_left (N.historyReachWeight source history.1)
      (N.informationMass source who sourceSite) scaleNonzero scaleFinite,
    fiber history, ← mass, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro original
  by_cases same : project original.1 = history.1
  · have equal : history = ⟨project original.1, maps original.1 original.2⟩ :=
      Subtype.ext same.symm
    rw [ite_eq_left equal, ite_eq_left same, div_eq_mul_inv]
  · have different : history ≠ ⟨project original.1, maps original.1 original.2⟩ :=
      fun equal => same (congrArg Subtype.val equal).symm
    rw [ite_eq_right different, ite_eq_right same, zero_mul]

end GameTheory.Protocol.InformationModel
