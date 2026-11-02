/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

variable {ι : Type*} {E T : ExecutionProtocol ι} [E.FiniteMovers] [T.FiniteMovers]
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

include fiber in
/-- **Proportional Bayes projection.** A history map whose fiber sums of reach
weights are a fixed positive finite multiple of the target reach weights
transports the Bayes belief. -/
theorem bayesBelief_projection_of_positive_reach
    (scaleNonzero : scale ≠ 0)
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
  have scaleFinite : scale ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_left (by
      rw [← mass]
      exact ne_top_of_le_ne_top ENNReal.one_ne_top
        (M.informationMass_le_one raw who rawSite rawAntichain)) sourcePositive.ne').ne
  exact M.bayesBelief_projection_of_proportional_reach N raw source project who
    rawSite sourceSite maps scale fiber scaleNonzero scaleFinite rawAntichain
    sourceAntichain sourcePositive

end GameTheory.Protocol.InformationModel
