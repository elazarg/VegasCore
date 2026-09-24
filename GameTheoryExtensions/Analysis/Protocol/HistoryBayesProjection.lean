/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment
import Mathlib.Algebra.BigOperators.Field

/-! # Bayes projection from complete-history laws

A length-preserving history projection transports reach probabilities by
summing its fibers. If positive histories cannot project into an information
site without belonging to its chosen raw fiber, the same identity transports
the site's mass and its normalized Bayes belief.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] {E T : ExecutionProtocol Player}
  (M : InformationModel E) (N : InformationModel T)
  [Finite E.History]
  (raw : ∀ who, M.BehavioralPolicy who) (source : ∀ who, N.BehavioralPolicy who)
  (project : E.History → T.History)
  (lengths : ∀ history, (project history).trace.length = history.trace.length)
  (laws : ∀ fuel, (M.runBehavioral raw fuel).map project = N.runBehavioral source fuel)

include lengths laws in
omit [Finite E.History] in
theorem historyReachProbability_projection [Fintype E.History] [DecidableEq T.History]
    (history : T.History) :
    N.historyReachProbability source history =
      ∑ original,
        if project original = history then M.historyReachProbability raw original else 0 :=
    by
  classical
  have law := congrArg (fun law => law.prob history) (laws history.trace.length)
  rw [FinDist.prob_map, FinDist.expect_eq_sum] at law
  rw [historyReachProbability, ← law]
  apply Finset.sum_congr rfl
  intro original _
  by_cases same : project original = history
  · rw [ite_eq_left same, ite_eq_left same.symm, mul_one, ← same, lengths]
    rfl
  · simp only [same, Ne.symm same, ite_false, mul_zero]

variable (who : Player) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
  [Fintype (M.InformationHistory who rawSite.1)]
  [Fintype (N.InformationHistory who sourceSite.1)]
  (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
    N.infoOf who (project history).trace = sourceSite.1)
  (reflects : ∀ history, 0 < M.historyReachProbability raw history →
    N.infoOf who (project history).trace = sourceSite.1 →
      M.infoOf who history.trace = rawSite.1)

include lengths laws reflects in
omit [Fintype (N.InformationHistory who sourceSite.1)] in
theorem informationHistoryReach_projection [DecidableEq T.History]
    (history : N.InformationHistory who sourceSite.1) :
    N.historyReachProbability source history.1 =
      ∑ original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then M.historyReachProbability raw original.1 else 0 := by
  classical
  let := Fintype.ofFinite E.History
  rw [M.historyReachProbability_projection N raw source project lengths laws]
  let value (original : E.History) :=
    if project original = history.1 then M.historyReachProbability raw original else 0
  have outside : ∀ original, M.infoOf who original.trace ≠ rawSite.1 → value original = 0 := by
    intro original absent
    by_cases same : project original = history.1
    · have zero : M.historyReachProbability raw original = 0 := by
        apply le_antisymm
        · apply le_of_not_gt
          intro positive
          exact absent (reflects original positive (by rw [same]; exact history.2))
        · exact FinDist.prob_nonneg _ _
      simp only [value, same, ite_true, zero]
    · exact ite_eq_right same
  change (∑ original, value original) = ∑ original : M.InformationHistory who rawSite.1,
    value original.1
  calc
    _ = ∑ original ∈ Finset.univ.filter (fun h => M.infoOf who h.trace = rawSite.1),
        value original := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro original _ absent
      apply outside original
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using absent
    _ = _ := Finset.sum_subtype _
      (by intro original; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) value

include lengths laws reflects maps in
theorem informationMass_projection :
    M.informationMass raw who rawSite = N.informationMass source who sourceSite := by
  classical
  unfold informationMass
  simp_rw [M.informationHistoryReach_projection N raw source project lengths laws who rawSite
    sourceSite reflects]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  let image : N.InformationHistory who sourceSite.1 :=
    ⟨project original.1, maps original.1 original.2⟩
  have equal (target : N.InformationHistory who sourceSite.1) :
      project original.1 = target.1 ↔ image = target := by
    change image.1 = target.1 ↔ image = target
    exact Subtype.ext_iff.symm
  simp only [equal, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

include lengths laws reflects maps in
/-- Canonical Bayes beliefs commute with the history projection whenever the
positive raw histories reflect membership in the chosen information fiber. -/
theorem bayesBelief_projection
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (rawPositive : 0 < M.informationMass raw who rawSite)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief raw who rawSite rawAntichain rawPositive).map
      (fun original : M.InformationHistory who rawSite.1 =>
        (⟨project original.1, maps original.1 original.2⟩ :
          N.InformationHistory who sourceSite.1)) =
      N.bayesBelief source who sourceSite sourceAntichain sourcePositive := by
  classical
  apply FinDist.ext_of_prob
  intro history
  rw [FinDist.prob_map, FinDist.expect_eq_sum, N.bayesBelief_prob]
  simp_rw [M.bayesBelief_prob]
  rw [← M.informationMass_projection N raw source project lengths laws who rawSite sourceSite
    maps reflects,
    M.informationHistoryReach_projection N raw source project lengths laws who rawSite
      sourceSite reflects history, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro original _
  by_cases same : project original.1 = history.1
  · have equal : history = ⟨project original.1, maps original.1 original.2⟩ :=
      Subtype.ext same.symm
    rw [ite_eq_left equal, mul_one, ite_eq_left same]
  · have different : history ≠ ⟨project original.1, maps original.1 original.2⟩ :=
      fun equal => same (congrArg Subtype.val equal).symm
    simp only [same, different, ite_false, mul_zero, zero_div]

end GameTheory.Protocol.InformationModel
