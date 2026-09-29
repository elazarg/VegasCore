/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment
import GameTheoryExtensions.Analysis.Protocol.CounterfactualBeliefs
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
  have law := congrArg (fun law => (law history).toReal) (laws history.trace.length)
  rw [toReal_map_apply, expect_eq_sum] at law
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
        · exact ENNReal.toReal_nonneg
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
  apply pmf_ext_toReal
  intro history
  rw [toReal_map_apply, expect_eq_sum, N.bayesBelief_prob]
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



namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] {E T : ExecutionProtocol Player}
  (M : InformationModel E) (N : InformationModel T) [Finite E.History]
  (raw : ∀ who, M.BehavioralPolicy who) (source : ∀ who, N.BehavioralPolicy who)
  (project : E.History → T.History)
  (who : Player) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
  [Fintype (M.InformationHistory who rawSite.1)]
  [Fintype (N.InformationHistory who sourceSite.1)]
  (rawDepth sourceDepth : Nat)
  (rawClock : ∀ history : M.InformationHistory who rawSite.1,
    history.1.trace.length = rawDepth)
  (sourceClock : ∀ history : N.InformationHistory who sourceSite.1,
    history.1.trace.length = sourceDepth)
  (law : (M.runBehavioral raw rawDepth).map project = N.runBehavioral source sourceDepth)
  (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
    N.infoOf who (project history).trace = sourceSite.1)
  (reflects : ∀ history, 0 < ((M.runBehavioral raw rawDepth) history).toReal →
    N.infoOf who (project history).trace = sourceSite.1 →
      M.infoOf who history.trace = rawSite.1)

include rawClock sourceClock law reflects in
omit [Fintype (N.InformationHistory who sourceSite.1)] in
/-- A service block may consume a different number of steps than its source
action. At corresponding decision checkpoints, the actual prefix law still
transports reach weights by summing the compatible native histories. -/
theorem informationHistoryReach_projection_at_depth [DecidableEq T.History]
    (history : N.InformationHistory who sourceSite.1) :
    N.historyReachProbability source history.1 =
      ∑ original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then M.historyReachProbability raw original.1 else 0 := by
  classical
  let := Fintype.ofFinite E.History
  have probability := congrArg (fun distribution => (distribution history.1).toReal) law
  rw [toReal_map_apply, expect_eq_sum] at probability
  rw [historyReachProbability, sourceClock history, ← probability]
  let value (original : E.History) :=
    if project original = history.1 then ((M.runBehavioral raw rawDepth) original).toReal else 0
  have outside : ∀ original, M.infoOf who original.trace ≠ rawSite.1 → value original = 0 := by
    intro original absent
    by_cases same : project original = history.1
    · have zero : ((M.runBehavioral raw rawDepth) original).toReal = 0 := by
        apply le_antisymm
        · apply le_of_not_gt
          intro positive
          exact absent (reflects original positive (by rw [same]; exact history.2))
        · exact ENNReal.toReal_nonneg
      simp only [value, same, ite_true, zero]
    · exact ite_eq_right same
  calc
    _ = ∑ original, value original := by
      apply Finset.sum_congr rfl
      intro original _
      by_cases same : project original = history.1
      · simp only [value, same, ite_true, mul_one]
      · simp only [value, same, Ne.symm same, ite_false, mul_zero]
    _ = ∑ original ∈ Finset.univ.filter (fun h => M.infoOf who h.trace = rawSite.1),
        value original := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro original _ absent
      apply outside original
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using absent
    _ = ∑ original : M.InformationHistory who rawSite.1, value original.1 :=
      Finset.sum_subtype _
        (by intro original; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) value
    _ = _ := by
      apply Finset.sum_congr rfl
      intro original _
      rw [historyReachProbability, rawClock original]

include rawClock sourceClock law maps reflects in
theorem informationMass_projection_at_depth :
    M.informationMass raw who rawSite = N.informationMass source who sourceSite := by
  classical
  unfold informationMass
  simp_rw [M.informationHistoryReach_projection_at_depth N raw source project who rawSite
    sourceSite rawDepth sourceDepth rawClock sourceClock law reflects]
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

include rawClock sourceClock law maps reflects in
/-- Bayes conditioning commutes with a checkpoint projection even when source
and implementation take different numbers of steps. Applying this identity to
each fully mixed approximant preserves off-path limiting beliefs; no positive
probability at the limiting profile is required. -/
theorem bayesBelief_projection_at_depth
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
  apply pmf_ext_toReal
  intro history
  rw [toReal_map_apply, expect_eq_sum, N.bayesBelief_prob]
  simp_rw [M.bayesBelief_prob]
  rw [← M.informationMass_projection_at_depth N raw source project who rawSite sourceSite
    rawDepth sourceDepth rawClock sourceClock law maps reflects,
    M.informationHistoryReach_projection_at_depth N raw source project who rawSite sourceSite
      rawDepth sourceDepth rawClock sourceClock law reflects history, Finset.sum_div]
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

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] {E T : ExecutionProtocol Player}
  (M : InformationModel E) (N : InformationModel T) [Finite E.History]

/-- A focal selector can single out one private alias history without changing
that player's Bayes belief. Only the selected profile must reflect the chosen
raw information fiber; the native profile may mix over many aliases. Source
and native checkpoints may occur at different depths. -/
theorem bayesBelief_projection_at_depth_of_focal_selector
    (native selected : ∀ who, M.BehavioralPolicy who)
    (source : ∀ who, N.BehavioralPolicy who)
    (project : E.History → T.History)
    (who : Player) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
    [Fintype (M.InformationHistory who rawSite.1)]
    [Fintype (N.InformationHistory who sourceSite.1)]
    (rawDepth sourceDepth : Nat)
    (rawClock : ∀ history : M.InformationHistory who rawSite.1,
      history.1.trace.length = rawDepth)
    (sourceClock : ∀ history : N.InformationHistory who sourceSite.1,
      history.1.trace.length = sourceDepth)
    (law : (M.runBehavioral selected rawDepth).map project =
      N.runBehavioral source sourceDepth)
    (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
      N.infoOf who (project history).trace = sourceSite.1)
    (reflects : ∀ history, 0 < ((M.runBehavioral selected rawDepth) history).toReal →
      N.infoOf who (project history).trace = sourceSite.1 →
        M.infoOf who history.trace = rawSite.1)
    (agree : ∀ other, other ≠ who → native other = selected other)
    (nativeCommon : M.CommonPlayerReachAt native who rawSite)
    (selectedCommon : M.CommonPlayerReachAt selected who rawSite)
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (nativePositive : 0 < M.informationMass native who rawSite)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief native who rawSite rawAntichain nativePositive).map
      (fun original : M.InformationHistory who rawSite.1 =>
        (⟨project original.1, maps original.1 original.2⟩ :
          N.InformationHistory who sourceSite.1)) =
      N.bayesBelief source who sourceSite sourceAntichain sourcePositive := by
  have mass := M.informationMass_projection_at_depth N selected source project who rawSite
    sourceSite rawDepth sourceDepth rawClock sourceClock law maps reflects
  have selectedPositive : 0 < M.informationMass selected who rawSite := by
    rw [mass]
    exact sourcePositive
  rw [M.bayesBelief_eq_of_eq_off native selected who rawSite rawAntichain agree
    nativeCommon selectedCommon nativePositive selectedPositive]
  exact M.bayesBelief_projection_at_depth N selected source project who rawSite sourceSite
    rawDepth sourceDepth rawClock sourceClock law maps reflects rawAntichain sourceAntichain
      selectedPositive sourcePositive

end GameTheory.Protocol.InformationModel
