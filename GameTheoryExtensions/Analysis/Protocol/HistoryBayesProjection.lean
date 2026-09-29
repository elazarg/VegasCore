/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment
import GameTheoryExtensions.Analysis.Protocol.CounterfactualBeliefs

/-! # Bayes projection from complete-history laws

A history projection transports reach weights by summing its fibers. If
positive histories cannot project into an information site without belonging
to its chosen raw fiber, the same identity transports the site's mass and its
normalized Bayes belief. No finiteness of histories or fibers is assumed.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] {E T : ExecutionProtocol Player}
  (M : InformationModel E) (N : InformationModel T)

section Fiber

variable (project : E.History → T.History) (who : Player)
  (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
  (rawWeight : E.History → ENNReal) (sourceWeight : T.History → ENNReal)
  (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
    N.infoOf who (project history).trace = sourceSite.1)

omit [Fintype Player] in
/-- Restrict a projected reach sum to the chosen raw fiber: positive raw
histories projecting into the source fiber lie in the raw fiber. -/
private theorem fiber_sum [DecidableEq T.History]
    (projected : ∀ history : T.History,
      sourceWeight history = ∑' original,
          if project original = history then rawWeight original else 0)
    (reflects : ∀ history, rawWeight history ≠ 0 →
      N.infoOf who (project history).trace = sourceSite.1 →
        M.infoOf who history.trace = rawSite.1)
    (history : N.InformationHistory who sourceSite.1) :
    sourceWeight history.1 =
      ∑' original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then rawWeight original.1 else 0 := by
  classical
  rw [projected, ← tsum_subtype_eq_of_support_subset
    (s := {original : E.History | M.infoOf who original.trace = rawSite.1})]
  · rfl
  · intro original present
    by_cases same : project original = history.1
    · rw [Function.mem_support, ite_eq_left same] at present
      exact reflects original present (by rw [same]; exact history.2)
    · exact absurd (ite_eq_right same) present

omit [Fintype Player] in
include maps in
private theorem fiber_mass [DecidableEq T.History]
    (fiber : ∀ history : N.InformationHistory who sourceSite.1,
      sourceWeight history.1 =
        ∑' original : M.InformationHistory who rawSite.1,
          if project original.1 = history.1 then rawWeight original.1 else 0) :
    ∑' original : M.InformationHistory who rawSite.1, rawWeight original.1 =
      ∑' history : N.InformationHistory who sourceSite.1, sourceWeight history.1 := by
  classical
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

end Fiber

variable (raw : ∀ who, M.BehavioralPolicy who) (source : ∀ who, N.BehavioralPolicy who)
  (project : E.History → T.History)

/-- A length-preserving projection with matching complete-history laws
transports each reach weight to the sum over its fiber. -/
theorem historyReachWeight_projection [DecidableEq T.History]
    (lengths : ∀ history, (project history).trace.length = history.trace.length)
    (laws : ∀ fuel, (M.runBehavioral raw fuel).map project = N.runBehavioral source fuel)
    (history : T.History) :
    N.historyReachWeight source history =
      ∑' original, if project original = history then M.historyReachWeight raw original else 0 := by
  classical
  unfold historyReachWeight
  rw [← laws history.trace.length, PMF.map_apply]
  apply tsum_congr
  intro original
  by_cases same : project original = history
  · rw [ite_eq_left same.symm, ite_eq_left same, ← same, lengths]
  · rw [ite_eq_right (Ne.symm same), ite_eq_right same]

/-- Canonical Bayes beliefs commute with a history projection once the fiber
reach identity and equal masses are known. -/
private theorem bayes_projection [DecidableEq T.History]
    (who : Player) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
    (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
      N.infoOf who (project history).trace = sourceSite.1)
    (rawAntichain : rawSite.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (rawPositive : 0 < M.informationMass raw who rawSite)
    (sourcePositive : 0 < N.informationMass source who sourceSite)
    (fiber : ∀ history : N.InformationHistory who sourceSite.1,
      N.historyReachWeight source history.1 =
        ∑' original : M.InformationHistory who rawSite.1,
          if project original.1 = history.1 then M.historyReachWeight raw original.1 else 0)
    (mass : M.informationMass raw who rawSite = N.informationMass source who sourceSite) :
    (M.bayesBelief raw who rawSite rawAntichain rawPositive).map
      (fun original : M.InformationHistory who rawSite.1 =>
        (⟨project original.1, maps original.1 original.2⟩ :
          N.InformationHistory who sourceSite.1)) =
      N.bayesBelief source who sourceSite sourceAntichain sourcePositive := by
  classical
  ext history
  rw [PMF.map_apply, N.bayesBelief_apply, fiber history, ← mass, div_eq_mul_inv,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro original
  rw [M.bayesBelief_apply]
  by_cases same : project original.1 = history.1
  · have equal : history = ⟨project original.1, maps original.1 original.2⟩ :=
      Subtype.ext same.symm
    rw [ite_eq_left equal, ite_eq_left same, div_eq_mul_inv]
  · have different : history ≠ ⟨project original.1, maps original.1 original.2⟩ :=
      fun equal => same (congrArg Subtype.val equal).symm
    rw [ite_eq_right different, ite_eq_right same, zero_mul]

section Aligned

variable (lengths : ∀ history, (project history).trace.length = history.trace.length)
  (laws : ∀ fuel, (M.runBehavioral raw fuel).map project = N.runBehavioral source fuel)
  (who : Player) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
  (maps : ∀ history, M.infoOf who history.trace = rawSite.1 →
    N.infoOf who (project history).trace = sourceSite.1)
  (reflects : ∀ history, 0 < (M.historyReachWeight raw history).toReal →
    N.infoOf who (project history).trace = sourceSite.1 →
      M.infoOf who history.trace = rawSite.1)

include lengths laws reflects in
theorem informationHistoryReach_projection [DecidableEq T.History]
    (history : N.InformationHistory who sourceSite.1) :
    N.historyReachWeight source history.1 =
      ∑' original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then M.historyReachWeight raw original.1 else 0 :=
  fiber_sum M N project who rawSite sourceSite (M.historyReachWeight raw)
    (N.historyReachWeight source) (M.historyReachWeight_projection N raw source project lengths
        laws)
    (fun original present => reflects original
      (ENNReal.toReal_pos present (PMF.apply_ne_top _ _))) history

include lengths laws reflects maps in
theorem informationMass_projection :
    M.informationMass raw who rawSite = N.informationMass source who sourceSite := by
  classical
  exact fiber_mass M N project who rawSite sourceSite (M.historyReachWeight raw)
    (N.historyReachWeight source) maps
    (M.informationHistoryReach_projection N raw source project lengths laws who rawSite
      sourceSite reflects)

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
  exact M.bayes_projection N raw source project who rawSite sourceSite maps rawAntichain
    sourceAntichain rawPositive sourcePositive
    (M.informationHistoryReach_projection N raw source project lengths laws who rawSite
      sourceSite reflects)
    (M.informationMass_projection N raw source project lengths laws who rawSite sourceSite
      maps reflects)

end Aligned

section Depth

variable (who : Player) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
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
/-- A service block may consume a different number of steps than its source
action. At corresponding decision checkpoints, the actual prefix law still
transports reach weights by summing the compatible native histories. -/
theorem informationHistoryReach_projection_at_depth [DecidableEq T.History]
    (history : N.InformationHistory who sourceSite.1) :
    N.historyReachWeight source history.1 =
      ∑' original : M.InformationHistory who rawSite.1,
        if project original.1 = history.1 then M.historyReachWeight raw original.1 else 0 := by
  have fiber := fiber_sum M N project who rawSite sourceSite (M.runBehavioral raw rawDepth)
    (N.runBehavioral source sourceDepth)
    (fun target => by
      rw [← law, PMF.map_apply]
      apply tsum_congr
      intro original
      by_cases same : project original = target
      · rw [ite_eq_left same.symm, ite_eq_left same]
      · rw [ite_eq_right (Ne.symm same), ite_eq_right same])
    (fun original present => reflects original
      (ENNReal.toReal_pos present (PMF.apply_ne_top _ _))) history
  rw [historyReachWeight, sourceClock history, fiber]
  apply tsum_congr
  intro original
  rw [historyReachWeight, rawClock original]

include rawClock sourceClock law maps reflects in
theorem informationMass_projection_at_depth :
    M.informationMass raw who rawSite = N.informationMass source who sourceSite := by
  classical
  exact fiber_mass M N project who rawSite sourceSite (M.historyReachWeight raw)
    (N.historyReachWeight source) maps
    (M.informationHistoryReach_projection_at_depth N raw source project who rawSite
      sourceSite rawDepth sourceDepth rawClock sourceClock law reflects)

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
  exact M.bayes_projection N raw source project who rawSite sourceSite maps rawAntichain
    sourceAntichain rawPositive sourcePositive
    (M.informationHistoryReach_projection_at_depth N raw source project who rawSite
      sourceSite rawDepth sourceDepth rawClock sourceClock law reflects)
    (M.informationMass_projection_at_depth N raw source project who rawSite sourceSite
      rawDepth sourceDepth rawClock sourceClock law maps reflects)

end Depth

/-- A focal selector can single out one private alias history without changing
that player's Bayes belief. Only the selected profile must reflect the chosen
raw information fiber; the native profile may mix over many aliases. Source
and native checkpoints may occur at different depths. -/
theorem bayesBelief_projection_at_depth_of_focal_selector
    (native selected : ∀ who, M.BehavioralPolicy who)
    (source : ∀ who, N.BehavioralPolicy who)
    (project : E.History → T.History)
    (who : Player) (rawSite : M.InformationSite who) (sourceSite : N.InformationSite who)
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
