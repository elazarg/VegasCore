/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.ObservableEnforcement

/-! # Sanctions distinguish visible violations from hidden profitable deviations

The prescribed outcome pays zero and the deviating outcome pays one. An alarm
seeing a constant observation cannot deter this gain without false positives.
When it sees the outcome, the deterministic outside-set alarm with penalty one
does deter the same deviation, with the prescribed law still uncharged.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ObservableEnforcement

open GameTheory GameTheory.Math.Probability GameTheory.Enforcement

private def base (outcome : Bool) : ℝ := if outcome then 1 else 0

private theorem profitable : expect (PMF.pure false) base < expect (PMF.pure true) base := by
  simp [expect_pure, base]

/-- Both hidden outcomes have the same admitted observation. No randomized
sound alarm and no finite nonnegative penalty can remove the strict gain. -/
theorem hidden_deviation_cannot_be_deterred :
    ¬ ∃ (alarm : Unit → PMF Bool) (penalty : ℝ), 0 ≤ penalty ∧
      (∀ observation ∈ (Set.univ : Set Unit), ((alarm observation) true).toReal = 0) ∧
      (IncentiveComparison.mk (PMF.pure false) (PMF.pure true)).Holds
        (monitoredUtility base (fun _ => ()) alarm penalty) := by
  rw [exists_sound_sanction_iff (PMF.pure false) (PMF.pure true) base (fun _ => ()) Set.univ
    (fun _ _ => Set.mem_univ _) (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)
    profitable]
  simp

/-- Revealing the outcome creates positive unlawful mass, so the generic
criterion supplies a sound finite sanction for the very same comparison. -/
theorem visible_deviation_can_be_deterred :
    ∃ (alarm : Bool → PMF Bool) (penalty : ℝ), 0 ≤ penalty ∧
      (∀ observation ∈ ({false} : Set Bool), ((alarm observation) true).toReal = 0) ∧
      (IncentiveComparison.mk (PMF.pure false) (PMF.pure true)).Holds
        (monitoredUtility base id alarm penalty) := by
  apply (exists_sound_sanction_iff (PMF.pure false) (PMF.pure true) base id {false}
    (by intro outcome member; simpa using member)
    (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _) profitable).mpr
  simp [PMF.pure_map]

/-- The optimal alarm actually fires with probability one on the deviation. -/
theorem visible_detection :
    (((PMF.pure true).bind (outsideAlarm ({false} : Set Bool))) true).toReal = 1 := by
  rw [outsideAlarm_detection]
  simp

/-- Charging one utility unit makes both actual monitored payoffs zero. -/
theorem unit_penalty_deters :
    (IncentiveComparison.mk (PMF.pure false) (PMF.pure true)).Holds
      (monitoredUtility base id (outsideAlarm ({false} : Set Bool)) 1) := by
  rw [IncentiveComparison.holds_iff]
  simp [expect_pure, monitoredUtility_eq, base]

end GameTheoryExtensionsTests.ObservableEnforcement
