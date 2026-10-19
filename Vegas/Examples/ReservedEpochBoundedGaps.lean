/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.ReservedEpochUsableConcurrency

/-! # Bounded gaps in the correlated concurrent service environment -/

namespace Vegas.Examples.ReservedEpochConcurrency

open EventGraphRuntime

theorem tape_processing (reverse : Bool) (cycle : Nat) :
    (tape reverse).processes cycle = if cycle % 3 = 1 then !reverse else true := rfl

theorem tape_boundedGaps (reverse : Bool) (cycles : Nat) :
    (tape reverse).BoundedGaps cycles 1 2 where
  activation cycle _ owner := ⟨cycle, le_rfl, by omega, rfl⟩
  processing cycle _ := by
    by_cases current : (tape reverse).processes cycle = true
    · exact ⟨cycle, le_rfl, by omega, current⟩
    · have position : cycle % 3 = 1 := by
        by_contra other
        exact current (by simp only [tape_processing, other, ↓reduceIte])
      have next : (cycle + 1) % 3 ≠ 1 := by omega
      exact ⟨cycle + 1, by omega, by omega, by
        simp only [tape_processing, next, ↓reduceIte]⟩

theorem supported_tape_boundedGaps (selected : ReservedEpoch.Tape Player 2)
    (supported : selected ∈ prior.support) (cycles : Nat) :
    selected.BoundedGaps cycles 1 2 := by
  rw [prior, PMF.support_map] at supported
  obtain ⟨reverse, _positive, rfl⟩ := supported
  exact tape_boundedGaps reverse cycles

end Vegas.Examples.ReservedEpochConcurrency
