/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.DependencyHeight
import Mathlib.Tactic.FinCases

/-! # Parallel and serial completion depths -/

namespace VegasTests.DependencyHeight

open Vegas

def parallel (count : Nat) : EventOrder where
  eventCount := count
  predecessors _ := ∅
  predecessor_lt := by simp

def chain : EventOrder where
  eventCount := 3
  predecessors event :=
    if event.val = 0 then ∅ else if event.val = 1 then {0} else {1}
  predecessor_lt := by
    intro event predecessor member
    fin_cases event <;> simp_all

example : (parallel 0).dependencyHeight = 0 := by decide

example : (parallel 5).dependencyHeight = 1 := by
  have depth (event : Fin 5) : (parallel 5).dependencyDepth event = 1 := by
    rw [EventOrder.dependencyDepth]
    simp [parallel]
  apply le_antisymm
  · apply Finset.sup_le
    intro event _
    exact (depth event).le
  · have lower := (parallel 5).dependencyDepth_le_height (0 : Fin 5)
    simpa only [depth] using lower

example : chain.dependencyHeight = 3 := by
  have zero : chain.dependencyDepth (0 : Fin 3) = 1 := by
    rw [EventOrder.dependencyDepth]
    simp [chain]
  have one : chain.dependencyDepth (1 : Fin 3) = 2 := by
    rw [EventOrder.dependencyDepth]
    simpa [chain] using zero
  have two : chain.dependencyDepth (2 : Fin 3) = 3 := by
    rw [EventOrder.dependencyDepth]
    simpa [chain] using one
  apply le_antisymm
  · exact chain.dependencyHeight_le_eventCount
  · have lower := chain.dependencyDepth_le_height (2 : Fin 3)
    simpa only [two] using lower

end VegasTests.DependencyHeight
