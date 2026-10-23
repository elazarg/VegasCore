/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecall

/-! # Passive observation is hidden from scheduler state and recall

The scheduler chooses whom to activate. The observation kernel then samples
independently using the pending packets. The selected subset is private player
knowledge; every supported sample has exactly the same scheduler observation
and scheduler recall. Later public transmissions remain visible.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem activation_visible (execution next : app.Execution) (who : Principal)
    (reached : next ∈ (execution.environmentStep app (.activate who)).support) :
    next.observeEnvironment app = execution.observeEnvironment app ∧
      next.environmentRecall = execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .activate who⟩] := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
  exact ⟨rfl, rfl⟩

/-- A scheduler with arbitrary public-history memory makes the same next
choice at every private observation outcome of this activation. -/
theorem scheduler_after_activation (scheduler : app.Scheduler)
    (execution first second : app.Execution) (who : Principal)
    (firstReached : first ∈ (execution.environmentStep app (.activate who)).support)
    (secondReached : second ∈ (execution.environmentStep app (.activate who)).support) :
    scheduler first.environmentRecall (first.observeEnvironment app) =
      scheduler second.environmentRecall (second.observeEnvironment app) := by
  obtain ⟨firstView, firstRecall⟩ := app.activation_visible execution first who firstReached
  obtain ⟨secondView, secondRecall⟩ := app.activation_visible execution second who secondReached
  rw [firstView, secondView, firstRecall, secondRecall]

end Interaction.ReactiveApplication
