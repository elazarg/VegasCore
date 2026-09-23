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
  obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
  obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
  exact ⟨rfl, rfl⟩

/-- The complete law visible to a scheduler is independent of the sampled leaks. -/
theorem activation_visible_law (execution : app.Execution) (who : Principal) :
    (execution.environmentStep app (.activate who)).map
      (fun next => (next.environmentRecall, next.observeEnvironment app)) =
        FinDist.pure (execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .activate who⟩],
          execution.observeEnvironment app) := by
  simp only [Execution.environmentStep, FinDist.map_comp]
  simp only [Function.comp_def, Execution.observeEnvironment, MessageNetwork.learn,
    MessageNetwork.publicView, FinDist.map_const]

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

/-- Private memory changes and silence reveal no evidence of the sampled
knowledge when control actually returns to the scheduler. -/
theorem scheduler_after_silent_response (scheduler : app.Scheduler)
    (execution first second : app.Execution) (who : Principal)
    (firstMemory secondMemory : app.Memory)
    (firstReached : first ∈ (execution.environmentStep app (.activate who)).support)
    (secondReached : second ∈ (execution.environmentStep app (.activate who)).support) :
    let left := first.respond app who ⟨firstMemory, none⟩
    let right := second.respond app who ⟨secondMemory, none⟩
    scheduler left.environmentRecall (left.observeEnvironment app) =
      scheduler right.environmentRecall (right.observeEnvironment app) := by
  change scheduler first.environmentRecall (first.observeEnvironment app) =
    scheduler second.environmentRecall (second.observeEnvironment app)
  exact app.scheduler_after_activation scheduler execution first second who
    firstReached secondReached

end Interaction.ReactiveApplication
