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

/-- Equal player inputs and pending pools give equal actual inputs after
passive observation, including the player's complete response recall. -/
theorem activation_info_congr (left right : app.Execution) (who : Principal)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (localView : app.observePlayer left.application who =
      app.observePlayer right.application who)
    (recall : left.recall who = right.recall who) :
    (left.environmentStep app (.activate who)).map
        (fun next => (next.recall who, next.observe app who)) =
      (right.environmentStep app (.activate who)).map
        (fun next => (next.recall who, next.observe app who)) := by
  simp only [Execution.environmentStep, PMF.map_comp, Function.comp_def,
    Execution.observe]
  rw [network, receipts, localView, recall]

theorem activation_visible (execution next : app.Execution) (who : Principal)
    (reached : next ∈ (execution.environmentStep app (.activate who)).support) :
    next.observeEnvironment app = execution.observeEnvironment app ∧
      next.environmentRecall = execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .activate who⟩] := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
  exact ⟨rfl, rfl⟩

/-- The complete law visible to a scheduler is independent of the sampled leaks. -/
theorem activation_visible_law (execution : app.Execution) (who : Principal) :
    (execution.environmentStep app (.activate who)).map
      (fun next => (next.environmentRecall, next.observeEnvironment app)) =
        PMF.pure (execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .activate who⟩],
          execution.observeEnvironment app) := by
  simp only [Execution.environmentStep, PMF.map_comp]
  simp only [Function.comp_def, Execution.observeEnvironment, MessageNetwork.learn,
    MessageNetwork.publicView, PMF.map_const]

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

/-- Silence reveals no evidence of the sampled
knowledge when control actually returns to the scheduler. -/
theorem scheduler_after_silent_response (scheduler : app.Scheduler)
    (execution first second : app.Execution) (who : Principal)
    (firstReached : first ∈ (execution.environmentStep app (.activate who)).support)
    (secondReached : second ∈ (execution.environmentStep app (.activate who)).support) :
    let left := first.respond app who ⟨none⟩
    let right := second.respond app who ⟨none⟩
    scheduler left.environmentRecall (left.observeEnvironment app) =
      scheduler right.environmentRecall (right.observeEnvironment app) := by
  change scheduler first.environmentRecall (first.observeEnvironment app) =
    scheduler second.environmentRecall (second.observeEnvironment app)
  exact app.scheduler_after_activation scheduler execution first second who
    firstReached secondReached

end Interaction.ReactiveApplication
