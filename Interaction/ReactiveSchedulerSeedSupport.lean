/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerBeforeResponse

/-! # Actual fixed-seed executions in behavioral posterior support

A supported posterior seed realizes the same observed execution under its
original immutable scheduler. The statement also holds at genuine active
decision boundaries, before any player response.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Every supported posterior seed has an actual original fixed-scheduler run. -/
theorem schedulerMixture_run_of_posterior_support {Seed : Type} (prior : PMF Seed)
    (family : Seed → app.Scheduler) (players : Principal → app.Policy)
    (count : Nat) (state : app.State) (execution : app.Execution) (seed : Seed)
    (reached : execution ∈
      (app.runRounds (app.schedulerMixture prior family).scheduler players count
        (Execution.initial app state)).support)
    (supported : seed ∈
      ((app.schedulerMixture prior family).posterior execution.environmentRecall).support) :
    seed ∈ prior.support ∧
      execution ∈ (app.runRounds (family seed) players count
        (Execution.initial app state)).support := by
  have joined : (execution, seed) ∈
      ((app.runRounds (app.schedulerMixture prior family).scheduler players count
        (Execution.initial app state)).bind fun next =>
          ((app.schedulerMixture prior family).posterior next.environmentRecall).map
            (Prod.mk next)).support := by
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨execution, reached,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨seed, supported, rfl⟩⟩
  rw [← app.schedulerMixture_joint prior family players count state] at joined
  obtain ⟨chosen, chosenSupport, actual⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ joined)
  obtain ⟨realized, runSupport, same⟩ := (PMF.mem_support_map_iff _ _ _).mp actual
  cases same
  exact ⟨chosenSupport, runSupport⟩

/-- At a supported actual next command, every posterior seed realizes an
original fixed-scheduler prefix and genuine environment step to that decision. -/
theorem schedulerMixture_decision_of_posterior_support {Seed : Type} (prior : PMF Seed)
    (family : Seed → app.Scheduler) (players : Principal → app.Policy)
    (count : Nat) (state : app.State) (execution next : app.Execution)
    (command : app.Command) (seed : Seed)
    (reached : execution ∈
      (app.runRounds (app.schedulerMixture prior family).scheduler players count
        (Execution.initial app state)).support)
    (chosen : command ∈ ((app.schedulerMixture prior family).scheduler execution.environmentRecall
      (execution.observeEnvironment app)).support)
    (observed : next ∈ (execution.environmentStep app command).support)
    (supported : seed ∈
      ((app.schedulerMixture prior family).posterior next.environmentRecall).support) :
    seed ∈ prior.support ∧ ∃ original,
      original ∈ (app.runRounds (family seed) players count
        (Execution.initial app state)).support ∧
      command ∈ (family seed original.environmentRecall
        (original.observeEnvironment app)).support ∧
      next ∈ (original.environmentStep app command).support := by
  have joined : (command, next, seed) ∈
      ((app.runRounds (app.schedulerMixture prior family).scheduler players count
        (Execution.initial app state)).bind fun before =>
          ((app.schedulerMixture prior family).scheduler before.environmentRecall
            (before.observeEnvironment app)).bind fun selected =>
              (before.environmentStep app selected).bind fun after =>
                ((app.schedulerMixture prior family).posterior after.environmentRecall).map
                  fun value => (selected, after, value)).support := by
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨execution, reached, ?_⟩
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨command, chosen, ?_⟩
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨next, observed,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨seed, supported, rfl⟩⟩
  rw [← app.schedulerMixture_beforeResponse_joint prior family players count state] at joined
  obtain ⟨value, valueSupport, afterSeed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ joined)
  obtain ⟨original, originalSupport, afterRun⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterSeed)
  obtain ⟨selected, selectedSupport, afterCommand⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterRun)
  obtain ⟨actual, actualSupport, same⟩ := (PMF.mem_support_map_iff _ _ _).mp afterCommand
  cases same
  exact ⟨valueSupport, original, originalSupport, selectedSupport, actualSupport⟩

end Interaction.ReactiveApplication
