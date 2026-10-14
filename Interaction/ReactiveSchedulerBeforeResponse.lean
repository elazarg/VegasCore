/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerImplementation
import Interaction.ReactiveResponseAccounting

/-! # Seeded scheduler laws before the selected player's response

The next command and its genuine environment effects can be observed before
the active player responds. Behavioral realization retains the exact joint
seed law at that decision boundary.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- A fixed seed mixture realizes the full law at the actual next command and
environment step, before invoking any selected player's response. -/
theorem schedulerMixture_beforeResponse_joint {Seed : Type} (prior : PMF Seed)
    (family : Seed → app.Scheduler) (players : Principal → app.Policy)
    (count : Nat) (state : app.State) :
    (prior.bind fun seed =>
      (app.runRounds (family seed) players count (Execution.initial app state)).bind
        fun execution =>
          (family seed execution.environmentRecall (execution.observeEnvironment app)).bind
            fun command => (execution.environmentStep app command).map
              fun next => (command, next, seed)) =
      (app.runRounds (app.schedulerMixture prior family).scheduler players count
        (Execution.initial app state)).bind fun execution =>
          ((app.schedulerMixture prior family).scheduler execution.environmentRecall
            (execution.observeEnvironment app)).bind fun command =>
              (execution.environmentStep app command).bind fun next =>
                ((app.schedulerMixture prior family).posterior next.environmentRecall).map
                  fun seed => (command, next, seed) := by
  let implementation := app.schedulerMixture prior family
  let follow : app.Execution × Seed → PMF (app.Command × app.Execution × Seed) := fun pair =>
    (family pair.2 pair.1.environmentRecall (pair.1.observeEnvironment app)).bind fun command =>
      (pair.1.environmentStep app command).map fun next => (command, next, pair.2)
  have transferred := congrArg (fun law => law.bind follow)
    (app.schedulerMixture_joint prior family players count state)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, follow] at transferred
  rw [transferred]
  apply bind_congr_on_support _
  intro execution _
  have disintegrated := implementation.command_disintegrate execution
    (fun command seed => (execution.environmentStep app command).map
      fun next => (command, next, seed))
  have respondEq : ∀ seed input, implementation.respond seed input =
      (family seed input.1 input.2).map (fun command => (command, seed)) := fun _ _ => rfl
  simp only [respondEq, PMF.bind_map, Function.comp_def] at disintegrated
  rw [disintegrated]
  apply bind_congr_on_support _
  intro command _
  simp only [PMF.map]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro next reached
  rw [app.environmentStep_environmentRecall execution next command reached]
  rfl

end Interaction.ReactiveApplication
