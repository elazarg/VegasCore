/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerImplementation
import Interaction.ReactiveStopping

/-! # Immutable scheduler seeds at actual stopping times

The actual bounded stopping evaluator retains the complete execution and
original scheduler seed. Stopping may depend on the entire current execution.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- An endogenous actual stopping rule preserves the joint realization of
an immutable scheduler seed and the complete stopped execution. -/
theorem schedulerMixture_runUntil_joint {Seed : Type} (prior : PMF Seed)
    (family : Seed → app.Scheduler) (players : Principal → app.Policy)
    (stop : app.Execution → Prop) [DecidablePred stop]
    (count : Nat) (execution : app.Execution) :
    ((app.schedulerMixture prior family).posterior execution.environmentRecall).bind
      (fun seed => (app.runUntil (family seed) players stop count execution).map
        fun next => (next, seed)) =
    (app.runUntil (app.schedulerMixture prior family).scheduler players stop count execution).bind
      fun next => ((app.schedulerMixture prior family).posterior next.environmentRecall).map
        (Prod.mk next) := by
  induction count generalizing execution with
  | zero =>
      simp only [runUntil, PMF.pure_map, PMF.pure_bind]
      rfl
  | succ count ih =>
      by_cases halt : stop execution
      · simp only [runUntil, halt, ↓reduceIte, PMF.pure_map, PMF.pure_bind]
        rfl
      · have split := (app.schedulerMixture prior family).command_disintegrate execution
          (fun command seed => (app.dispatch players command execution).bind fun next =>
            (app.runUntil (family seed) players stop count next).map fun final => (final, seed))
        conv at split =>
          lhs
          arg 2
          ext seed
          arg 1
          change (family seed execution.environmentRecall
            (execution.observeEnvironment app)).map (fun command => (command, seed))
        simp only [PMF.bind_map, Function.comp_def] at split
        simp only [runUntil, halt, ↓reduceIte, PMF.map_bind, round, PMF.bind_bind]
        rw [split]
        apply bind_congr_on_support _
        intro command _
        rw [PMF.bind_comm]
        apply bind_congr_on_support _
        intro next reached
        rw [← app.dispatch_environmentRecall players command execution next reached]
        exact ih next

end Interaction.ReactiveApplication
