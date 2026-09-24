/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveImplementation

/-! # Private implementation realization at a pending response

A continuation can start after activation, before the player's response.
Conditioning private implementation state on own recall gives the same
completion law at that boundary as the behavioral realization. This supplies
the response boundary needed for sequential continuation comparisons.
-/

noncomputable section

namespace Interaction.ReactiveApplication.Implementation

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  {Memory : Type} (implementation : app.Implementation Memory)

theorem realize_continuation (who : Principal) (players : Principal → app.Policy)
    (scheduler : app.Scheduler) (count : Nat) (actor : Option Principal)
    (execution : app.Execution) :
    (implementation.posterior (execution.recall who)).bind (fun memory =>
      (implementation.resume who players actor execution memory).bind fun result =>
        implementation.run who players scheduler count result.1 result.2) =
      (app.resume (Function.update players who implementation.policy) actor execution).bind
        (app.runRounds scheduler (Function.update players who implementation.policy) count) := by
  cases actor with
  | none =>
      simpa only [resume, ReactiveApplication.resume, FinDist.pure_bind] using
        implementation.realize who players scheduler count execution
  | some owner =>
      by_cases same : owner = who
      · subst owner
        simp only [resume, ↓reduceIte, FinDist.bind_map]
        rw [implementation.response_disintegrate]
        simp only [implementation.realize, ReactiveApplication.resume, invoke,
          Function.update_self, FinDist.bind_map]
      · simp only [resume, same, ↓reduceIte, FinDist.bind_map,
          ReactiveApplication.resume, invoke, Function.update_of_ne same]
        rw [FinDist.bind_comm]
        apply FinDist.bind_congr
        intro action _
        rw [← app.respond_recall_other execution owner who (Ne.symm same) action]
        exact implementation.realize who players scheduler count _

end Interaction.ReactiveApplication.Implementation
