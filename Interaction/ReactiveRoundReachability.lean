/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu
import Interaction.ReactiveRounds
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Legal histories occur in the round evaluator

A response family with support on every menu action witnesses every legal
history. At a pending activation the witness stops after the environment step;
at scheduler control it stops after a complete round. Thus round-based service
proofs also apply at off-path decision histories, without assuming those
histories have positive probability in an equilibrium assessment.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)

end ResponseMenu

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

open GameTheory.Protocol GameTheory.Math.Probability

/-- Initialization followed by a specified number of complete scheduler rounds. -/
def roundsFrom (initial : PMF app.State) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) : PMF app.Execution :=
  initial.bind fun state => app.runRounds scheduler players count (Execution.initial app state)

theorem roundsFrom_succ (initial : PMF app.State) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) :
    app.roundsFrom initial scheduler players (count + 1) =
      (app.roundsFrom initial scheduler players count).bind (app.round scheduler players) := by
  unfold roundsFrom
  simp only [app.runRounds_add scheduler players count 1, PMF.bind_bind]
  congr 1
  funext state
  apply bind_congr_on_support _
  intro execution _
  simp only [runRounds, PMF.bind_pure]
end Interaction.ReactiveApplication
