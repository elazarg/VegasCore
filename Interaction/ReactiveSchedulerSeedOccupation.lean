/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveControlOccupation
import Interaction.ReactiveSchedulerBeforeResponse

/-! # Original persistent seeds in actual bounded command occupation -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- The original fixed scheduler seed and complete current control have exactly
the behavioral occupation law tagged by the actual full-transcript posterior. -/
theorem schedulerMixture_occupation_joint {Seed : Type} (prior : PMF Seed)
    (family : Seed → app.Scheduler) (players : Principal → app.Policy)
    (initial : PMF app.State) (horizon : Nat) [NeZero horizon] :
    (prior.bind fun seed =>
      (app.occupationControlLaw (family seed) players initial horizon).map
        fun state => (state, seed)) =
      (app.occupationControlLaw (app.schedulerMixture prior family).scheduler players
        initial horizon).bind fun state =>
          (match state with
          | none => prior
          | some current => (app.schedulerMixture prior family).posterior
              current.execution.environmentRecall).map (Prod.mk state) := by
  classical
  simp only [occupationControlLaw, commandControlLaw, PMF.map_bind, PMF.map_comp,
    Function.comp_def, PMF.bind_bind, PMF.bind_map]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro time _
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro state _
  have realized := app.schedulerMixture_beforeResponse_joint prior family players time.val state
  have mapped := congrArg (PMF.map fun outcome : app.Command × app.Execution × Seed =>
    (some (⟨horizon - time.val - 1, outcome.1.actor? app, outcome.2.1⟩ : app.Control),
      outcome.2.2)) realized
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
  convert mapped using 1

end Interaction.ReactiveApplication
