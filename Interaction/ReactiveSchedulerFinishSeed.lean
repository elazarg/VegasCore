/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveSchedulerImplementation

/-! # Original scheduler seeds through full physical continuations -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- A pending response and the complete remaining execution retain the original
scheduler seed, with the actual transcript posterior at each boundary. -/
theorem schedulerMixture_finish_joint {Seed : Type} (prior : PMF Seed)
    (family : Seed → app.Scheduler) (initial : PMF app.State) (horizon : Nat)
    (players : Principal → app.Policy) (state : app.ProtocolState) :
    ((match state with
      | none => prior
      | some current => (app.schedulerMixture prior family).posterior
          current.execution.environmentRecall).bind fun seed =>
        (app.finish initial horizon (family seed) players state).map
          fun final => (final, seed)) =
      (app.finish initial horizon (app.schedulerMixture prior family).scheduler players state).bind
        fun final => (match final with
          | none => prior
          | some current => (app.schedulerMixture prior family).posterior
              current.execution.environmentRecall).map (Prod.mk final) := by
  cases state with
  | none =>
      simp only [finish, PMF.map_bind, PMF.map_comp, Function.comp_def]
      rw [PMF.bind_comm]
      simp only [PMF.bind_bind, PMF.bind_map, finished]
      apply bind_congr_on_support _
      intro state _
      have joint := congrArg (PMF.map fun result : app.Execution × Seed =>
        (app.finished result.1, result.2))
          (app.schedulerMixture_joint prior family players horizon state)
      simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_map, finished]
        using joint
  | some current =>
      simp only [finish, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_bind,
        PMF.bind_map, finished]
      rw [PMF.bind_comm]
      apply bind_congr_on_support _
      intro execution reached
      rw [← app.resume_environmentRecall players current.actor current.execution execution reached]
      have joint := congrArg (PMF.map fun result : app.Execution × Seed =>
        (app.finished result.1, result.2))
          ((app.schedulerMixture prior family).realizeJoint players current.remaining execution)
      simpa only [schedulerMixture_runJoint, PMF.map_bind, PMF.map_comp,
        Function.comp_def, PMF.bind_map, finished] using joint

end Interaction.ReactiveApplication
