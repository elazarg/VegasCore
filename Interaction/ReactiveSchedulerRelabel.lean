/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveSchedulerImplementation
import GameTheory.Math.Probability.ConditionalObservation

/-! # Relabeling the initialized private scheduler seed -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal First Second : Type} (app : ReactiveApplication Principal)

/-- Projection of private seed memory commutes with its complete posterior,
including fallback at an impossible recorded command. -/
theorem schedulerMixture_posterior_map (prior : PMF First) (project : First → Second)
    (members : Second → app.Scheduler) (past : List app.EnvironmentEntry) :
    ((app.schedulerMixture prior (fun seed => members (project seed))).posterior past).map project =
      (app.schedulerMixture (prior.map project) members).posterior past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [SchedulerImplementation.posterior_snoc, SchedulerImplementation.posterior_snoc]
      let joint := ((app.schedulerMixture prior (fun seed => members (project seed))).posterior
        past).bind fun seed => (members (project seed) past entry.beforeView).map
          (fun command => (command, seed))
      have jointEq : joint.map (fun pair => (pair.1, project pair.2)) =
          ((app.schedulerMixture (prior.map project) members).posterior past).bind
            (fun seed => (members seed past entry.beforeView).map
              fun command => (command, seed)) := by
        rw [← ih]
        simp only [joint, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
      have projected : ((fiberPosterior joint Prod.fst entry.command).map Prod.snd).map project =
          (fiberPosterior (joint.map (fun pair => (pair.1, project pair.2))) Prod.fst
            entry.command).map Prod.snd := by
        by_cases present : entry.command ∈ (joint.map Prod.fst).support
        · have transported := map_fiberPosterior_readout joint
            (fun pair => (pair.1, project pair.2)) Prod.fst entry.command present
          have mapped := congrArg (PMF.map Prod.snd) transported
          simpa only [PMF.map_comp, Function.comp_def] using mapped
        · have absent : entry.command ∉
              ((joint.map (fun pair => (pair.1, project pair.2))).map Prod.fst).support := by
            simpa only [PMF.map_comp, Function.comp_def] using present
          rw [fiberPosterior_of_not_mem_support _ _ present,
            fiberPosterior_of_not_mem_support _ _ absent]
          simp only [PMF.map_comp, Function.comp_def]
      exact projected.trans
        (congrArg (fun law => (fiberPosterior law Prod.fst entry.command).map Prod.snd) jointEq)

/-- The installed behavioral scheduler is unchanged on every transcript,
not only on supported initial executions. -/
theorem schedulerMixture_scheduler_map (prior : PMF First) (project : First → Second)
    (members : Second → app.Scheduler) :
    (app.schedulerMixture prior (fun seed => members (project seed))).scheduler =
      (app.schedulerMixture (prior.map project) members).scheduler := by
  funext past view
  rw [SchedulerImplementation.scheduler_eq, SchedulerImplementation.scheduler_eq]
  rw [← app.schedulerMixture_posterior_map prior project members past]
  simp only [schedulerMixture, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

end Interaction.ReactiveApplication
