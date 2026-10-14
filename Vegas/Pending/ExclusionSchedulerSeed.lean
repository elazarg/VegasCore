/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionSchedulerLift
import Interaction.ReactiveSchedulerImplementation

/-! # Persistent scheduler seeds through recovery command lifting -/

noncomputable section

namespace Vegas.EventGraphRuntime.RecoveryProjection

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "native" => runtime.reactiveApplication leaks
local notation "recovery" => runtime.recoveryApplication leaks

private theorem posterior_liftCommand {Seed : Type}
    (law : PMF ((native).Command × Seed)) (chosen : (recovery).Command) :
    (fiberPosterior (law.map fun result => (liftCommand runtime leaks result.1, result.2))
      Prod.fst chosen).map Prod.snd =
        (fiberPosterior law Prod.fst (command runtime leaks chosen)).map Prod.snd := by
  classical
  let read := fun result : (native).Command × Seed =>
    (liftCommand runtime leaks result.1, result.2)
  have sameFiber : fiberPosterior law (Prod.fst ∘ read) chosen =
      fiberPosterior law Prod.fst (command runtime leaks chosen) := by
    apply fiberPosterior_eq_of_support_fiber
    intro result _
    change liftCommand runtime leaks result.1 = chosen ↔
      result.1 = command runtime leaks chosen
    constructor
    · intro equal
      simpa only [command_liftCommand] using congrArg (command runtime leaks) equal
    · intro equal
      simpa only [liftCommand_command] using congrArg (liftCommand runtime leaks) equal
  have transported : (fiberPosterior law (Prod.fst ∘ read) chosen).map read =
      fiberPosterior (law.map read) Prod.fst chosen := by
    by_cases present : chosen ∈ (law.map (Prod.fst ∘ read)).support
    · exact map_fiberPosterior_readout law read Prod.fst chosen present
    · have absent : chosen ∉ ((law.map read).map Prod.fst).support := by
        simpa only [PMF.map_comp] using present
      rw [fiberPosterior_of_not_mem_support law _ present,
        fiberPosterior_of_not_mem_support _ _ absent]
  rw [sameFiber] at transported
  have projected := congrArg (PMF.map Prod.snd) transported
  simpa only [PMF.map_comp, Function.comp_def, read] using projected.symm

/-- The actual posterior of a persistent lifted scheduler seed is the native
posterior at the projected full environment transcript, including zero fibers. -/
theorem schedulerMixture_liftScheduler_posterior {Seed : Type}
    (prior : PMF Seed) (family : Seed → (native).Scheduler)
    (past : List (recovery).EnvironmentEntry) :
    (((recovery).schedulerMixture prior
      (fun seed => liftScheduler runtime leaks (family seed))).posterior past) =
      (((native).schedulerMixture prior family).posterior
        (past.map (environmentEntry runtime leaks))) := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [ReactiveApplication.SchedulerImplementation.posterior_snoc, List.map_append,
        List.map_singleton, ReactiveApplication.SchedulerImplementation.posterior_snoc, ih]
      simp only [ReactiveApplication.schedulerMixture, liftScheduler, PMF.map_comp,
        Function.comp_def, environmentEntry]
      have lifted := posterior_liftCommand runtime leaks
        ((((native).schedulerMixture prior family).posterior
          (past.map (environmentEntry runtime leaks))).bind fun seed =>
            (family seed (past.map (environmentEntry runtime leaks))
              (environmentView runtime leaks entry.beforeView)).map
                fun selected => (selected, seed))
        entry.command
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
        ReactiveApplication.schedulerMixture] at lifted
      convert lifted using 1

/-- Mixing lifted fixed schedulers gives exactly the lift of the native
behavioral mixture; no seed is resampled along a run. -/
theorem schedulerMixture_liftScheduler_scheduler {Seed : Type}
    (prior : PMF Seed) (family : Seed → (native).Scheduler) :
    ((recovery).schedulerMixture prior
      (fun seed => liftScheduler runtime leaks (family seed))).scheduler =
        liftScheduler runtime leaks (((native).schedulerMixture prior family).scheduler) := by
  funext past view
  rw [ReactiveApplication.SchedulerImplementation.scheduler_eq,
    schedulerMixture_liftScheduler_posterior]
  change _ = ((((native).schedulerMixture prior family).scheduler
    (past.map (environmentEntry runtime leaks)) (environmentView runtime leaks view)).map
      (liftCommand runtime leaks))
  rw [ReactiveApplication.SchedulerImplementation.scheduler_eq]
  simp only [ReactiveApplication.schedulerMixture, liftScheduler, PMF.map_bind,
    PMF.map_comp, Function.comp_def]

end Vegas.EventGraphRuntime.RecoveryProjection
