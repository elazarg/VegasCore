/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds
import GameTheory.Protocol.PrivateStrategy

/-! # Private implementations of reactive schedulers

A scheduler may retain private memory across commands. Behavioral realization
conditions that memory on its actual environment views and commands. Memory
stays outside the execution state, including for an initially sampled seed.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- Reconstruct scheduler inputs at their original recall prefixes, newest first. -/
def schedulerTranscriptFrom (earlier : List app.EnvironmentEntry) :
    List app.EnvironmentEntry →
      PrivateStrategy.Transcript (List app.EnvironmentEntry × app.EnvironmentView) app.Command
  | [] => []
  | entry :: rest => schedulerTranscriptFrom (earlier ++ [entry]) rest ++
      [((earlier, entry.beforeView), entry.command)]

theorem schedulerTranscriptFrom_append (earlier left right : List app.EnvironmentEntry) :
    app.schedulerTranscriptFrom earlier (left ++ right) =
      app.schedulerTranscriptFrom (earlier ++ left) right ++
        app.schedulerTranscriptFrom earlier left := by
  induction left generalizing earlier with
  | nil => simp [schedulerTranscriptFrom]
  | cons entry rest ih => simp [schedulerTranscriptFrom, ih, List.append_assoc]

/-- The actual scheduler's observed input/output transcript. -/
def schedulerTranscript (past : List app.EnvironmentEntry) := app.schedulerTranscriptFrom [] past

theorem schedulerTranscript_snoc (past : List app.EnvironmentEntry) (entry : app.EnvironmentEntry) :
    app.schedulerTranscript (past ++ [entry]) =
      ((past, entry.beforeView), entry.command) :: app.schedulerTranscript past := by
  simp [schedulerTranscript, schedulerTranscriptFrom_append, schedulerTranscriptFrom]

/-- Private scheduler state is an implementation detail, absent from runtime state. -/
abbrev SchedulerImplementation (Memory : Type) :=
  PrivateStrategy.Strategy Memory (List app.EnvironmentEntry × app.EnvironmentView) app.Command

namespace SchedulerImplementation

variable {app} {Memory : Type} (implementation : app.SchedulerImplementation Memory)

/-- The private memory law after the recorded environment commands. -/
def posterior (past : List app.EnvironmentEntry) : PMF Memory :=
  PrivateStrategy.posterior implementation (app.schedulerTranscript past)

/-- The behavioral scheduler corresponding to the private implementation. -/
def scheduler : app.Scheduler := fun past view =>
  PrivateStrategy.behavioral implementation (app.schedulerTranscript past) (past, view)

theorem posterior_snoc (past : List app.EnvironmentEntry) (entry : app.EnvironmentEntry) :
    implementation.posterior (past ++ [entry]) =
      (fiberPosterior ((implementation.posterior past).bind fun memory =>
        implementation.respond memory (past, entry.beforeView))
          Prod.fst entry.command).map Prod.snd := by
  rw [posterior, app.schedulerTranscript_snoc]
  rfl

theorem scheduler_eq (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    implementation.scheduler past view =
      ((implementation.posterior past).bind fun memory =>
        implementation.respond memory (past, view)).map Prod.fst := rfl

/-- Disintegrating one actual command retains both the output and next memory. -/
theorem command_disintegrate {Result : Type} (execution : app.Execution)
    (next : app.Command → Memory → PMF Result) :
    (implementation.posterior execution.environmentRecall).bind (fun memory =>
      (implementation.respond memory
        (execution.environmentRecall, execution.observeEnvironment app)).bind
          fun response => next response.1 response.2) =
      (implementation.scheduler execution.environmentRecall
        (execution.observeEnvironment app)).bind fun command =>
          (implementation.posterior (execution.environmentRecall ++
            [⟨execution.observeEnvironment app, command⟩])).bind (next command) := by
  let law := (implementation.posterior execution.environmentRecall).bind fun memory =>
    implementation.respond memory (execution.environmentRecall, execution.observeEnvironment app)
  rw [← PMF.bind_bind]
  change law.bind (fun response => next response.1 response.2) = _
  conv_lhs => arg 1; rw [eq_bind_fst_fiberPosterior_snd law]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, scheduler_eq, posterior_snoc, law]

variable [DecidableEq Principal]

/-- Execute genuine scheduler rounds while keeping private memory outside the runtime. -/
def runJoint (players : Principal → app.Policy) :
    Nat → app.Execution → Memory → PMF (app.Execution × Memory)
  | 0, execution, memory => PMF.pure (execution, memory)
  | count + 1, execution, memory =>
      (implementation.respond memory
        (execution.environmentRecall, execution.observeEnvironment app)).bind fun response =>
          (app.dispatch players response.1 execution).bind fun next =>
            runJoint players count next response.2

/-- The full joint law of actual execution and private memory is recovered by
running the behavioral scheduler and conditioning on its final recorded recall. -/
theorem realizeJoint (players : Principal → app.Policy) (count : Nat)
    (execution : app.Execution) :
    (implementation.posterior execution.environmentRecall).bind
        (implementation.runJoint players count execution) =
      (app.runRounds implementation.scheduler players count execution).bind fun next =>
        (implementation.posterior next.environmentRecall).map (Prod.mk next) := by
  induction count generalizing execution with
  | zero =>
      simp only [runJoint, runRounds, PMF.pure_bind]
      rfl
  | succ count ih =>
      change (implementation.posterior execution.environmentRecall).bind (fun memory =>
        (implementation.respond memory
          (execution.environmentRecall, execution.observeEnvironment app)).bind fun response =>
            (app.dispatch players response.1 execution).bind fun next =>
              implementation.runJoint players count next response.2) = _
      rw [implementation.command_disintegrate execution (fun command memory =>
        (app.dispatch players command execution).bind fun next =>
          implementation.runJoint players count next memory)]
      simp only [runRounds, round, PMF.bind_bind]
      apply bind_congr_on_support _
      intro command _
      rw [PMF.bind_comm]
      apply bind_congr_on_support _
      intro next reached
      rw [← app.dispatch_environmentRecall players command execution next reached]
      exact ih next

/-- Behavioral realization preserves the complete execution law. -/
theorem realize (players : Principal → app.Policy) (count : Nat) (execution : app.Execution) :
    ((implementation.posterior execution.environmentRecall).bind
      (implementation.runJoint players count execution)).map Prod.fst =
        app.runRounds implementation.scheduler players count execution := by
  rw [implementation.realizeJoint]
  simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.bind_const,
    PMF.bind_pure]

end SchedulerImplementation

/-- Sample one private seed and retain the selected existing scheduler throughout the run. -/
def schedulerMixture {Seed : Type} (prior : PMF Seed) (family : Seed → app.Scheduler) :
    app.SchedulerImplementation Seed where
  initial := prior
  respond seed input := (family seed input.1 input.2).map fun command => (command, seed)

variable [DecidableEq Principal]

/-- The private mixture runs the existing scheduler selected by its fixed seed. -/
theorem schedulerMixture_runJoint {Seed : Type} (prior : PMF Seed) (family : Seed → app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution : app.Execution) (seed : Seed) :
    (app.schedulerMixture prior family).runJoint players count execution seed =
      (app.runRounds (family seed) players count execution).map fun next => (next, seed) := by
  induction count generalizing execution with
  | zero => simp only [SchedulerImplementation.runJoint, runRounds, PMF.pure_map]
  | succ count ih =>
      change ((family seed execution.environmentRecall (execution.observeEnvironment app)).map
        (fun command => (command, seed))).bind (fun response =>
          (app.dispatch players response.1 execution).bind fun next =>
            (app.schedulerMixture prior family).runJoint players count next response.2) = _
      simp only [PMF.bind_map, Function.comp_def, runRounds, round, PMF.map_bind, PMF.bind_bind]
      apply bind_congr_on_support _
      intro command _
      apply bind_congr_on_support _
      intro next _
      exact ih next

/-- Sampling an independent scheduler seed once has exactly the joint law
obtained from its behavioral scheduler and the final seed posterior. -/
theorem schedulerMixture_joint {Seed : Type} (prior : PMF Seed) (family : Seed → app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (state : app.State) :
    (prior.bind fun seed =>
      (app.runRounds (family seed) players count (Execution.initial app state)).map
        fun next => (next, seed)) =
      (app.runRounds (app.schedulerMixture prior family).scheduler players count
        (Execution.initial app state)).bind fun next =>
          ((app.schedulerMixture prior family).posterior next.environmentRecall).map
            (Prod.mk next) := by
  have joint := (app.schedulerMixture prior family).realizeJoint players count
    (Execution.initial app state)
  change (prior.bind fun seed => (app.schedulerMixture prior family).runJoint players count
    (Execution.initial app state) seed) = _ at joint
  simpa only [schedulerMixture_runJoint] using joint

/-- A fixed independent seed mixture and its behavioral scheduler have the same
complete execution law for every initial state and every player profile. -/
theorem schedulerMixture_realize {Seed : Type} (prior : PMF Seed) (family : Seed → app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (state : app.State) :
    (prior.bind fun seed =>
      app.runRounds (family seed) players count (Execution.initial app state)) =
      app.runRounds (app.schedulerMixture prior family).scheduler players count
        (Execution.initial app state) := by
  have joint := congrArg (fun law => law.map Prod.fst)
    (app.schedulerMixture_joint prior family players count state)
  simpa only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.bind_const,
    PMF.bind_pure] using joint

end Interaction.ReactiveApplication
