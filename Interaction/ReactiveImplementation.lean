/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds
import Interaction.ReactiveRecall
import GameTheoryExtensions.Protocol.PrivateStrategy
import GameTheoryExtensions.Math.Probability.Conditioning

/-! # Private implementations of reactive behavioral policies

An implementation carries internal state between activations. Its behavioral
realization conditions that state on the player's own observed inputs and
semantic responses. Implementation state is absent from the execution result
and is never passed to opponents, the application, or the scheduler.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- Reconstruct inputs at their original recall prefixes, most recent first. -/
def privateTranscriptFrom (earlier : List app.PlayerEntry) : List app.PlayerEntry →
    PrivateStrategy.Transcript (List app.PlayerEntry × app.PlayerView) app.Action
  | [] => []
  | entry :: rest => privateTranscriptFrom (earlier ++ [entry]) rest ++
      [((earlier, entry.beforeView), entry.action)]

theorem privateTranscriptFrom_append (earlier left right : List app.PlayerEntry) :
    app.privateTranscriptFrom earlier (left ++ right) =
      app.privateTranscriptFrom (earlier ++ left) right ++
        app.privateTranscriptFrom earlier left := by
  induction left generalizing earlier with
  | nil => simp [privateTranscriptFrom]
  | cons entry rest ih =>
      simp [privateTranscriptFrom, ih, List.append_assoc]

def privateTranscript (past : List app.PlayerEntry) := app.privateTranscriptFrom [] past

theorem privateTranscript_snoc (past : List app.PlayerEntry) (entry : app.PlayerEntry) :
    app.privateTranscript (past ++ [entry]) =
      ((past, entry.beforeView), entry.action) :: app.privateTranscript past := by
  simp [privateTranscript, privateTranscriptFrom_append, privateTranscriptFrom]

abbrev Implementation (Memory : Type) :=
  PrivateStrategy.Strategy Memory (List app.PlayerEntry × app.PlayerView) app.Action

namespace Implementation

variable {app} {Memory : Type} (implementation : app.Implementation Memory)

def posterior (past : List app.PlayerEntry) : PMF Memory :=
  PrivateStrategy.posterior implementation (app.privateTranscript past)

def policy : app.Policy := fun past view =>
  PrivateStrategy.behavioral implementation (app.privateTranscript past) (past, view)

theorem posterior_snoc (past : List app.PlayerEntry) (entry : app.PlayerEntry) :
    implementation.posterior (past ++ [entry]) =
      (fiberConditional ((implementation.posterior past).bind fun memory =>
        implementation.respond memory (past, entry.beforeView))
          Prod.fst entry.action).map Prod.snd := by
  rw [posterior, app.privateTranscript_snoc]
  rfl

theorem policy_eq (past : List app.PlayerEntry) (view : app.PlayerView) :
    implementation.policy past view =
      ((implementation.posterior past).bind fun memory =>
        implementation.respond memory (past, view)).map Prod.fst := rfl

variable [DecidableEq Principal]

theorem posterior_respond (execution : app.Execution) (who : Principal) (action : app.Action) :
    implementation.posterior ((execution.respond app who action).recall who) =
      (fiberConditional ((implementation.posterior (execution.recall who)).bind fun memory =>
        implementation.respond memory (execution.recall who, execution.observe app who))
          Prod.fst action).map Prod.snd := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => simp only [Execution.respond, ↓reduceIte, posterior_snoc]
  | some transmission =>
      cases transmission <;> simp only [Execution.respond, ↓reduceIte, posterior_snoc]

/-- Disintegrate one real response using only the focal player's recall. The
continuation may inspect the complete external execution and private state. -/
theorem response_disintegrate {Result : Type} (execution : app.Execution) (who : Principal)
    (next : app.Execution → Memory → PMF Result) :
    (implementation.posterior (execution.recall who)).bind (fun memory =>
      (implementation.respond memory (execution.recall who, execution.observe app who)).bind
        fun response => next (execution.respond app who response.1) response.2) =
      (implementation.policy (execution.recall who) (execution.observe app who)).bind
        (fun action =>
          (implementation.posterior ((execution.respond app who action).recall who)).bind
            (next (execution.respond app who action))) := by
  let law := (implementation.posterior (execution.recall who)).bind fun memory =>
    implementation.respond memory (execution.recall who, execution.observe app who)
  rw [← PMF.bind_bind]
  change law.bind (fun response => next (execution.respond app who response.1) response.2) = _
  conv_lhs => arg 1; rw [eq_bind_fst_conditional_snd law]
  simp only [PMF.bind_bind, PMF.bind_map, policy_eq, posterior_respond, law]

/-- One activation with implementation state carried outside the game. -/
def resume (who : Principal) (players : Principal → app.Policy) (actor : Option Principal)
    (execution : app.Execution) (memory : Memory) : PMF (app.Execution × Memory) :=
  match actor with
  | none => PMF.pure (execution, memory)
  | some owner => if owner = who then
      (implementation.respond memory (execution.recall who, execution.observe app who)).map
        fun response => (execution.respond app who response.1, response.2)
    else (app.invoke players owner execution).map fun next => (next, memory)

def round (who : Principal) (players : Principal → app.Policy) (scheduler : app.Scheduler)
    (execution : app.Execution) (memory : Memory) : PMF (app.Execution × Memory) :=
  (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind fun command =>
    (execution.environmentStep app command).bind fun next =>
      implementation.resume who players (command.actor? app) next memory

/-- The single internal iteration retains private memory for composition of
successive service segments. The memory is never placed in the execution. -/
def runJoint (who : Principal) (players : Principal → app.Policy) (scheduler : app.Scheduler) :
    Nat → app.Execution → Memory → PMF (app.Execution × Memory)
  | 0, execution, memory => PMF.pure (execution, memory)
  | count + 1, execution, memory =>
      (implementation.round who players scheduler execution memory).bind fun next =>
        runJoint who players scheduler count next.1 next.2

/-- The external result discards private memory from the same joint iteration. -/
def run (who : Principal) (players : Principal → app.Policy) (scheduler : app.Scheduler)
    (count : Nat) (execution : app.Execution) (memory : Memory) : PMF app.Execution :=
  (implementation.runJoint who players scheduler count execution memory).map Prod.fst

theorem run_zero (who : Principal) (players : Principal → app.Policy)
    (scheduler : app.Scheduler) (execution : app.Execution) (memory : Memory) :
    implementation.run who players scheduler 0 execution memory = PMF.pure execution := by
  simp only [run, runJoint, PMF.pure_map]

theorem run_succ (who : Principal) (players : Principal → app.Policy)
    (scheduler : app.Scheduler) (count : Nat) (execution : app.Execution) (memory : Memory) :
    implementation.run who players scheduler (count + 1) execution memory =
      (implementation.round who players scheduler execution memory).bind
        (fun next => implementation.run who players scheduler count next.1 next.2) := by
  simp only [run, runJoint, PMF.map_bind]

/-- Exact composition retains the joint memory law, rather than choosing an
arbitrary memory witness after observing an external execution. Binding the
right-hand side to any terminal kernel gives the corresponding continuation
law without defining another evaluator. -/
theorem runJoint_add (who : Principal) (players : Principal → app.Policy)
    (scheduler : app.Scheduler) (first second : Nat) (execution : app.Execution)
    (memory : Memory) :
    implementation.runJoint who players scheduler (first + second) execution memory =
      (implementation.runJoint who players scheduler first execution memory).bind
        (fun next => implementation.runJoint who players scheduler second next.1 next.2) := by
  induction first generalizing execution memory with
  | zero => simp only [Nat.zero_add, runJoint, PMF.pure_bind]
  | succ first ih =>
      simp only [Nat.succ_add, runJoint, PMF.bind_bind]
      exact bind_congr_on_support _ fun next _ => ih next.1 next.2

theorem run_add (who : Principal) (players : Principal → app.Policy)
    (scheduler : app.Scheduler) (first second : Nat) (execution : app.Execution)
    (memory : Memory) :
    implementation.run who players scheduler (first + second) execution memory =
      (implementation.runJoint who players scheduler first execution memory).bind
        (fun next => implementation.run who players scheduler second next.1 next.2) := by
  simp only [run, runJoint_add, PMF.map_bind]

/-- Replacing any one player by its behavioral realization preserves the whole
execution law against arbitrary opponents and observation-local scheduling. -/
theorem realize (who : Principal) (players : Principal → app.Policy) (scheduler : app.Scheduler)
    (count : Nat) (execution : app.Execution) :
    (implementation.posterior (execution.recall who)).bind
        (implementation.run who players scheduler count execution) =
      app.runRounds scheduler (Function.update players who implementation.policy)
        count execution := by
  induction count generalizing execution with
  | zero =>
      change (implementation.posterior (execution.recall who)).bind
        (fun memory => implementation.run who players scheduler 0 execution memory) = _
      simp only [run_zero, runRounds, PMF.bind_const]
  | succ count ih =>
      let next := implementation.run who players scheduler count
      have resumed (current : app.Execution) (actor : Option Principal) :
          (implementation.posterior (current.recall who)).bind (fun memory =>
            (implementation.resume who players actor current memory).bind
              fun result => next result.1 result.2) =
          (app.resume (Function.update players who implementation.policy) actor current).bind
            (app.runRounds scheduler (Function.update players who implementation.policy)
              count) := by
        cases actor with
        | none =>
            simpa only [resume, ReactiveApplication.resume, PMF.pure_bind] using ih current
        | some owner =>
            by_cases same : owner = who
            · subst owner
              simp only [resume, ↓reduceIte, PMF.bind_map]
              rw [implementation.response_disintegrate]
              simp only [next, ih, ReactiveApplication.resume, invoke, Function.update_self,
                PMF.bind_map]
            · simp only [resume, same, ↓reduceIte, PMF.bind_map,
                ReactiveApplication.resume, invoke, Function.update_of_ne same]
              rw [PMF.bind_comm]
              apply bind_congr_on_support _
              intro action _
              rw [← app.respond_recall_other current owner who (Ne.symm same) action]
              exact ih _
      change (implementation.posterior (execution.recall who)).bind
        (fun memory => implementation.run who players scheduler (count + 1) execution memory) = _
      simp only [run_succ, round, runRounds, ReactiveApplication.round, dispatch, PMF.bind_bind]
      rw [PMF.bind_comm]
      apply bind_congr_on_support _
      intro command _
      rw [PMF.bind_comm]
      apply bind_congr_on_support _
      intro current reached
      rw [← app.environmentStep_recall execution current command reached]
      exact resumed current (command.actor? app)

theorem realize_initial (who : Principal) (players : Principal → app.Policy)
    (scheduler : app.Scheduler) (count : Nat) (state : app.State) :
    implementation.initial.bind
        (implementation.run who players scheduler count (Execution.initial app state)) =
      app.runRounds scheduler (Function.update players who implementation.policy)
        count (Execution.initial app state) :=
  implementation.realize who players scheduler count (Execution.initial app state)

end Implementation
end Interaction.ReactiveApplication
