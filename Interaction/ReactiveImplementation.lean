/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds
import Interaction.ReactiveRecall
import GameTheoryExtensions.Protocol.PrivateStrategy

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

def posterior (past : List app.PlayerEntry) : FinDist Memory :=
  PrivateStrategy.posterior implementation (app.privateTranscript past)

def policy : app.Policy := fun past view =>
  PrivateStrategy.behavioral implementation (app.privateTranscript past) (past, view)

theorem posterior_snoc (past : List app.PlayerEntry) (entry : app.PlayerEntry) :
    implementation.posterior (past ++ [entry]) =
      (((implementation.posterior past).bind fun memory =>
        implementation.respond memory (past, entry.beforeView)).condOnFibre
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
      (((implementation.posterior (execution.recall who)).bind fun memory =>
        implementation.respond memory (execution.recall who, execution.observe app who)).condOnFibre
          Prod.fst action).map Prod.snd := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => simp only [Execution.respond, ↓reduceIte, posterior_snoc]
  | some transmission =>
      cases transmission <;> simp only [Execution.respond, ↓reduceIte, posterior_snoc]

/-- Disintegrate one real response using only the focal player's recall. The
continuation may inspect the complete external execution and private state. -/
theorem response_disintegrate {Result : Type} (execution : app.Execution) (who : Principal)
    (next : app.Execution → Memory → FinDist Result) :
    (implementation.posterior (execution.recall who)).bind (fun memory =>
      (implementation.respond memory (execution.recall who, execution.observe app who)).bind
        fun response => next (execution.respond app who response.1) response.2) =
      (implementation.policy (execution.recall who) (execution.observe app who)).bind
        (fun action =>
          (implementation.posterior ((execution.respond app who action).recall who)).bind
            (next (execution.respond app who action))) := by
  let law := (implementation.posterior (execution.recall who)).bind fun memory =>
    implementation.respond memory (execution.recall who, execution.observe app who)
  rw [← FinDist.bind_bind]
  change law.bind (fun response => next (execution.respond app who response.1) response.2) = _
  conv_lhs => arg 1; rw [FinDist.eq_bind_fst_conditional_snd law]
  simp only [FinDist.bind_bind, FinDist.bind_map, policy_eq, posterior_respond, law]

/-- One activation with implementation state carried outside the game. -/
def resume (who : Principal) (players : Principal → app.Policy) (actor : Option Principal)
    (execution : app.Execution) (memory : Memory) : FinDist (app.Execution × Memory) :=
  match actor with
  | none => FinDist.pure (execution, memory)
  | some owner => if owner = who then
      (implementation.respond memory (execution.recall who, execution.observe app who)).map
        fun response => (execution.respond app who response.1, response.2)
    else (app.invoke players owner execution).map fun next => (next, memory)

def round (who : Principal) (players : Principal → app.Policy) (scheduler : app.Scheduler)
    (execution : app.Execution) (memory : Memory) : FinDist (app.Execution × Memory) :=
  (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind fun command =>
    (execution.environmentStep app command).bind fun next =>
      implementation.resume who players (command.actor? app) next memory

/-- The result retains the entire execution, but no implementation state. -/
def run (who : Principal) (players : Principal → app.Policy) (scheduler : app.Scheduler) :
    Nat → app.Execution → Memory → FinDist app.Execution
  | 0, execution, _ => FinDist.pure execution
  | count + 1, execution, memory =>
      (implementation.round who players scheduler execution memory).bind fun next =>
        run who players scheduler count next.1 next.2

/-- Replacing any one player by its behavioral realization preserves the whole
execution law against arbitrary opponents and observation-local scheduling. -/
theorem realize (who : Principal) (players : Principal → app.Policy) (scheduler : app.Scheduler)
    (count : Nat) (execution : app.Execution) :
    (implementation.posterior (execution.recall who)).bind
        (implementation.run who players scheduler count execution) =
      app.runRounds scheduler (Function.update players who implementation.policy)
        count execution := by
  induction count generalizing execution with
  | zero => simp [run, runRounds]
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
            simpa only [resume, ReactiveApplication.resume, FinDist.pure_bind] using ih current
        | some owner =>
            by_cases same : owner = who
            · subst owner
              simp only [resume, ↓reduceIte, FinDist.bind_map]
              rw [implementation.response_disintegrate]
              simp only [next, ih, ReactiveApplication.resume, invoke, Function.update_self,
                FinDist.bind_map]
            · simp only [resume, same, ↓reduceIte, FinDist.bind_map,
                ReactiveApplication.resume, invoke, Function.update_of_ne same]
              rw [FinDist.bind_comm]
              apply FinDist.bind_congr
              intro action _
              rw [← app.respond_recall_other current owner who (Ne.symm same) action]
              exact ih _
      simp only [run, round, runRounds, ReactiveApplication.round, dispatch, FinDist.bind_bind]
      rw [FinDist.bind_comm]
      change _ = (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind _
      apply FinDist.bind_congr
      intro command _
      rw [FinDist.bind_comm]
      apply FinDist.bind_congr
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
