/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveEvaluation
import Interaction.ReactiveHistory
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Support

/-! # Evaluation by scheduler rounds

A round executes one scheduler command and, for activation, the selected
player response. This is an evaluator for the canonical protocol: the exact
law below retains its complete execution state and private recall. It does
not change the protocol's histories, strategic decisions, or subgames.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def invoke (players : Principal → app.Policy) (who : Principal)
    (execution : app.Execution) : PMF app.Execution :=
  (players who (execution.recall who) (execution.observe app who)).map
    (execution.respond app who)

def resume (players : Principal → app.Policy) (actor : Option Principal)
    (execution : app.Execution) : PMF app.Execution :=
  match actor with
  | none => PMF.pure execution
  | some who => app.invoke players who execution

def dispatch (players : Principal → app.Policy) (command : app.Command)
    (execution : app.Execution) : PMF app.Execution :=
  (execution.environmentStep app command).bind (app.resume players (command.actor? app))

def round (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (execution : app.Execution) : PMF app.Execution :=
  (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
    (fun command => app.dispatch players command execution)

def runRounds (scheduler : app.Scheduler) (players : Principal → app.Policy) :
    Nat → app.Execution → PMF app.Execution
  | 0, execution => PMF.pure execution
  | count + 1, execution => (app.round scheduler players execution).bind
      (runRounds scheduler players count)

/-- One dispatched command records exactly one response by its selected actor.
Passive observations and application commands add no private response entry. -/
theorem dispatch_recall_length (players : Principal → app.Policy) (command : app.Command)
    (before after : app.Execution)
    (reached : after ∈ (app.dispatch players command before).support) (who : Principal) :
    (after.recall who).length = (before.recall who).length +
      if command.actor? app = some who then 1 else 0 := by
  obtain ⟨activated, observed, responded⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have prior := app.environmentStep_recall before activated command observed
  cases actor : command.actor? app with
  | none =>
      change after ∈ (app.resume players (command.actor? app) activated).support at responded
      rw [actor] at responded
      cases (PMF.mem_support_pure_iff _ _).mp responded
      simp only [prior, reduceCtorEq, ↓reduceIte, Nat.add_zero]
  | some owner =>
      change after ∈ (app.resume players (command.actor? app) activated).support at responded
      rw [actor] at responded
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ responded
      rw [app.respond_recall_length, prior]
      simp only [Option.some.injEq]

theorem resume_environmentRecall (players : Principal → app.Policy) (actor : Option Principal)
    (execution next : app.Execution)
    (reached : next ∈ (app.resume players actor execution).support) :
    next.environmentRecall = execution.environmentRecall := by
  cases actor with
  | none => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | some who =>
      obtain ⟨action, _, rfl⟩ := PMF.support_map .. ▸ reached
      rcases action with ⟨transmission⟩
      cases transmission with
      | none => rfl
      | some transmission => rfl

/-- A round records exactly one scheduler command, independently of which
player it activates or whether the response emits a packet. -/
theorem dispatch_environmentRecall (players : Principal → app.Policy) (command : app.Command)
    (execution next : app.Execution)
    (reached : next ∈ (app.dispatch players command execution).support) :
    next.environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] := by
  obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [app.resume_environmentRecall players _ middle next moved]
  obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ supported
  rfl

theorem runRounds_add (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (first second : Nat) (execution : app.Execution) :
    app.runRounds scheduler players (first + second) execution =
      (app.runRounds scheduler players first execution).bind
        (app.runRounds scheduler players second) := by
  induction first generalizing execution with
  | zero => simp only [Nat.zero_add, runRounds, PMF.pure_bind]
  | succ first ih =>
      simp only [Nat.succ_add, runRounds, PMF.bind_bind]
      exact bind_congr_on_support _ fun next _ => ih next

def finished (execution : app.Execution) : app.ProtocolState := some ⟨0, none, execution⟩

def finish (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) : app.ProtocolState → PMF app.ProtocolState
  | none => initial.bind fun state =>
      (app.runRounds scheduler players horizon (Execution.initial app state)).map app.finished
  | some control => ((app.resume players control.actor control.execution).bind
      (app.runRounds scheduler players control.remaining)).map app.finished

theorem finish_terminal (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (state : app.ProtocolState) (stopped : app.terminal state) :
    app.finish initial horizon scheduler players state = PMF.pure state := by
  cases state with
  | none => exact stopped.elim
  | some control =>
      rcases control with ⟨remaining, current, execution⟩
      rcases stopped with ⟨rfl, rfl⟩
      simp only [finish, resume, PMF.pure_bind, runRounds, PMF.pure_map, finished]

theorem finish_step (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (state : app.ProtocolState) :
    (app.controlStep initial horizon scheduler players state).bind
      (app.finish initial horizon scheduler players) =
        app.finish initial horizon scheduler players state := by
  cases state with
  | none =>
      simp only [controlStep, actor, Option.bind_none, transition, PMF.bind_map, Function.comp_def,
        finish, resume, PMF.pure_bind]
  | some control =>
      rcases control with ⟨remaining, current, execution⟩
      cases current with
      | some who =>
          simp only [controlStep, actor, Option.bind_some, transition, ↓reduceIte,
            Option.getD_some, PMF.bind_bind, PMF.pure_bind, finish, resume,
            invoke, PMF.bind_map, PMF.map_bind, Function.comp_def]
      | none =>
          cases remaining with
          | zero => simp only [controlStep, actor, Option.bind_some, transition, PMF.pure_bind]
          | succ remaining =>
              simp only [controlStep, actor, Option.bind_some, transition, PMF.bind_bind,
                PMF.bind_map, finish, resume, PMF.pure_bind, runRounds, round,
                dispatch, PMF.map_bind, Function.comp_def]

theorem controlStep_rank (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (before after : app.ProtocolState) (running : ¬ app.terminal before)
    (reached : after ∈ (app.controlStep initial horizon scheduler players before).support) :
    app.rank horizon after < app.rank horizon before := by
  unfold controlStep at reached
  split at reached
  · exact app.rank_step initial horizon scheduler before after _ running reached
  · cases before with
    | none => simp [actor] at *
    | some control =>
        obtain ⟨action, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        exact app.rank_step initial horizon scheduler _ after _ running supported

/-- Completing after any finite prefix gives the same final law as completing
immediately, including the network, recall, and receipts. -/
theorem finish_after_steps (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (fuel : Nat) (law : PMF app.ProtocolState) :
    ((fun distribution => distribution.bind (app.controlStep initial horizon scheduler players))
      ^[fuel] law).bind (app.finish initial horizon scheduler players) =
      law.bind (app.finish initial horizon scheduler players) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply', PMF.bind_bind]
      calc
        _ = ((fun distribution => distribution.bind
              (app.controlStep initial horizon scheduler players))^[fuel] law).bind
                (app.finish initial horizon scheduler players) := by
          apply bind_congr_on_support _
          intro state _
          exact app.finish_step initial horizon scheduler players state
        _ = _ := ih

/-- At sufficient fuel, iteration of the actual protocol kernel equals the
round evaluator. Equality includes the final network, all recall, and receipts. -/
theorem iterate_eq_finish (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (fuel : Nat) (state : app.ProtocolState) (enough : app.rank horizon state ≤ fuel) :
    (fun law => law.bind (app.controlStep initial horizon scheduler players))^[fuel]
      (PMF.pure state) = app.finish initial horizon scheduler players state := by
  induction fuel generalizing state with
  | zero =>
      have stopped := (app.rank_zero horizon state).mp (by omega)
      exact (app.finish_terminal initial horizon scheduler players state stopped).symm
  | succ fuel ih =>
      by_cases stopped : app.terminal state
      · have stationary : app.controlStep initial horizon scheduler players state =
            PMF.pure state := by
          cases state with
          | none => exact stopped.elim
          | some control =>
              rcases control with ⟨remaining, current, execution⟩
              rcases stopped with ⟨rfl, rfl⟩
              rfl
        rw [Function.iterate_succ_apply, PMF.pure_bind, stationary]
        exact ih state (by rw [(app.rank_zero horizon state).mpr stopped]; omega)
      · rw [Function.iterate_succ_apply, PMF.pure_bind]
        have expand := iterate_bind (app.controlStep initial horizon scheduler players) fuel
          (app.controlStep initial horizon scheduler players state) PMF.pure
        rw [PMF.bind_pure] at expand
        rw [expand]
        calc
          _ = (app.controlStep initial horizon scheduler players state).bind
                (app.finish initial horizon scheduler players) := by
              apply bind_congr_on_support _
              intro next supported
              have decreases := app.controlStep_rank initial horizon scheduler players
                state next stopped supported
              exact ih next (by omega)
          _ = _ := app.finish_step initial horizon scheduler players state

/-- The scheduler-round evaluator is the final-state law of the canonical
behavioral game, for every player profile and observation-local scheduler. -/
theorem canonical_run_rounds (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy) :
    ((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun who => app.encodePolicy (players who))
      (2 * horizon + 1) (app.protocol initial horizon scheduler).initHistory).map
        ExecutionProtocol.History.state =
      initial.bind (fun state =>
        (app.runRounds scheduler players horizon (Execution.initial app state)).map
          app.finished) := by
  rw [app.run_map_state]
  change
    (fun law => law.bind (app.controlStep initial horizon scheduler players))^[2 * horizon + 1]
      (PMF.pure none) = _
  rw [app.iterate_eq_finish initial horizon scheduler players _ _ (by rfl)]
  rfl

end Interaction.ReactiveApplication
