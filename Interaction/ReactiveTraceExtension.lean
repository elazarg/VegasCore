/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundTrace
import Interaction.ReactiveSchedulerRefinement

/-! # Extending genuine menu histories by actual dispatches -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) (initial : PMF app.State)

private def addTurns (extra : Nat) : app.ProtocolState → app.ProtocolState :=
  Option.map fun control => { control with remaining := control.remaining + extra }

private theorem legal_addTurns (horizon extra : Nat) (scheduler : app.Scheduler)
    (state : app.ProtocolState) (joint : Principal → Option app.Action)
    (legal : (menu.protocol initial horizon scheduler).Legal state joint) :
    (menu.protocol initial (horizon + extra) scheduler).Legal (addTurns extra state) joint := by
  cases state with
  | none => exact legal
  | some control =>
      refine ⟨?_, legal.2⟩
      intro terminal
      apply legal.1
      change control.remaining + extra = 0 ∧ control.actor = none at terminal
      change control.remaining = 0 ∧ control.actor = none
      exact ⟨by omega, terminal.2⟩

private theorem transition_addTurns (horizon extra : Nat) (scheduler : app.Scheduler)
    (state : app.ProtocolState) (joint : Principal → Option app.Action)
    (running : ¬ app.terminal state) :
    app.transition initial (horizon + extra) scheduler (addTurns extra state) joint =
      (app.transition initial horizon scheduler state joint).map (addTurns extra) := by
  cases state with
  | none => simp only [addTurns, Option.map_none, transition, PMF.map_comp]; rfl
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who => simp only [addTurns, Option.map_some, transition, PMF.pure_map]
      | none =>
          cases remaining with
          | zero => exact (running ⟨rfl, rfl⟩).elim
          | succ remaining =>
              simp only [addTurns, Option.map_some, transition, Nat.succ_add,
                PMF.map_bind, PMF.map_comp]
              rfl

private theorem trace_addTurns (horizon extra : Nat) (scheduler : app.Scheduler) :
    ∀ {state}, (menu.protocol initial horizon scheduler).Trace state →
      Nonempty ((menu.protocol initial (horizon + extra) scheduler).Trace (addTurns extra state))
  | _, .start => ⟨.start⟩
  | _, .extend prior joint legal reached => by
      obtain ⟨earlier⟩ := trace_addTurns horizon extra scheduler prior
      refine ⟨.extend earlier joint (legal_addTurns menu initial horizon extra scheduler _ _ legal)
        ?_⟩
      change _ ∈ (app.transition initial (horizon + extra) scheduler _ joint).support
      rw [transition_addTurns initial horizon extra scheduler _ joint legal.1]
      rw [PMF.support_map]
      exact ⟨_, reached, rfl⟩

/-- Additional environment fuel leaves every realized execution and response unchanged. -/
theorem trace_more_environment_turns (horizon extra : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some control)) :
    Nonempty ((menu.protocol initial (horizon + extra) scheduler).Trace
      (some { control with remaining := control.remaining + extra })) :=
  trace_addTurns menu initial horizon extra scheduler trace

/-- Enlarging scheduler support retains all genuine menu histories. -/
def trace_of_scheduler_support_subset (horizon : Nat) (smaller larger : app.Scheduler)
    (included : ∀ past view, (smaller past view).support ⊆ (larger past view).support) :
    ∀ {state}, (menu.protocol initial horizon smaller).Trace state →
      (menu.protocol initial horizon larger).Trace state
  | _, .start => .start
  | _, .extend prior joint legal reached =>
      .extend (trace_of_scheduler_support_subset horizon smaller larger included prior) joint legal
        (app.transition_support_subset_of_scheduler_support_subset initial horizon smaller larger
          included _ _ reached)

private def schedulerWithCommand (scheduler : app.Scheduler) (command : app.Command) :
    app.Scheduler := fun past view => (PMF.uniformOfFintype Bool).bind fun select =>
      if select then scheduler past view else PMF.pure command

omit [DecidableEq Principal] in
private theorem schedulerWithCommand_includes (scheduler : app.Scheduler) (command : app.Command)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    (scheduler past view).support ⊆ (schedulerWithCommand scheduler command past view).support := by
  intro selected supported
  rw [schedulerWithCommand, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨true, by simp, supported⟩

/-- A genuine actor-free menu history can be extended by any supported dispatch
whose player responses stay in the menu. No scheduler support premise is needed. -/
theorem trace_dispatch (horizon : Nat) (scheduler : app.Scheduler) (remaining : Nat)
    (execution next : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (players : Principal → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view)
    (command : app.Command) (reached : next ∈ (app.dispatch players command execution).support) :
    ∃ extendedScheduler, Nonempty ((menu.protocol initial (horizon + 1) extendedScheduler).Trace
      (some ⟨remaining, none, next⟩)) := by
  obtain ⟨longer⟩ := menu.trace_more_environment_turns initial horizon 1 scheduler _ trace
  let extended := schedulerWithCommand scheduler command
  have expanded := menu.trace_of_scheduler_support_subset initial (horizon + 1) scheduler extended
    (schedulerWithCommand_includes scheduler command) longer
  refine ⟨extended, menu.trace_round initial (horizon + 1) extended players covered remaining
    execution next expanded ?_⟩
  rw [round, PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨command, ?_, reached⟩
  change command ∈ (schedulerWithCommand scheduler command _ _).support
  rw [schedulerWithCommand, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨false, by simp, by simp⟩

end Interaction.ReactiveApplication.ResponseMenu
