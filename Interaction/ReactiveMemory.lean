/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory

/-! # Private response memory can be relabeled without changing traffic

Relabeling one player's auxiliary memory preserves legal reactive histories,
all application and network states, and every other player's information.
This concerns auxiliary response memory, not private submission material or
commitment meanings. Schedulers and passive observation rules are unrestricted.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def Action.mapMemory (change : app.Memory → app.Memory) (action : app.Action) : app.Action :=
  { action with memory := change action.memory }

def PlayerEntry.mapMemory (change : app.Memory → app.Memory) (entry : app.PlayerEntry) :
    app.PlayerEntry := { entry with action := entry.action.mapMemory app change }

def Execution.mapMemory (owner : Principal) (change : app.Memory → app.Memory)
    (execution : app.Execution) : app.Execution :=
  { execution with recall := fun who => if who = owner then
      (execution.recall who).map (PlayerEntry.mapMemory app change) else execution.recall who }

def mapActionMemory (owner : Principal) (change : app.Memory → app.Memory)
    (who : Principal) (action : app.Action) : app.Action :=
  if who = owner then action.mapMemory app change else action

def mapStateMemory (owner : Principal) (change : app.Memory → app.Memory) :
    app.ProtocolState → app.ProtocolState :=
  Option.map fun control => { control with
    execution := control.execution.mapMemory app owner change }

theorem mapMemory_initial (owner : Principal) (change : app.Memory → app.Memory)
    (state : app.State) : (Execution.initial app state).mapMemory app owner change =
      Execution.initial app state := by
  simp [Execution.mapMemory, Execution.initial]

theorem mapMemory_respond (owner : Principal) (change : app.Memory → app.Memory)
    (execution : app.Execution) (who : Principal) (action : app.Action) :
    (execution.mapMemory app owner change).respond app who
      (app.mapActionMemory owner change who action) =
        (execution.respond app who action).mapMemory app owner change := by
  rcases action with ⟨memory, transmission⟩
  by_cases own : who = owner
  · subst who
    cases transmission with
    | none =>
        simp only [mapActionMemory, ↓reduceIte, Action.mapMemory, Execution.respond,
          Execution.mapMemory, Execution.observe]
        congr 1
        funext observer
        by_cases same : observer = owner <;>
          simp [same, List.map_append, PlayerEntry.mapMemory, Action.mapMemory]
    | some transmission =>
        cases transmission <;>
          simp only [mapActionMemory, ↓reduceIte, Action.mapMemory, Execution.respond,
            Execution.mapMemory, Execution.observe]
        all_goals
          congr 1
          funext observer
          by_cases same : observer = owner <;>
            simp [same, List.map_append, PlayerEntry.mapMemory, Action.mapMemory]
  · cases transmission with
    | none =>
        simp only [mapActionMemory, own, ↓reduceIte, Execution.respond,
          Execution.mapMemory, Execution.observe]
        congr 1
        funext observer
        by_cases same : observer = who <;> by_cases other : observer = owner <;>
          simp_all
    | some transmission =>
        cases transmission <;>
          simp only [mapActionMemory, own, ↓reduceIte, Execution.respond,
            Execution.mapMemory, Execution.observe]
        all_goals
          congr 1
          funext observer
          by_cases same : observer = who <;> by_cases other : observer = owner <;>
            simp_all

theorem mapMemory_environment (owner : Principal) (change : app.Memory → app.Memory)
    (execution : app.Execution) (command : app.Command) :
    (execution.mapMemory app owner change).environmentStep app command =
      (execution.environmentStep app command).map (Execution.mapMemory app owner change) := by
  cases command with
  | activate who =>
      simp only [Execution.environmentStep, FinDist.map_comp]
      rfl
  | wait => simp only [Execution.environmentStep, FinDist.map_pure]; rfl
  | application command =>
      simp only [Execution.environmentStep, FinDist.map_comp]
      rfl
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure]
      cases found : execution.network.lookup id <;>
        simp [Execution.includePending, Execution.mapMemory, MessageNetwork.includePending, found,
          Execution.observeEnvironment]

theorem observe_mapMemory_other (owner observer : Principal) (different : observer ≠ owner)
    (change : app.Memory → app.Memory) (state : app.ProtocolState) :
    app.observe observer (app.mapStateMemory owner change state) = app.observe observer state := by
  cases state with
  | none => rfl
  | some control =>
      simp only [observe, mapStateMemory, Option.map_some, Execution.mapMemory,
        Execution.observe, different, ↓reduceIte]

variable [Inhabited app.Memory]

def mapJointMemory (owner : Principal) (change : app.Memory → app.Memory)
    (joint : Principal → Option app.Action) : Principal → Option app.Action :=
  fun who => (joint who).map (app.mapActionMemory owner change who)

theorem mapMemory_legal (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (owner : Principal) (change : app.Memory → app.Memory) (state : app.ProtocolState)
    (joint : Principal → Option app.Action) (legal : (app.protocol initial horizon scheduler).Legal
      state joint) : (app.protocol initial horizon scheduler).Legal
        (app.mapStateMemory owner change state) (app.mapJointMemory owner change joint) := by
  constructor
  · cases state <;> exact legal.1
  · intro who
    have choice := legal.2 who
    cases state <;> cases selected : joint who <;>
      simp_all [mapJointMemory, protocol, actor, mapStateMemory]

theorem mapMemory_transition (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (owner : Principal) (change : app.Memory → app.Memory)
    (state : app.ProtocolState) (joint : Principal → Option app.Action)
    (legal : (app.protocol initial horizon scheduler).Legal state joint) :
    app.transition initial horizon scheduler (app.mapStateMemory owner change state)
      (app.mapJointMemory owner change joint) =
    (app.transition initial horizon scheduler state joint).map
      (app.mapStateMemory owner change) := by
  cases state with
  | none =>
      simp only [mapStateMemory, Option.map_none, transition, FinDist.map_comp]
      apply FinDist.map_congr_of_eq_on_support
      intro state _
      simp [app.mapMemory_initial]
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          obtain ⟨action, chosen⟩ := LegalOption.exists_eq_some_of_active
            (E := app.protocol initial horizon scheduler) (joint who)
            ((app.protocol initial horizon scheduler).legalOption_of_legal legal who) rfl
          simp only [mapStateMemory, Option.map_some, transition, mapJointMemory, chosen,
            Option.getD_some, app.mapMemory_respond, FinDist.map_pure]
      | none =>
          cases remaining with
          | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
          | succ remaining =>
              simp only [mapStateMemory, Option.map_some, transition, Execution.mapMemory,
                Execution.observeEnvironment, FinDist.map_bind]
              apply FinDist.bind_congr
              intro command _
              have moved := congrArg (fun law : FinDist app.Execution =>
                law.map fun next => some (Control.mk remaining (command.actor? app) next))
                  (app.mapMemory_environment owner change execution command)
              simpa only [FinDist.map_comp, Function.comp_def, mapStateMemory,
                Option.map_some, Execution.mapMemory] using moved

def mapMemoryTrace (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (owner : Principal) (change : app.Memory → app.Memory) :
    ∀ {state}, (app.protocol initial horizon scheduler).Trace state →
      (app.protocol initial horizon scheduler).Trace (app.mapStateMemory owner change state)
  | _, .start => .start
  | _, .extend prior joint legal reached =>
      (mapMemoryTrace initial horizon scheduler owner change prior).extend
        (app.mapJointMemory owner change joint)
        (app.mapMemory_legal initial horizon scheduler owner change _ joint legal) (by
          change app.mapStateMemory owner change _ ∈
            (app.transition initial horizon scheduler _ _).support
          rw [app.mapMemory_transition initial horizon scheduler owner change _ joint legal,
            FinDist.support_map]
          exact ⟨_, reached, rfl⟩)

theorem mapMemoryTrace_length (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (owner : Principal) (change : app.Memory → app.Memory) :
    ∀ {state} (trace : (app.protocol initial horizon scheduler).Trace state),
      (app.mapMemoryTrace initial horizon scheduler owner change trace).length = trace.length
  | _, .start => rfl
  | _, .extend prior _ _ _ => congrArg (· + 1)
      (mapMemoryTrace_length initial horizon scheduler owner change prior)

end Interaction.ReactiveApplication
