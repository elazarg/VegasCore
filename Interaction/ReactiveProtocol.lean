/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveApplication
import GameTheory.Protocol.Information
import GameTheory.Protocol.Backward

/-! # A scheduler that activates players explicitly

Each scheduler decision chooses one activation, inclusion, application operation,
or wait. Activation privately samples pending-message observations and transfers
control to one player; its single response transfers control back. The horizon
bounds scheduler decisions. Application completion requires a service certificate.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def Command.actor? : app.Command → Option Principal
  | .activate who => some who
  | _ => none

structure Control where
  remaining : Nat
  actor : Option Principal
  execution : app.Execution

abbrev ProtocolState := Option app.Control

def actor (state : app.ProtocolState) : Option Principal := state.bind Control.actor

def terminal : app.ProtocolState → Prop
  | none => False
  | some control => control.remaining = 0 ∧ control.actor = none

def rank (horizon : Nat) : app.ProtocolState → Nat
  | none => 2 * horizon + 1
  | some control => 2 * control.remaining + if control.actor.isSome then 1 else 0

def transition (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    app.ProtocolState → (Principal → Option app.Action) → PMF app.ProtocolState
  | none, _ => initial.map fun state => some ⟨horizon, none, Execution.initial app state⟩
  | some control, joint => match control.actor with
    | some who => PMF.pure (some { control with
        actor := none
        execution := control.execution.respond app who ((joint who).getD ⟨none⟩) })
    | none => match control.remaining with
      | 0 => PMF.pure (some control)
      | remaining + 1 =>
          (scheduler control.execution.environmentRecall
            (control.execution.observeEnvironment app)).bind fun command =>
            (control.execution.environmentStep app command).map fun execution =>
              some ⟨remaining, command.actor? app, execution⟩

/-- The application's own nature branches finitely: every pending-message
observation and every environment step has finite support. -/
class FiniteEnvironment : Prop where
  observePending_finite : ∀ who pending, (app.observePending who pending).support.Finite
  environment_finite : ∀ state command, (app.environment state command).support.Finite

/-- All nature branches finitely: the application's own laws, the initial law
and every scheduler decision have finite support. -/
class FiniteNature (initial : PMF app.State) (scheduler : app.Scheduler) : Prop
    extends app.FiniteEnvironment where
  initial_finite : initial.support.Finite
  scheduler_finite : ∀ recall view, (scheduler recall view).support.Finite

theorem environmentStep_support_finite [app.FiniteEnvironment]
    (execution : app.Execution) (command : app.Command) :
    (execution.environmentStep app command).support.Finite := by
  unfold Execution.environmentStep
  rw [PMF.support_map]
  refine Set.Finite.image _ ?_
  cases command with
  | activate who =>
      rw [PMF.support_map]
      exact (FiniteEnvironment.observePending_finite who _).image _
  | «include» id => simp
  | application command =>
      rw [PMF.support_map]
      exact (FiniteEnvironment.environment_finite _ command).image _
  | wait => simp

theorem transition_support_finite (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) [app.FiniteNature initial scheduler]
    (state : app.ProtocolState) (joint : Principal → Option app.Action) :
    (app.transition initial horizon scheduler state joint).support.Finite := by
  rcases state with _ | ⟨remaining, actor, execution⟩
  · rw [transition, PMF.support_map]
    exact (FiniteNature.initial_finite (app := app) scheduler).image _
  rcases actor with _ | who
  · rcases remaining with _ | remaining
    · simp [transition]
    · simp only [transition, PMF.support_bind, PMF.support_map]
      exact (FiniteNature.scheduler_finite initial _ _).biUnion fun command _ =>
        (app.environmentStep_support_finite _ command).image _
  · simp [transition]

def protocol (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    ExecutionProtocol Principal where
  State := app.ProtocolState
  Action _ := app.Action
  init := none
  active state who := app.actor state = some who
  available _ _ := Set.univ
  terminal := app.terminal
  step state joint := app.transition initial horizon scheduler state joint.1
  progress state _ := by
    refine ⟨fun who => if app.actor state = some who then some ⟨none⟩ else none, ?_⟩
    intro who
    by_cases active : app.actor state = some who <;> simp [active]

abbrev Info := Option (List app.PlayerEntry × app.PlayerView)

def observe (who : Principal) (state : app.ProtocolState) : app.Info :=
  match state with
  | none => none
  | some control => if control.actor = some who then
      some (control.execution.recall who, control.execution.observe app who) else none

theorem observe_isSome (who : Principal) (state : app.ProtocolState) :
    (app.observe who state).isSome ↔ app.actor state = some who := by
  cases state with
  | none => simp [observe, actor]
  | some control =>
      by_cases active : control.actor = some who <;> simp [observe, actor, active]

def signals (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    InfoSignals (app.protocol initial horizon scheduler) where
  PublicSignal := Unit
  PrivateSignal _ := app.Info
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal who event := app.observe who event.target
  InfoState _ := app.Info
  initInfo _ view _ := view
  pushInfo _ _ _ view _ := view

theorem info (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) : ∀ {state} (trace : (app.protocol initial horizon scheduler).Trace state),
    (app.signals initial horizon scheduler).infoOf who trace = app.observe who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- Every active player has the same one-response menu. No service position
or response capacity is added to its observation. -/
def information (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    InformationModel (app.protocol initial horizon scheduler) where
  toInfoSignals := app.signals initial horizon scheduler
  menu _ info := {choice | choice.isSome = info.isSome}
  menu_adequate := by
    intro who state trace choice
    rw [app.info initial horizon scheduler who trace]
    have active := app.observe_isSome who state
    cases observed : app.observe who state <;> cases choice <;>
      simp_all [LegalOption, protocol]

omit [DecidableEq Principal] in
theorem rank_zero (horizon : Nat) (state : app.ProtocolState) :
    app.rank horizon state = 0 ↔ app.terminal state := by
  cases state with
  | none => simp [rank, terminal]
  | some control => cases control.actor <;> simp [rank, terminal]

theorem rank_step (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (running : ¬ app.terminal before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.rank horizon after < app.rank horizon before := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      simp [rank]
  | some control =>
      rcases control with ⟨remaining, current, execution⟩
      cases current with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          simp [rank]
      | none =>
          cases remaining with
          | zero => exact (running ⟨rfl, rfl⟩).elim
          | succ remaining =>
              obtain ⟨command, _, supported⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, _, rfl⟩ := PMF.support_map .. ▸ supported
              cases command <;> simp [rank, Command.actor?]
              omega

theorem terminates (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    (app.protocol initial horizon scheduler).WellFoundedPlay := by
  apply wellFoundedPlay_of_rank (app.rank horizon)
  intro before after transition
  obtain ⟨joint, legal, reached⟩ := transition
  exact app.rank_step initial horizon scheduler before after joint legal.1 reached

theorem trace_bound (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    ∀ {state} (trace : (app.protocol initial horizon scheduler).Trace state),
      trace.length + app.rank horizon state ≤ 2 * horizon + 1
  | _, .start => by simp [Trace.length, protocol, rank]
  | _, .extend prior joint legal reached => by
      have earlier := trace_bound initial horizon scheduler prior
      have decreases := app.rank_step initial horizon scheduler _ _ joint legal.1 reached
      simp only [Trace.length]
      omega

theorem bounded (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    (app.protocol initial horizon scheduler).BoundedHorizon (2 * horizon + 1) := by
  intro state trace enough
  have bound := app.trace_bound initial horizon scheduler trace
  exact (app.rank_zero horizon state).mp (by omega)

end Interaction.ReactiveApplication
