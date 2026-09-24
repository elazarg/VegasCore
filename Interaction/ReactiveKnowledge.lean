/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveObservation

/-! # Own packets never enter passive knowledge at legal histories -/

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def Execution.ForeignLeaks (execution : app.Execution) : Prop :=
  ∀ who message, message ∈ execution.network.leaked who → message.sender ≠ who

theorem respond_foreignLeaks (execution : app.Execution) (who : Principal) (action : app.Action)
    (valid : execution.ForeignLeaks app) : (execution.respond app who action).ForeignLeaks app := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact valid
  | some transmission =>
      cases transmission with
      | submit material => exact valid
      | replay id =>
          change ({ execution with
            network := (execution.network.replay who id).2
            recall := _ } : app.Execution).ForeignLeaks app
          unfold MessageNetwork.replay
          split <;> exact valid

theorem environment_foreignLeaks (execution next : app.Execution) (command : app.Command)
    (valid : execution.ForeignLeaks app)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.ForeignLeaks app := by
  cases command with
  | wait =>
      cases FinDist.mem_support_pure.mp (by
        simpa only [Execution.environmentStep, FinDist.map_pure] using reached)
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      intro observer message member
      by_cases same : observer = who
      · subst observer
        rcases execution.network.learn_mem who selected message member with prior | fresh
        · exact valid who message prior
        · exact fresh.2
      · rw [MessageNetwork.learn_other _ who observer selected same] at member
        exact valid observer message member
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      cases found : execution.network.lookup id <;>
        simpa only [Execution.ForeignLeaks, Execution.includePending,
          MessageNetwork.includePending, found] using valid
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid

def foreignLeaks : app.ProtocolState → Prop
  | none => True
  | some control => control.execution.ForeignLeaks app

theorem transition_foreignLeaks (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before after : app.ProtocolState)
    (joint : Principal → Option app.Action) (valid : app.foreignLeaks before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.foreignLeaks after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ reached
      intro who message member
      exact (List.not_mem_nil member).elim
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases FinDist.mem_support_pure.mp reached
          exact app.respond_foreignLeaks execution who _ valid
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
              exact app.environment_foreignLeaks execution next command valid supported

/-- All legal initialized histories, with arbitrary strategies, schedulers,
and observation laws, exclude self-authored messages from passive knowledge. -/
theorem history_foreignLeaks (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      app.foreignLeaks state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      app.transition_foreignLeaks initial horizon scheduler _ _ joint
        (history_foreignLeaks initial horizon scheduler prior) reached

end Interaction.ReactiveApplication
