/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu
import Interaction.ReactiveRounds

/-! # Legal histories occur in the round evaluator

A response family with support on every menu action witnesses every legal
history. At a pending activation the witness stops after the environment step;
at scheduler control it stops after a complete round. Thus round-based service
proofs also apply at off-path decision histories, without assuming those
histories have positive probability in an equilibrium assessment.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)

def uniformResponses (who : Principal) : app.Policy := fun past view => by
  let choices := menu.actions who past view
  letI : Nonempty choices := ⟨⟨(menu.nonempty who past view).choose,
    (menu.nonempty who past view).choose_spec⟩⟩
  exact (FinDist.uniformOfFintype : FinDist choices).map Subtype.val

omit [DecidableEq Principal] in
theorem uniformResponses_support (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView) (action : app.Action) :
    action ∈ (menu.uniformResponses who past view).support ↔
      action ∈ menu.actions who past view := by
  let : Nonempty (menu.actions who past view) :=
    ⟨⟨(menu.nonempty who past view).choose, (menu.nonempty who past view).choose_spec⟩⟩
  simp only [uniformResponses, FinDist.support_map]
  constructor
  · rintro ⟨choice, _, rfl⟩
    exact choice.2
  · intro member
    exact ⟨⟨action, member⟩, FinDist.mem_support_uniformOfFintype _, rfl⟩

end ResponseMenu

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

open GameTheory.Protocol GameTheory.Math.Probability

/-- Initialization followed by a specified number of complete scheduler rounds. -/
def roundsFrom (initial : FinDist app.State) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) : FinDist app.Execution :=
  initial.bind fun state => app.runRounds scheduler players count (Execution.initial app state)

theorem roundsFrom_succ (initial : FinDist app.State) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) :
    app.roundsFrom initial scheduler players (count + 1) =
      (app.roundsFrom initial scheduler players count).bind (app.round scheduler players) := by
  unfold roundsFrom
  simp only [app.runRounds_add scheduler players count 1, FinDist.bind_bind]
  congr 1
  funext state
  apply FinDist.bind_congr
  intro execution _
  simp only [runRounds, FinDist.bind_pure]

/-- The scheduler cursor and a support witness for either a completed round
or its pending player response. -/
def RoundSupported (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) : app.ProtocolState → Prop
  | none => True
  | some control =>
      control.execution.environmentRecall.length + control.remaining = horizon ∧
      match control.actor with
      | none => control.execution ∈ (app.roundsFrom initial scheduler players
          control.execution.environmentRecall.length).support
      | some who => ∃ count prior command,
          control.execution.environmentRecall.length = count + 1 ∧
          prior ∈ (app.roundsFrom initial scheduler players count).support ∧
          command ∈ (scheduler prior.environmentRecall (prior.observeEnvironment app)).support ∧
          command.actor? app = some who ∧
          control.execution ∈ (prior.environmentStep app command).support

theorem roundsFrom_recall (initial : FinDist app.State) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution : app.Execution)
    (reached : execution ∈ (app.roundsFrom initial scheduler players count).support) :
    execution.environmentRecall.length = count := by
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      cases FinDist.mem_support_pure.mp supported
      rfl
  | succ count ih =>
      rw [roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ moved)
      rw [app.dispatch_environmentRecall players command prior execution dispatched]
      simp only [List.length_append, List.length_singleton, ih prior priorMem]

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu) (initial : FinDist app.State) (horizon : Nat)
  (scheduler : app.Scheduler) (players : Principal → app.Policy)
  (full : ∀ who past view action, action ∈ menu.actions who past view →
    action ∈ (players who past view).support)

include full in
theorem roundSupported_transition (before after : app.ProtocolState)
    (joint : Principal → Option app.Action)
    (valid : app.RoundSupported initial horizon scheduler players before)
    (legal : (menu.protocol initial horizon scheduler).Legal before joint)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.RoundSupported initial horizon scheduler players after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      refine ⟨by simp [Execution.initial], ?_⟩
      change Execution.initial app state ∈ (app.roundsFrom initial scheduler players 0).support
      rw [roundsFrom, FinDist.support_bind]
      apply Set.mem_iUnion₂.mpr
      exact ⟨state, supported, FinDist.mem_support_pure.mpr rfl⟩
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          have localLegal := legal.2 who
          cases selected : joint who with
          | none => simp [selected, protocol, ReactiveApplication.actor] at localLegal
          | some action =>
              rw [selected] at localLegal
              cases FinDist.mem_support_pure.mp reached
              obtain ⟨accounted, count, prior, command, position, priorMem,
                commandMem, active, observed⟩ := valid
              simp only [RoundSupported, selected, Option.getD_some]
              change (execution.respond app who action).environmentRecall.length + remaining =
                horizon ∧ (execution.respond app who action) ∈
                  (app.roundsFrom initial scheduler players
                    (execution.respond app who action).environmentRecall.length).support
              rw [app.respond_environmentRecall]
              refine ⟨accounted, ?_⟩
              rw [position, app.roundsFrom_succ, FinDist.support_bind]
              apply Set.mem_iUnion₂.mpr
              refine ⟨prior, priorMem, ?_⟩
              rw [round, FinDist.support_bind]
              apply Set.mem_iUnion₂.mpr
              refine ⟨command, commandMem, ?_⟩
              rw [dispatch, FinDist.support_bind]
              apply Set.mem_iUnion₂.mpr
              refine ⟨execution, observed, ?_⟩
              simp only [resume, active, invoke, FinDist.support_map]
              exact ⟨action, full who _ _ action localLegal.2, rfl⟩
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, selected, moved⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
              have advanced : next.environmentRecall.length =
                  execution.environmentRecall.length + 1 := by
                obtain ⟨updated, _, same⟩ := FinDist.support_map .. ▸ supported
                cases same
                simp
              refine ⟨by have accounted := valid.1; dsimp at *; omega, ?_⟩
              cases active : command.actor? app with
              | some who =>
                  exact ⟨_, execution, command, advanced, valid.2, selected, active, supported⟩
              | none =>
                  change next ∈ (app.roundsFrom initial scheduler players
                    next.environmentRecall.length).support
                  rw [advanced, app.roundsFrom_succ, FinDist.support_bind]
                  apply Set.mem_iUnion₂.mpr
                  refine ⟨execution, valid.2, ?_⟩
                  rw [round, FinDist.support_bind]
                  apply Set.mem_iUnion₂.mpr
                  refine ⟨command, selected, ?_⟩
                  rw [dispatch, FinDist.support_bind]
                  apply Set.mem_iUnion₂.mpr
                  exact ⟨next, supported, by simp [resume, active]⟩

include full in
theorem roundSupported_history :
    ∀ {state} (_trace : (menu.protocol initial horizon scheduler).Trace state),
      app.RoundSupported initial horizon scheduler players state
  | _, .start => trivial
  | _, .extend prior joint legal reached =>
      menu.roundSupported_transition initial horizon scheduler players full _ _ joint
        (roundSupported_history prior) legal reached

theorem roundSupported_uniform {state}
    (trace : (menu.protocol initial horizon scheduler).Trace state) :
    app.RoundSupported initial horizon scheduler menu.uniformResponses state :=
  menu.roundSupported_history initial horizon scheduler menu.uniformResponses
    (fun who past view action => (menu.uniformResponses_support who past view action).mpr) trace

end ResponseMenu
end Interaction.ReactiveApplication
