/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSupportedRounds

/-! # Supported play from a round boundary stays in the round evaluator

From a history at scheduler control, every state that behavioral play of a
response menu reaches with positive probability is the result of complete
rounds of the decoded profile from that history's execution, or, at a pending
activation, follows an environment step from such a result
(`Interaction.ReactiveApplication.ResponseMenu.runRoundsSupported_of_mem_run`).
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

/-- Complete rounds end by appending one more round. -/
theorem runRounds_succ_eq_bind_round (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution : app.Execution) :
    app.runRounds scheduler players (count + 1) execution =
      (app.runRounds scheduler players count execution).bind (app.round scheduler players) := by
  rw [app.runRounds_add scheduler players count 1]
  congr 1
  funext middle
  change (app.round scheduler players middle).bind (app.runRounds scheduler players 0) = _
  exact PMF.bind_pure _

variable (app) in
/-- A protocol state reached by complete rounds of `players` from `anchor`, or by
an environment step activating a player after such rounds. -/
def RunRoundsSupported (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (anchor : app.Execution) : app.ProtocolState → Prop
  | none => False
  | some control =>
      match control.actor with
      | none => ∃ count, control.execution ∈ (app.runRounds scheduler players count anchor).support
      | some who => ∃ count prior command,
          prior ∈ (app.runRounds scheduler players count anchor).support ∧
          command ∈ (scheduler prior.environmentRecall (prior.observeEnvironment app)).support ∧
          command.actor? app = some who ∧
          control.execution ∈ (prior.environmentStep app command).support

/-- One step of the canonical kernel of a profile keeps round support from an
anchor for that profile. -/
theorem runRoundsSupported_controlStep (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy) (anchor : app.Execution)
    (before after : app.ProtocolState)
    (valid : app.RunRoundsSupported scheduler players anchor before)
    (reached : after ∈ (app.controlStep initial horizon scheduler players before).support) :
    app.RunRoundsSupported scheduler players anchor after := by
  cases before with
  | none => exact valid.elim
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          obtain ⟨action, chosen, stepped⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          simp only [transition, ↓reduceIte, Option.getD_some] at stepped
          cases (PMF.mem_support_pure_iff _ _).mp stepped
          obtain ⟨count, prior, command, priorMem, commandMem, active, observed⟩ := valid
          refine ⟨count + 1, ?_⟩
          rw [runRounds_succ_eq_bind_round, PMF.support_bind]
          apply Set.mem_iUnion₂.mpr
          refine ⟨prior, priorMem, ?_⟩
          rw [round, PMF.support_bind]
          apply Set.mem_iUnion₂.mpr
          refine ⟨command, commandMem, ?_⟩
          rw [dispatch, PMF.support_bind]
          apply Set.mem_iUnion₂.mpr
          refine ⟨execution, observed, ?_⟩
          simp only [resume, active, invoke, PMF.support_map]
          exact ⟨action, chosen, rfl⟩
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
          | succ remaining =>
              obtain ⟨count, supported⟩ := valid
              obtain ⟨command, selected, moved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, stepped, rfl⟩ := PMF.support_map .. ▸ moved
              cases active : command.actor? app with
              | some who =>
                  change ∃ count prior command, _
                  exact ⟨count, execution, command, supported, selected, active, stepped⟩
              | none =>
                  change ∃ count, _
                  refine ⟨count + 1, ?_⟩
                  rw [runRounds_succ_eq_bind_round, PMF.support_bind]
                  apply Set.mem_iUnion₂.mpr
                  refine ⟨execution, supported, ?_⟩
                  rw [round, PMF.support_bind]
                  apply Set.mem_iUnion₂.mpr
                  refine ⟨command, selected, ?_⟩
                  rw [dispatch, PMF.support_bind]
                  apply Set.mem_iUnion₂.mpr
                  exact ⟨next, stepped, by simp [resume, active]⟩

/-- Every state the canonical kernel of a profile reaches from a round boundary
is round-supported from its execution. -/
theorem runRoundsSupported_of_mem_iterate (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy) (remaining : Nat)
    (anchor : app.Execution) (fuel : Nat) (result : app.ProtocolState)
    (reached : result ∈ ((fun law => law.bind (app.controlStep initial horizon scheduler
      players))^[fuel] (PMF.pure (some ⟨remaining, none, anchor⟩))).support) :
    app.RunRoundsSupported scheduler players anchor result := by
  induction fuel generalizing result with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨0, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  | succ fuel ih =>
      rw [Function.iterate_succ_apply'] at reached
      obtain ⟨before, prior, stepped⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact runRoundsSupported_controlStep initial horizon scheduler players anchor before
        result (ih before prior) stepped

namespace ResponseMenu

variable [Fintype Principal] (menu : app.ResponseMenu) (initial : PMF app.State)
  (horizon : Nat) (scheduler : app.Scheduler)

/-- **Supported play from a round boundary is round-supported.** Every history
that behavioral play of a response menu reaches with positive probability from
a history at scheduler control is round-supported, for the decoded profile,
from that history's execution. -/
theorem runRoundsSupported_of_mem_run
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) (start history : (menu.protocol initial horizon scheduler).History)
    {remaining : Nat} {anchor : app.Execution}
    (state : start.state = some ⟨remaining, none, anchor⟩)
    (reached : history ∈ ((menu.information initial horizon scheduler).runBehavioralFrom profile
      fuel start).support) :
    app.RunRoundsSupported scheduler (menu.decodeProfile initial horizon scheduler profile) anchor
      history.state := by
  have stateReached : history.state ∈ ((fun law => law.bind (app.controlStep initial horizon
      scheduler (menu.decodeProfile initial horizon scheduler profile)))^[fuel]
        (PMF.pure start.state)).support := by
    rw [← menu.run_map_state_eq_iterate initial horizon scheduler profile fuel]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨history, reached, rfl⟩
  rw [state] at stateReached
  exact runRoundsSupported_of_mem_iterate initial horizon scheduler _ remaining anchor fuel
    history.state stateReached

end ResponseMenu

end Interaction.ReactiveApplication
