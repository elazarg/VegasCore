/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSupportedRounds

/-! # Round support from an anchor execution

A protocol state is round-supported from an anchor execution when it is the
result of complete rounds of a profile from that execution, or, at a pending
activation, follows an environment step from such a result
(`Interaction.ReactiveApplication.RunRoundsSupported`). One step of the
canonical kernel of the profile keeps round support
(`Interaction.ReactiveApplication.runRoundsSupported_controlStep`).
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

end Interaction.ReactiveApplication
