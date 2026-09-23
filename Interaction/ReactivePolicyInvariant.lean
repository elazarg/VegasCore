/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds

/-! # Execution invariants under reactive player policies

The predicate may inspect the complete execution, including each player's
recall. Player obligations concern supported responses at their actual local
view. Environment obligations cover every command, so the result holds under
any observation-local scheduler, at every prefix of canonical behavioral play.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

structure PolicyInvariant (players : Principal → app.Policy)
    (predicate : app.Execution → Prop) : Prop where
  respond : ∀ execution who action, predicate execution →
    action ∈ (players who (execution.recall who) (execution.observe app who)).support →
      predicate (execution.respond app who action)
  environment : ∀ execution next command, predicate execution →
    next ∈ (execution.environmentStep app command).support → predicate next

variable {app} {players : Principal → app.Policy} {predicate : app.Execution → Prop}

theorem PolicyInvariant.resume (invariant : app.PolicyInvariant players predicate)
    (actor : Option Principal) (execution next : app.Execution) (valid : predicate execution)
    (reached : next ∈ (app.resume players actor execution).support) : predicate next := by
  cases actor with
  | none => cases FinDist.mem_support_pure.mp reached; exact valid
  | some who =>
      obtain ⟨action, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      exact invariant.respond execution who action valid supported

theorem PolicyInvariant.dispatch (invariant : app.PolicyInvariant players predicate)
    (command : app.Command) (execution next : app.Execution) (valid : predicate execution)
    (reached : next ∈ (app.dispatch players command execution).support) : predicate next := by
  obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  exact invariant.resume _ middle next
    (invariant.environment execution middle command valid supported) moved

theorem PolicyInvariant.runRounds (invariant : app.PolicyInvariant players predicate)
    (scheduler : app.Scheduler) (count : Nat) (execution next : app.Execution)
    (valid : predicate execution)
    (reached : next ∈ (app.runRounds scheduler players count execution).support) :
    predicate next := by
  induction count generalizing execution with
  | zero => cases FinDist.mem_support_pure.mp reached; exact valid
  | succ count ih =>
      obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨command, _, stepped⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      exact ih middle (invariant.dispatch command execution middle valid stepped) moved

def executionInvariant (predicate : app.Execution → Prop) : app.ProtocolState → Prop
  | none => True
  | some control => predicate control.execution

variable [Inhabited app.Memory]

theorem PolicyInvariant.controlStep (invariant : app.PolicyInvariant players predicate)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (setup : ∀ state ∈ initial.support, predicate (Execution.initial app state))
    (before after : app.ProtocolState) (valid : executionInvariant predicate before)
    (reached : after ∈ (app.controlStep initial horizon scheduler players before).support) :
    executionInvariant predicate after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      exact setup state supported
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          obtain ⟨action, supported, stepped⟩ :=
            Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
          simp only [transition, ↓reduceIte, Option.getD_some] at stepped
          cases FinDist.mem_support_pure.mp stepped
          exact invariant.respond execution who action valid supported
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _, supported⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
              exact invariant.environment execution next command valid moved

/-- Includes intermediate scheduler and player states, for any amount of fuel.
Only the chosen players' supported responses constrain the invariant. -/
theorem PolicyInvariant.canonical_run (invariant : app.PolicyInvariant players predicate)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (setup : ∀ state ∈ initial.support, predicate (Execution.initial app state))
    (fuel : Nat) (result : app.ProtocolState)
    (supported : result ∈ (((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler)
        (fun who => app.encodePolicy (players who)) fuel
        (app.protocol initial horizon scheduler).initHistory).map
          ExecutionProtocol.History.state).support) : executionInvariant predicate result := by
  rw [app.run_map_state] at supported
  change result ∈ ((fun law => law.bind (app.controlStep initial horizon scheduler players))^[fuel]
    (FinDist.pure none)).support at supported
  induction fuel generalizing result with
  | zero => cases FinDist.mem_support_pure.mp supported; trivial
  | succ fuel ih =>
      rw [Function.iterate_succ_apply'] at supported
      obtain ⟨before, prior, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      exact invariant.controlStep initial horizon scheduler setup before result (ih before prior)
        reached

end Interaction.ReactiveApplication
