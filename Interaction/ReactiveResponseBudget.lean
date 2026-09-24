/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory

/-! # Response counts under a scheduler horizon

An activation spends a scheduler opportunity before the corresponding response.
At an active decision, the player's earlier response count is strictly below
the horizon. This is accounting for actual interaction, not private computation.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def responseBudget (horizon : Nat) : app.ProtocolState → Prop
  | none => True
  | some control => ∀ who, (control.execution.recall who).length + control.remaining +
      (if control.actor = some who then 1 else 0) ≤ horizon

theorem responseBudget_transition (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before after : app.ProtocolState)
    (joint : Principal → Option app.Action) (valid : app.responseBudget horizon before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.responseBudget horizon after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ reached
      intro who
      simp [Execution.initial]
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some actor =>
          cases FinDist.mem_support_pure.mp reached
          intro who
          have budget := valid who
          by_cases same : who = actor
          · subst who
            have grows := congrArg List.length
              (app.respond_actions execution actor ((joint actor).getD ⟨none⟩))
            simp only [List.length_map, List.length_append, List.length_singleton] at grows
            simp only [grows, reduceCtorEq, ↓reduceIte] at budget ⊢
            omega
          · rw [app.respond_recall_other execution actor who same]
            simp only [Option.some.injEq, Ne.symm same, ↓reduceIte, reduceCtorEq] at budget ⊢
            exact budget
      | none =>
          cases remaining with
          | zero =>
              cases FinDist.mem_support_pure.mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, _, supported⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
              intro who
              have budget := valid who
              rw [app.environmentStep_recall execution next command moved]
              simp only [reduceCtorEq, ↓reduceIte] at budget
              change (execution.recall who).length + remaining +
                (if command.actor? app = some who then 1 else 0) ≤ horizon
              split <;> omega

theorem responseBudget_history (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      app.responseBudget horizon state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      app.responseBudget_transition initial horizon scheduler _ _ joint
        (responseBudget_history initial horizon scheduler prior) reached

/-- Even the final activation has an unused response opportunity. -/
theorem active_recall_lt_horizon (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (active : control.actor = some who) :
    (control.execution.recall who).length < horizon := by
  have budget := app.responseBudget_history initial horizon scheduler trace who
  simp only [active, ↓reduceIte] at budget
  omega

end Interaction.ReactiveApplication
