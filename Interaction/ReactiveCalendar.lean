/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory

/-! # Remaining service opportunities at scheduled activations

Every environment transition consumes exactly one scheduler opportunity and
appends one command to its recall. A player response does neither. If a player
can be activated at only one position, every one of its decision histories has
the same remaining service horizon. This is a fact about legal histories; the
position need not be added to the player's observation.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def calendarPosition (horizon : Nat) (who : Principal) (position : Nat) :
    app.ProtocolState → Prop
  | none => True
  | some control =>
      control.execution.environmentRecall.length + control.remaining = horizon ∧
      (control.actor = some who → control.execution.environmentRecall.length = position + 1)

theorem calendarPosition_transition (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal) (position : Nat)
    (unique : ∀ history view command, command ∈ (scheduler history view).support →
      command.actor? app = some who → history.length = position)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (valid : app.calendarPosition horizon who position before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.calendarPosition horizon who position after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact ⟨by simp [Execution.initial], by simp⟩
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some actor =>
          cases FinDist.mem_support_pure.mp reached
          refine ⟨?_, by simp⟩
          rw [app.respond_environmentRecall]
          exact valid.1
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, selected, moved⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
              obtain ⟨updated, _, same⟩ := FinDist.support_map .. ▸ supported
              cases same
              change (execution.environmentRecall ++ [_]).length + remaining = horizon ∧ _
              simp only [List.length_append, List.length_singleton]
              have accounted : execution.environmentRecall.length + (remaining + 1) = horizon :=
                valid.1
              refine ⟨by omega, ?_⟩
              intro active
              have located := unique execution.environmentRecall
                (execution.observeEnvironment app) command selected active
              simp only [located]

theorem calendarPosition_history (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal) (position : Nat)
    (unique : ∀ history view command, command ∈ (scheduler history view).support →
      command.actor? app = some who → history.length = position) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      app.calendarPosition horizon who position state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      app.calendarPosition_transition initial horizon scheduler who position unique _ _ joint
        (calendarPosition_history initial horizon scheduler who position unique prior) reached

/-- Exact remaining time at every legal decision of a uniquely scheduled player. -/
theorem remaining_at_activation (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (who : Principal) (position : Nat)
    (unique : ∀ history view command, command ∈ (scheduler history view).support →
      command.actor? app = some who → history.length = position)
    (control : app.Control) (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (active : control.actor = some who) :
    control.execution.environmentRecall.length = position + 1 ∧
      control.remaining + (position + 1) = horizon := by
  have valid := app.calendarPosition_history initial horizon scheduler who position unique trace
  have located := valid.2 active
  exact ⟨located, by have accounted := valid.1; omega⟩

end Interaction.ReactiveApplication
