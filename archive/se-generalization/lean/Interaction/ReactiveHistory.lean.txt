/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecall
import GameTheory.Protocol.SubgamePerfect

/-! # Recall prefixes along complete reactive histories -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem respond_environmentRecall (execution : app.Execution) (who : Principal)
    (action : app.Action) :
    (execution.respond app who action).environmentRecall = execution.environmentRecall := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission => rfl

theorem respond_actions (execution : app.Execution) (who : Principal) (action : app.Action) :
    ((execution.respond app who action).recall who).map PlayerEntry.action =
      (execution.recall who).map PlayerEntry.action ++ [action] := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => simp only [Execution.respond, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
  | some transmission =>
      simp only [Execution.respond, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]

theorem respond_recall_length (execution : app.Execution) (who observer : Principal)
    (action : app.Action) :
    ((execution.respond app who action).recall observer).length =
      (execution.recall observer).length + if who = observer then 1 else 0 := by
  by_cases same : who = observer
  · subst observer
    have counts := congrArg List.length (app.respond_actions execution who action)
    simpa only [List.length_map, List.length_append, List.length_singleton, ↓reduceIte]
      using counts
  · rw [app.respond_recall_other execution who observer (Ne.symm same) action]
    simp only [same, ↓reduceIte, Nat.add_zero]

/-- An action occurs in a recalled suffix after a response precisely when it
already occurred there or this is that player's new response. -/
theorem respond_recorded_action (execution : app.Execution) (who observer : Principal)
    (action remembered : app.Action) (offset : Nat)
    (within : offset ≤ (execution.recall observer).length) :
    (∃ entry ∈ ((execution.respond app who action).recall observer).drop offset,
      entry.action = remembered) ↔
    (∃ entry ∈ (execution.recall observer).drop offset, entry.action = remembered) ∨
      (observer = who ∧ action = remembered) := by
  by_cases same : observer = who
  · subst observer
    have mapped :
        (((execution.respond app who action).recall who).drop offset).map PlayerEntry.action =
          ((execution.recall who).drop offset).map PlayerEntry.action ++ [action] := by
      rw [List.map_drop, app.respond_actions, List.drop_append_of_le_length]
      · rw [List.map_drop]
      · simpa only [List.length_map] using within
    have membership := congrArg (fun entries => remembered ∈ entries) mapped
    simpa only [List.mem_append, List.mem_map, List.mem_singleton, true_and,
      eq_comm (a := remembered) (b := action)] using Iff.of_eq membership
  · rw [app.respond_recall_other execution who observer same action]
    simp only [same, false_and, or_false]

theorem respond_recall_prefix (execution : app.Execution) (who observer : Principal)
    (action : app.Action) :
    execution.recall observer <+: (execution.respond app who action).recall observer := by
  by_cases same : observer = who
  · subst observer
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => simp only [Execution.respond, ↓reduceIte]; exact ⟨_, rfl⟩
    | some transmission =>
        simp only [Execution.respond, ↓reduceIte]
        exact ⟨_, rfl⟩
  · rw [app.respond_recall_other execution who observer same action]

theorem transition_recall_prefix (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before : app.Control) (after : app.ProtocolState)
    (joint : Principal → Option app.Action)
    (reached : after ∈ (app.transition initial horizon scheduler (some before) joint).support) :
    ∃ next, after = some next ∧
      ∀ who, before.execution.recall who <+: next.execution.recall who := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨_, rfl, fun observer => app.respond_recall_prefix execution who observer _⟩
  | none =>
      cases remaining with
      | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact ⟨_, rfl, fun _ => by rfl⟩
      | succ remaining =>
          obtain ⟨command, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
          refine ⟨_, rfl, fun who => ?_⟩
          rw [app.environmentStep_recall execution next command moved]

theorem reaches_recall_prefix (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last)
    (before after : app.Control) (firstEq : first.state = some before)
    (lastEq : last.state = some after) (who : Principal) :
    before.execution.recall who <+: after.execution.recall who := by
  induction path generalizing before with
  | refl _ history => cases Option.some.inj (firstEq.symm.trans lastEq); rfl
  | @step steps history target joint legal reached supported suffix ih =>
      have moved := supported
      change reached ∈ (app.transition initial horizon scheduler history.state joint).support
        at moved
      rw [firstEq] at moved
      obtain ⟨middle, middleEq, retained⟩ := app.transition_recall_prefix
        initial horizon scheduler before reached joint moved
      exact (retained who).trans (ih middle middleEq lastEq)

end Interaction.ReactiveApplication
