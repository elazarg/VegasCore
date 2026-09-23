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
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => rfl
  | some transmission => cases transmission <;> rfl

theorem respond_actions (execution : app.Execution) (who : Principal) (action : app.Action) :
    ((execution.respond app who action).recall who).map PlayerEntry.action =
      (execution.recall who).map PlayerEntry.action ++ [action] := by
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => simp only [Execution.respond, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
  | some transmission =>
      cases transmission <;>
        simp only [Execution.respond, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]

theorem respond_recall_prefix (execution : app.Execution) (who observer : Principal)
    (action : app.Action) :
    execution.recall observer <+: (execution.respond app who action).recall observer := by
  by_cases same : observer = who
  · subst observer
    rcases action with ⟨memory, transmission⟩
    cases transmission with
    | none => simp only [Execution.respond, ↓reduceIte]; exact ⟨_, rfl⟩
    | some transmission =>
        cases transmission <;> simp only [Execution.respond, ↓reduceIte] <;> exact ⟨_, rfl⟩
  · rw [app.respond_recall_other execution who observer same action]

variable [Inhabited app.Memory]

theorem transition_recall_prefix (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before : app.Control) (after : app.ProtocolState)
    (joint : Principal → Option app.Action)
    (reached : after ∈ (app.transition initial horizon scheduler (some before) joint).support) :
    ∃ next, after = some next ∧
      ∀ who, before.execution.recall who <+: next.execution.recall who := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      cases FinDist.mem_support_pure.mp reached
      exact ⟨_, rfl, fun observer => app.respond_recall_prefix execution who observer _⟩
  | none =>
      cases remaining with
      | zero => cases FinDist.mem_support_pure.mp reached; exact ⟨_, rfl, fun _ => by rfl⟩
      | succ remaining =>
          obtain ⟨command, _, supported⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
          obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
          refine ⟨_, rfl, fun who => ?_⟩
          rw [app.environmentStep_recall execution next command moved]

theorem reaches_recall_prefix (initial : FinDist app.State) (horizon : Nat)
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
