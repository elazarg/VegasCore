/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu
import Interaction.ReactiveRecallInvariant

/-! # Actual legal origins of remembered responses -/

noncomputable section

namespace Interaction.ReactiveApplication

/-- A response appends its actual view, action and emitted envelope to own recall. -/
theorem respond_recall_entry {Principal : Type} [DecidableEq Principal]
    (app : ReactiveApplication Principal) (execution : app.Execution) (owner : Principal)
    (action : app.Action) :
    ∃ emitted, (execution.respond app owner action).recall owner =
      execution.recall owner ++ [⟨execution.observe app owner, action, emitted⟩] := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨none, by simp only [Execution.respond, ↓reduceIte]⟩
  | some material =>
      exact ⟨some (execution.network.submit owner
        (app.packet (app.submit execution.application owner material) owner
          (execution.network.known owner) material)).1, by
            simp only [Execution.respond, ↓reduceIte]⟩

end Interaction.ReactiveApplication

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)

/-- Every remembered response retains its actual earlier active menu history,
pre-response observation and menu legality. -/
theorem recorded_response_prefix
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (entry : app.PlayerEntry) (recorded : entry ∈ control.execution.recall who) :
    ∃ before : app.Control,
      Nonempty ((menu.protocol initial horizon scheduler).Trace (some before)) ∧
      before.actor = some who ∧ entry.beforeView = before.execution.observe app who ∧
      entry.action ∈ menu.actions who (before.execution.recall who)
        (before.execution.observe app who) := by
  have origin : ∀ {state} (_history : (menu.protocol initial horizon scheduler).Trace state),
      state.elim True (fun current => ∀ who entry, entry ∈ current.execution.recall who →
        ∃ before : app.Control,
          Nonempty ((menu.protocol initial horizon scheduler).Trace (some before)) ∧
          before.actor = some who ∧ entry.beforeView = before.execution.observe app who ∧
          entry.action ∈ menu.actions who (before.execution.recall who)
            (before.execution.observe app who)) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈ (app.transition initial horizon scheduler source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
            intro who entry member
            exact (List.not_mem_nil member).elim
        | some current =>
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some acting =>
                have localLegal := legal.2 acting
                obtain ⟨action, chosen, permitted⟩ : ∃ action, joint acting = some action ∧
                    action ∈ menu.actions acting (execution.recall acting)
                      (execution.observe app acting) := by
                  cases chosen : joint acting with
                  | none =>
                      rw [chosen] at localLegal
                      exact False.elim (localLegal rfl)
                  | some action =>
                      rw [chosen] at localLegal
                      exact ⟨action, rfl, localLegal.2⟩
                cases (PMF.mem_support_pure_iff _ _).mp reached
                intro who entry member
                simp only [chosen, Option.getD_some] at member
                by_cases same : who = acting
                · subst who
                  rcases action with ⟨transmission⟩
                  cases transmission <;>
                    simp only [Execution.respond, ↓reduceIte, List.mem_append,
                      List.mem_singleton] at member
                  all_goals rcases member with earlier | rfl
                  all_goals first
                    | exact ih acting entry earlier
                    | exact ⟨⟨remaining, some acting, execution⟩, ⟨prior⟩, rfl, rfl, permitted⟩
                · rw [app.respond_recall_other execution acting who same action] at member
                  exact ih who entry member
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    intro who entry member
                    rw [app.environmentStep_recall execution next command supported] at member
                    exact ih who entry member
  exact origin trace who entry recorded

end Interaction.ReactiveApplication.ResponseMenu

end
