/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveAnchoredTrace
import Interaction.ReactiveRoundTrace

/-! # Recovering menu traces from literal permitted response records -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

theorem trace_of_recorded_actions (menu : app.ResponseMenu)
    (silence : ∀ who past view, (⟨none⟩ : app.Action) ∈ menu.actions who past view)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (current : app.Control) (trace : (app.protocol initial horizon scheduler).Trace (some current))
    (permitted : ∀ owner earlier entry later,
      current.execution.recall owner = earlier ++ entry :: later →
      entry.action ∈ menu.actions owner earlier entry.beforeView) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace (some current)) := by
  classical
  let silent : Principal → app.Policy := fun _ => app.silentPolicy
  let players := ReactiveApplication.anchoredPolicy current.execution silent
  have covered (owner : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
      (action : app.Action) (selected : action ∈ (players owner past view).support) :
      action ∈ menu.actions owner past view := by
    change action ∈
      (ReactiveApplication.anchoredPolicy current.execution silent owner past view).support
      at selected
    unfold ReactiveApplication.anchoredPolicy at selected
    cases found : (current.execution.recall owner)[past.length]? with
    | none =>
        rw [found] at selected
        cases (PMF.mem_support_pure_iff _ _).mp selected
        exact silence owner past view
    | some entry =>
        rw [found] at selected
        dsimp only at selected
        by_cases matched : past ++ [entry] <+: current.execution.recall owner ∧
            entry.beforeView = view
        · rw [ite_eq_left matched, PMF.mem_support_pure_iff] at selected
          subst action
          obtain ⟨later, joined⟩ := matched.1
          have recalled : current.execution.recall owner = past ++ entry :: later := by
            simpa only [List.append_assoc, List.singleton_append] using joined.symm
          rw [← matched.2]
          exact permitted owner past entry later recalled
        · rw [ite_eq_right matched] at selected
          cases (PMF.mem_support_pure_iff _ _).mp selected
          exact silence owner past view
  have actual := ReactiveApplication.anchored_of_trace initial horizon scheduler current.execution
    silent trace current rfl
      (fun _ => List.prefix_refl _)
  rcases current with ⟨remaining, actor, execution⟩
  obtain ⟨bounded, actual⟩ := actual
  cases actor with
  | none =>
      obtain ⟨counted⟩ := menu.trace_roundsFrom initial horizon scheduler players covered
        (horizon - remaining) (by omega) execution actual
      have countEq : horizon - (horizon - remaining) = remaining := Nat.sub_sub_self bounded
      rw [countEq] at counted
      exact ⟨counted⟩
  | some owner =>
      obtain ⟨strict, before, reached, command, selected, acting, moved⟩ := actual
      change remaining < horizon at strict
      obtain ⟨prior⟩ := menu.trace_roundsFrom initial horizon scheduler players covered
        (horizon - remaining - 1) (by omega) before reached
      have countEq : horizon - (horizon - remaining - 1) = remaining + 1 := by omega
      rw [countEq] at prior
      obtain ⟨after⟩ := menu.trace_environment initial horizon scheduler remaining before
        execution command prior selected moved
      rw [acting] at after
      exact ⟨after⟩

end Interaction.ReactiveApplication.ResponseMenu
