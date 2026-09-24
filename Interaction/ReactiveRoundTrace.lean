/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundReachability

/-! # Round support yields actual legal menu histories

This is the converse operational bridge: each supported scheduler round is
expanded into its environment transition and optional single player response.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) (initial : FinDist app.State) (horizon : Nat)
  (scheduler : app.Scheduler)

theorem trace_respond (remaining : Nat) (execution : app.Execution) (who : Principal)
    (response : app.Action)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (available : response ∈ menu.actions who (execution.recall who) (execution.observe app who)) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, execution.respond app who response⟩)) := by
  refine ⟨trace.extend (fun actor => if actor = who then some response else none) ?_ ?_⟩
  · constructor
    · simp [protocol, terminal]
    · intro actor
      by_cases same : actor = who
      · subst actor
        simpa [protocol, ReactiveApplication.actor, ResponseMenu.available] using available
      · simp [protocol, ReactiveApplication.actor, same, Ne.symm same]
  · change _ ∈ (FinDist.pure _).support
    simp only [↓reduceIte, Option.getD_some, FinDist.mem_support_pure]

theorem trace_environment (remaining : Nat) (execution next : app.Execution)
    (command : app.Command)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (selected : command ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment app)).support)
    (moved : next ∈ (execution.environmentStep app command).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, command.actor? app, next⟩)) := by
  refine ⟨trace.extend (fun _ => none) ?_ ?_⟩
  · constructor
    · simp [protocol, terminal]
    · intro who
      simp [protocol, actor]
  · change _ ∈ ((scheduler execution.environmentRecall
      (execution.observeEnvironment app)).bind _).support
    rw [FinDist.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨command, selected, ?_⟩
    rw [FinDist.support_map]
    exact ⟨next, moved, rfl⟩

theorem trace_round (players : Principal → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view)
    (remaining : Nat) (execution next : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (supported : next ∈ (app.round scheduler players execution).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, next⟩)) := by
  obtain ⟨command, selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨observed, moved, resumed⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ dispatched)
  obtain ⟨pending⟩ := menu.trace_environment initial horizon scheduler remaining execution observed
    command trace selected moved
  cases active : command.actor? app with
  | none =>
      rw [active] at pending
      change next ∈ (app.resume players (command.actor? app) observed).support at resumed
      rw [active] at resumed
      cases FinDist.mem_support_pure.mp resumed
      exact ⟨pending⟩
  | some who =>
      rw [active] at pending
      change next ∈ (app.resume players (command.actor? app) observed).support at resumed
      rw [active] at resumed
      obtain ⟨response, chosen, rfl⟩ := FinDist.support_map .. ▸ resumed
      exact menu.trace_respond initial horizon scheduler remaining observed who response pending
        (covered who _ _ response chosen)

theorem trace_runRounds (players : Principal → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view)
    (remaining count : Nat) (execution next : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
    (supported : next ∈ (app.runRounds scheduler players count execution).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, next⟩)) := by
  induction count generalizing execution with
  | zero =>
      cases FinDist.mem_support_pure.mp supported
      exact ⟨trace⟩
  | succ count ih =>
      obtain ⟨middle, moved, finished⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      obtain ⟨middleTrace⟩ := menu.trace_round initial horizon scheduler players covered
        (remaining + count) execution middle trace moved
      exact ih middle middleTrace finished

theorem trace_roundsFrom (players : Principal → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view)
    (count : Nat) (bounded : count ≤ horizon) (execution : app.Execution)
    (supported : execution ∈ (app.roundsFrom initial scheduler players count).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨horizon - count, none, execution⟩)) := by
  obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have start : Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨horizon, none, Execution.initial app state⟩)) := by
    refine ⟨.extend .start (fun _ => none) ?_ ?_⟩
    · constructor
      · change ¬False
        trivial
      · intro who
        simp [protocol, actor]
    · change _ ∈ (initial.map _).support
      rw [FinDist.support_map]
      exact ⟨state, stateMem, rfl⟩
  obtain ⟨trace⟩ := start
  exact menu.trace_runRounds initial horizon scheduler players covered (horizon - count) count
    (Execution.initial app state) execution (by simpa only [Nat.sub_add_cancel bounded] using trace)
      reached

end Interaction.ReactiveApplication.ResponseMenu
