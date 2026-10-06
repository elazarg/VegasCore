/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundReachability
import Interaction.ReactiveMenuPolicy

/-! # Round support yields actual legal menu histories

This is the converse operational bridge: each supported scheduler round is
expanded into its environment transition and optional single player response.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
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
  · change _ ∈ (PMF.pure _).support
    simp only [↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff _ _]

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
    rw [PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨command, selected, ?_⟩
    rw [PMF.support_map]
    exact ⟨next, moved, rfl⟩

/-- One supported round of admissible players from a legal idle history is a
legal idle history. Admissibility is needed only at legal decisions. -/
theorem trace_round_of_admissible (players : Principal → app.Policy)
    (admissible : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (remaining : Nat) (execution next : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (supported : next ∈ (app.round scheduler players execution).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, next⟩)) := by
  obtain ⟨command, selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨observed, moved, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨pending⟩ := menu.trace_environment initial horizon scheduler remaining execution observed
    command trace selected moved
  cases active : command.actor? app with
  | none =>
      rw [active] at pending
      change next ∈ (app.resume players (command.actor? app) observed).support at resumed
      rw [active] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact ⟨pending⟩
  | some who =>
      rw [active] at pending
      change next ∈ (app.resume players (command.actor? app) observed).support at resumed
      rw [active] at resumed
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ resumed
      exact menu.trace_respond initial horizon scheduler remaining observed who response pending
        (admissible who _ pending rfl response chosen)

/-- Players whose responses always lie in the menu are admissible. -/
theorem admissible_of_covered (players : Principal → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view) (who : Principal) :
    menu.Admissible initial horizon scheduler who (players who) :=
  fun _ _ _ action chosen => covered who _ _ action chosen

theorem trace_round (players : Principal → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view)
    (remaining : Nat) (execution next : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (supported : next ∈ (app.round scheduler players execution).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, next⟩)) :=
  menu.trace_round_of_admissible initial horizon scheduler players
    (menu.admissible_of_covered initial horizon scheduler players covered) remaining execution
    next trace supported

theorem trace_runRounds_of_admissible (players : Principal → app.Policy)
    (admissible : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (remaining count : Nat) (execution next : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
    (supported : next ∈ (app.runRounds scheduler players count execution).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, next⟩)) := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨trace⟩
  | succ count ih =>
      obtain ⟨middle, moved, finished⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨middleTrace⟩ := menu.trace_round_of_admissible initial horizon scheduler players
        admissible (remaining + count) execution middle trace moved
      exact ih middle middleTrace finished

theorem trace_runRounds (players : Principal → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view)
    (remaining count : Nat) (execution next : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
    (supported : next ∈ (app.runRounds scheduler players count execution).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, next⟩)) :=
  menu.trace_runRounds_of_admissible initial horizon scheduler players
    (menu.admissible_of_covered initial horizon scheduler players covered) remaining count
    execution next trace supported

/-- Initialization from a supported state is a legal history of every menu. -/
theorem trace_initial (state : app.State) (supported : state ∈ initial.support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨horizon, none, Execution.initial app state⟩)) := by
  refine ⟨.extend .start (fun _ => none) ?_ ?_⟩
  · constructor
    · change ¬False
      trivial
    · intro who
      simp [protocol, actor]
  · change _ ∈ (initial.map _).support
    rw [PMF.support_map]
    exact ⟨state, supported, rfl⟩

theorem trace_roundsFrom_of_admissible (players : Principal → app.Policy)
    (admissible : ∀ who, menu.Admissible initial horizon scheduler who (players who))
    (count : Nat) (bounded : count ≤ horizon) (execution : app.Execution)
    (supported : execution ∈ (app.roundsFrom initial scheduler players count).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨horizon - count, none, execution⟩)) := by
  obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨trace⟩ := menu.trace_initial initial horizon scheduler state stateMem
  exact menu.trace_runRounds_of_admissible initial horizon scheduler players admissible
    (horizon - count) count (Execution.initial app state) execution
    (by simpa only [Nat.sub_add_cancel bounded] using trace) reached

theorem trace_roundsFrom (players : Principal → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view)
    (count : Nat) (bounded : count ≤ horizon) (execution : app.Execution)
    (supported : execution ∈ (app.roundsFrom initial scheduler players count).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨horizon - count, none, execution⟩)) :=
  menu.trace_roundsFrom_of_admissible initial horizon scheduler players
    (menu.admissible_of_covered initial horizon scheduler players covered) count bounded
    execution supported

end Interaction.ReactiveApplication.ResponseMenu
