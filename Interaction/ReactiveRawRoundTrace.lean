/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundReachability

/-! # Rounds of arbitrary players are legal raw histories

The raw protocol offers every response, so any players' scheduler rounds from
initialization trace a legal raw history with the horizon accounted by the
environment recall. No admissibility condition on the players is needed.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- Every initialized raw history accounts for the scheduler horizon by its
completed environment recall and remaining rounds. Player responses consume
no scheduler rounds. -/
theorem raw_trace_horizon {control : app.Control}
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    control.execution.environmentRecall.length + control.remaining = horizon := by
  have accounted : ∀ {state}
      (_trace : (app.protocol initial horizon scheduler).Trace state),
      state.elim True (fun current =>
        current.execution.environmentRecall.length + current.remaining = horizon) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈ (app.transition initial horizon scheduler source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
            change 0 + horizon = horizon
            omega
        | some current =>
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some who =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                simpa only [Option.elim_some, app.respond_environmentRecall] using ih
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    have length : next.environmentRecall = execution.environmentRecall ++
                        [⟨execution.observeEnvironment app, command⟩] := by
                      unfold ReactiveApplication.Execution.environmentStep at supported
                      obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ supported
                      rfl
                    simp only [Option.elim_some] at ih ⊢
                    rw [length, List.length_append, List.length_singleton]
                    omega
  exact accounted trace

theorem raw_trace_respond (remaining : Nat) (execution : app.Execution) (who : Principal)
    (response : app.Action)
    (trace : (app.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩)) :
    Nonempty ((app.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, execution.respond app who response⟩)) := by
  refine ⟨trace.extend (fun actor => if actor = who then some response else none) ?_ ?_⟩
  · constructor
    · simp [protocol, terminal]
    · intro actor
      by_cases same : actor = who
      · subst actor
        simp [protocol, ReactiveApplication.actor]
      · simp [protocol, ReactiveApplication.actor, same, Ne.symm same]
  · change _ ∈ (PMF.pure _).support
    simp only [↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff _ _]

theorem raw_trace_environment (remaining : Nat) (execution next : app.Execution)
    (command : app.Command)
    (trace : (app.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (selected : command ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment app)).support)
    (moved : next ∈ (execution.environmentStep app command).support) :
    Nonempty ((app.protocol initial horizon scheduler).Trace
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

theorem raw_trace_round (players : Principal → app.Policy) (remaining : Nat)
    (execution next : app.Execution)
    (trace : (app.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (supported : next ∈ (app.round scheduler players execution).support) :
    Nonempty ((app.protocol initial horizon scheduler).Trace (some ⟨remaining, none, next⟩)) := by
  obtain ⟨command, selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨observed, moved, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨pending⟩ := app.raw_trace_environment initial horizon scheduler remaining execution
    observed command trace selected moved
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
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
      exact app.raw_trace_respond initial horizon scheduler remaining observed who response
        pending

theorem raw_trace_runRounds (players : Principal → app.Policy) (remaining count : Nat)
    (execution next : app.Execution)
    (trace : (app.protocol initial horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
    (supported : next ∈ (app.runRounds scheduler players count execution).support) :
    Nonempty ((app.protocol initial horizon scheduler).Trace (some ⟨remaining, none, next⟩)) := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨trace⟩
  | succ count ih =>
      obtain ⟨middle, moved, finished⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨middleTrace⟩ := app.raw_trace_round initial horizon scheduler players
        (remaining + count) execution middle trace moved
      exact ih middle middleTrace finished

/-- Any players' rounds from initialization trace a legal raw history. -/
theorem raw_trace_roundsFrom (players : Principal → app.Policy) (count : Nat)
    (bounded : count ≤ horizon) (execution : app.Execution)
    (supported : execution ∈ (app.roundsFrom initial scheduler players count).support) :
    Nonempty ((app.protocol initial horizon scheduler).Trace
      (some ⟨horizon - count, none, execution⟩)) := by
  obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  have start : Nonempty ((app.protocol initial horizon scheduler).Trace
      (some ⟨horizon, none, Execution.initial app state⟩)) := by
    refine ⟨.extend .start (fun _ => none) ?_ ?_⟩
    · constructor
      · change ¬False
        trivial
      · intro who
        simp [protocol, actor]
    · change _ ∈ (initial.map _).support
      rw [PMF.support_map]
      exact ⟨state, stateMem, rfl⟩
  obtain ⟨trace⟩ := start
  exact app.raw_trace_runRounds initial horizon scheduler players (horizon - count) count
    (Execution.initial app state) execution (by simpa only [Nat.sub_add_cancel bounded] using trace)
    reached

end Interaction.ReactiveApplication
