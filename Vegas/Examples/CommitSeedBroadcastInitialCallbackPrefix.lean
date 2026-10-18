/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalZeroSnapshot
import Interaction.ReactiveRoundTrace

/-! # Actual initialized raw histories at the three initial decisions -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Every original clock-zero decision is one of the three literal native
initial callbacks, retaining the actual preceding raw responses. -/
theorem original_zero_callback_prefix (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 0) :
    (owner = alice ∧ execution = initialAliceCallback) ∨
      (∃ first, owner = bob ∧ execution = initialBobCallback first) ∨
      (∃ first second, owner = carol ∧ execution = initialCarolCallback first second) := by
  classical
  have bound := original_zero_clock_index seed ⟨remaining, some owner, execution⟩
    (rawMenu.toRawTrace initial horizon (family seed) trace) original clock
  obtain ⟨_budget, count, before, command, position, prior, selected, actor, moved⟩ :=
    rawMenu.roundSupported_uniform initial horizon (family seed) trace
  have commandEq : command = .activate owner := by
    cases command <;> simp_all only [ReactiveApplication.Command.actor?,
      Option.some.injEq, reduceCtorEq]
  subst command
  have observed : execution = completeActivation before owner := by
    rw [completeActivation_law, PMF.mem_support_pure_iff] at moved
    exact moved
  have priorRun : before ∈ (app.runRounds (family seed) rawMenu.uniformResponses
      count initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using prior
  have beforeLength := app.runRounds_environmentRecall_length (family seed)
    rawMenu.uniformResponses count initialExecution before priorRun
  have short : count ≤ 2 := by
    rw [observed] at bound
    change (before.environmentRecall ++ [_]).length ≤ 3 at bound
    rw [List.length_append, List.length_singleton] at bound
    change before.environmentRecall.length = 0 + count at beforeLength
    omega
  interval_cases count
  · rw [ReactiveApplication.runRounds, PMF.mem_support_pure_iff] at priorRun
    subst before
    rw [initial_alice_choice, PMF.mem_support_pure_iff] at selected
    have same : owner = alice := by simpa only [ReactiveApplication.Command.activate.injEq]
      using selected
    subst owner
    exact Or.inl ⟨rfl, observed⟩
  · rw [ReactiveApplication.runRounds, initial_alice_round, PMF.bind_map] at priorRun
    change before ∈ ((rawMenu.uniformResponses alice []
      (initialAliceCallback.observe app alice)).map
        (initialAliceCallback.respond app alice)).support at priorRun
    obtain ⟨first, _chosen, sameBefore⟩ := (PMF.mem_support_map_iff _ _ _).mp priorRun
    subst before
    rw [initial_bob_choice, PMF.mem_support_pure_iff] at selected
    have same : owner = bob := by simpa only [ReactiveApplication.Command.activate.injEq]
      using selected
    subst owner
    exact Or.inr (Or.inl ⟨first, rfl, observed⟩)
  · change before ∈ ((app.round (family seed) rawMenu.uniformResponses initialExecution).bind
      (app.runRounds (family seed) rawMenu.uniformResponses 1)).support at priorRun
    rw [initial_alice_round, PMF.bind_map, PMF.support_bind] at priorRun
    obtain ⟨first, _first, rest⟩ := Set.mem_iUnion₂.mp priorRun
    change before ∈ ((app.round (family seed) rawMenu.uniformResponses
      (initialAliceCallback.respond app alice first)).bind
        (app.runRounds (family seed) rawMenu.uniformResponses 0)).support at rest
    rw [initial_bob_round] at rest
    change before ∈ (((rawMenu.uniformResponses bob []
      ((initialBobCallback first).observe app bob)).map
        ((initialBobCallback first).respond app bob)).bind PMF.pure).support at rest
    rw [PMF.bind_pure] at rest
    change before ∈ ((rawMenu.uniformResponses bob []
        ((initialBobCallback first).observe app bob)).map
          ((initialBobCallback first).respond app bob)).support at rest
    obtain ⟨second, _chosen, sameBefore⟩ := (PMF.mem_support_map_iff _ _ _).mp rest
    subst before
    rw [initial_carol_choice, PMF.mem_support_pure_iff] at selected
    have same : owner = carol := by simpa only [ReactiveApplication.Command.activate.injEq]
      using selected
    subst owner
    exact Or.inr (Or.inr ⟨first, second, rfl, observed⟩)

private theorem initial_bob_empty_inputs (first : app.Action)
    (empty : (initialBobCallback first).network.inputs = []) : first = ⟨none⟩ := by
  rcases first with ⟨first⟩
  cases first with
  | none => rfl
  | some material =>
      change [_] = [] at empty
      exact (List.cons_ne_nil _ _ empty).elim

private theorem initial_carol_empty_inputs (first second : app.Action)
    (empty : (initialCarolCallback first second).network.inputs = []) :
    first = ⟨none⟩ ∧ second = ⟨none⟩ := by
  rcases first with ⟨first⟩
  rcases second with ⟨second⟩
  cases first with
  | none =>
      cases second with
      | none => exact ⟨rfl, rfl⟩
      | some material =>
          change [_] = [] at empty
          exact (List.cons_ne_nil _ _ empty).elim
  | some material =>
      cases second with
      | none =>
          change [_] = [] at empty
          exact (List.cons_ne_nil _ _ empty).elim
      | some other =>
          change [_, _] = [] at empty
          exact (List.cons_ne_nil _ _ empty).elim

/-- Empty submitted traffic at an initial decision means that every earlier
initial owner waited. The entire physical control is the quiet callback. -/
theorem original_zero_empty_callback (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clock : execution.application.current.native.clock = 0)
    (empty : execution.network.inputs = []) : execution = initialCallback owner := by
  rcases original_zero_callback_prefix seed remaining execution owner trace original clock with
    ⟨rfl, rfl⟩ | ⟨first, rfl, rfl⟩ | ⟨first, second, rfl, rfl⟩
  · rfl
  · rw [initial_bob_empty_inputs first empty]
    rfl
  · obtain ⟨firstEq, secondEq⟩ := initial_carol_empty_inputs first second empty
    rw [firstEq, secondEq]
    rfl

end Vegas.Examples.CommitSeedBroadcast
