/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAnchoredSupport

/-! # The first environment loss along an actual supported round path -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

private theorem resume_preserves_predicate (players : Principal → app.Policy)
    (predicate : app.Execution → Prop)
    (respond : ∀ execution who action, predicate execution →
      predicate (execution.respond app who action))
    (actor : Option Principal) (execution next : app.Execution) (before : predicate execution)
    (reached : next ∈ (app.resume players actor execution).support) : predicate next := by
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact before
  | some who =>
      simp only [resume, invoke, PMF.support_map] at reached
      obtain ⟨action, _chosen, rfl⟩ := reached
      exact respond execution who action before

/-- Responses preserving a predicate leave every actual first loss at an
environment transition. Both the prefix and the remaining supported path are
retained; this is a decomposition of the existing finite round evaluator. -/
theorem runRounds_environment_boundary (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (predicate : app.Execution → Prop)
    (respond : ∀ execution who action, predicate execution →
      predicate (execution.respond app who action))
    (count : Nat) (execution final : app.Execution) (before : predicate execution)
    (reached : final ∈ (app.runRounds scheduler players count execution).support)
    (after : ¬ predicate final) :
    ∃ used remaining prior middle resumed command,
      used + 1 + remaining = count ∧
      prior ∈ (app.runRounds scheduler players used execution).support ∧ predicate prior ∧
      command ∈ (scheduler prior.environmentRecall (prior.observeEnvironment app)).support ∧
      middle ∈ (prior.environmentStep app command).support ∧ ¬ predicate middle ∧
      resumed ∈ (app.resume players (command.actor? app) middle).support ∧
      final ∈ (app.runRounds scheduler players remaining resumed).support := by
  induction count generalizing final with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (after before).elim
  | succ count ih =>
      rw [runRounds_succ_eq_bind_round, PMF.support_bind] at reached
      obtain ⟨previous, priorPath, lastRound⟩ := Set.mem_iUnion₂.mp reached
      by_cases previousInside : predicate previous
      · simp only [round, PMF.support_bind] at lastRound
        obtain ⟨command, chosen, dispatched⟩ := Set.mem_iUnion₂.mp lastRound
        simp only [dispatch, PMF.support_bind] at dispatched
        obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp dispatched
        have lost : ¬ predicate middle := fun valid => after
          (resume_preserves_predicate app players predicate respond (command.actor? app)
            middle final valid resumed)
        exact ⟨count, 0, previous, middle, final, command, by omega, priorPath, previousInside,
          chosen, moved, lost, resumed, by simp only [runRounds, PMF.mem_support_pure_iff _ _]⟩
      · obtain ⟨used, remaining, prior, middle, resumed, command, length, initialPath, inside,
            chosen, moved, lost, response, tail⟩ := ih previous priorPath previousInside
        have continued : final ∈
            (app.runRounds scheduler players (remaining + 1) resumed).support := by
          rw [runRounds_succ_eq_bind_round, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨previous, tail, lastRound⟩
        exact ⟨used, remaining + 1, prior, middle, resumed, command, by omega,
          initialPath, inside, chosen, moved, lost, response, continued⟩

end Interaction.ReactiveApplication
