/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerImplementation
import GameTheory.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.TaggedPosterior

/-! # Deterministic scheduler posterior from actual command recall

An immutable scheduler seed is filtered exactly by consistency with the recorded
commands. This owning-layer result applies to local controllers and addressed
all-event schedulers without a factorization assumption.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal Seed : Type} (app : ReactiveApplication Principal)

/-- Command consistency uses each entry's actual earlier environment recall. -/
def commandConsistentFrom
    (choose : Seed → List app.EnvironmentEntry → app.EnvironmentView → app.Command)
    (seed : Seed) (earlier : List app.EnvironmentEntry) : List app.EnvironmentEntry → Prop
  | [] => True
  | entry :: rest => choose seed earlier entry.beforeView = entry.command ∧
      commandConsistentFrom choose seed (earlier ++ [entry]) rest

theorem commandConsistentFrom_append
    (choose : Seed → List app.EnvironmentEntry → app.EnvironmentView → app.Command)
    (seed : Seed) (earlier left right : List app.EnvironmentEntry) :
    app.commandConsistentFrom choose seed earlier (left ++ right) ↔
      app.commandConsistentFrom choose seed earlier left ∧
        app.commandConsistentFrom choose seed (earlier ++ left) right := by
  induction left generalizing earlier with
  | nil => simp only [List.nil_append, commandConsistentFrom, List.append_nil, true_and]
  | cons entry rest ih =>
      simp only [List.cons_append, commandConsistentFrom, ih, List.append_assoc,
        List.nil_append, and_assoc]

theorem commandConsistent_snoc
    (choose : Seed → List app.EnvironmentEntry → app.EnvironmentView → app.Command)
    (seed : Seed) (past : List app.EnvironmentEntry) (entry : app.EnvironmentEntry) :
    app.commandConsistentFrom choose seed [] (past ++ [entry]) ↔
      app.commandConsistentFrom choose seed [] past ∧
        choose seed past entry.beforeView = entry.command := by
  simp only [commandConsistentFrom_append, commandConsistentFrom, List.nil_append, and_true]

/-- Reparameterizing an immutable original seed reparameterizes concrete
command consistency, without changing any recorded view or command. -/
theorem commandConsistentFrom_comp {Original : Type}
    (choose : Seed → List app.EnvironmentEntry → app.EnvironmentView → app.Command)
    (read : Original → Seed) (seed : Original) (earlier past : List app.EnvironmentEntry) :
    app.commandConsistentFrom (fun original => choose (read original)) seed earlier past ↔
      app.commandConsistentFrom choose (read seed) earlier past := by
  induction past generalizing earlier with
  | nil => rfl
  | cons entry rest ih => simp only [commandConsistentFrom, ih]

private theorem filter_eq_of_support_eq (prior : PMF Seed) (first second : Set Seed)
    (firstPositive : ∃ seed ∈ first, seed ∈ prior.support)
    (secondPositive : ∃ seed ∈ second, seed ∈ prior.support)
    (matching : ∀ seed ∈ prior.support, seed ∈ first ↔ seed ∈ second) :
    prior.filter first firstPositive = prior.filter second secondPositive := by
  classical
  have indicatorEq : first.indicator prior = second.indicator prior := by
    funext seed
    by_cases supported : seed ∈ prior.support
    · by_cases member : seed ∈ first
      · simp only [Set.indicator_of_mem member,
          Set.indicator_of_mem ((matching seed supported).mp member)]
      · simp only [Set.indicator_of_notMem member,
          Set.indicator_of_notMem (fun h => member ((matching seed supported).mpr h))]
    · have zero : prior seed = 0 := by
        change ¬ prior seed ≠ 0 at supported
        exact Classical.not_not.mp supported
      simp only [Set.indicator, zero, ite_self]
  ext seed
  simp only [PMF.filter_apply, indicatorEq]

/-- The posterior of the real immutable-seed scheduler is exactly its original
law filtered by the actual complete command transcript. -/
theorem schedulerMixture_posterior_eq_filter (prior : PMF Seed)
    (choose : Seed → List app.EnvironmentEntry → app.EnvironmentView → app.Command)
    (past : List app.EnvironmentEntry)
    (positive : ∃ seed ∈ {seed | app.commandConsistentFrom choose seed [] past},
      seed ∈ prior.support) :
    (app.schedulerMixture prior (fun seed before view => PMF.pure
      (choose seed before view))).posterior past =
        prior.filter {seed | app.commandConsistentFrom choose seed [] past} positive := by
  classical
  induction past using List.reverseRecOn with
  | nil =>
      change prior = _
      exact (filter_of_support_subset prior _ positive (by intro seed _; trivial)).symm
  | append_singleton past entry ih =>
      let earlier : Set Seed := {seed | app.commandConsistentFrom choose seed [] past}
      let full : Set Seed := {seed |
        app.commandConsistentFrom choose seed [] (past ++ [entry])}
      have included : full ⊆ earlier := fun seed compatible =>
        ((app.commandConsistent_snoc choose seed past entry).mp compatible).1
      have earlierPositive : ∃ seed ∈ earlier, seed ∈ prior.support := by
        obtain ⟨seed, compatible, supported⟩ := positive
        exact ⟨seed, included compatible, supported⟩
      let current := prior.filter earlier earlierPositive
      let decision := fun seed => choose seed past entry.beforeView
      have fullPositive : ∃ seed ∈ full, seed ∈ current.support := by
        obtain ⟨seed, compatible, supported⟩ := positive
        exact ⟨seed, compatible, (PMF.mem_support_filter_iff earlierPositive).mpr
          ⟨included compatible, supported⟩⟩
      have nextPositive : ∃ seed ∈ {seed | decision seed = entry.command},
          seed ∈ current.support := by
        obtain ⟨seed, compatible, supported⟩ := fullPositive
        exact ⟨seed, ((app.commandConsistent_snoc choose seed past entry).mp compatible).2,
          supported⟩
      rw [SchedulerImplementation.posterior_snoc, ih earlierPositive]
      simp only [schedulerMixture, PMF.pure_map]
      change (fiberPosterior (current.map fun seed => (decision seed, seed))
        Prod.fst entry.command).map Prod.snd = prior.filter full positive
      rw [fiberPosterior_tag, fiberPosterior_eq_filter _ _ nextPositive]
      have conditioned := filter_eq_of_support_eq current
        {seed | decision seed = entry.command} full nextPositive fullPositive
        (fun seed supported => by
          have old := ((PMF.mem_support_filter_iff earlierPositive).mp supported).1
          exact ⟨fun next => (app.commandConsistent_snoc choose seed past entry).mpr
            ⟨old, next⟩, fun whole =>
              ((app.commandConsistent_snoc choose seed past entry).mp whole).2⟩)
      rw [conditioned]
      exact filter_filter_of_subset prior earlier full earlierPositive fullPositive included

/-- Conditioning the actual scheduler posterior on a retained original seed
readout is filtering the same original law on both concrete observations. -/
theorem schedulerMixture_posterior_fiber_eq_filter {Readout : Type}
    (prior : PMF Seed)
    (choose : Seed → List app.EnvironmentEntry → app.EnvironmentView → app.Command)
    (past : List app.EnvironmentEntry) (read : Seed → Readout) (observed : Readout)
    (positive : ∃ seed ∈ {seed |
      app.commandConsistentFrom choose seed [] past ∧ read seed = observed},
        seed ∈ prior.support) :
    fiberPosterior ((app.schedulerMixture prior (fun seed before view => PMF.pure
      (choose seed before view))).posterior past) read observed =
      prior.filter {seed | app.commandConsistentFrom choose seed [] past ∧
        read seed = observed} positive := by
  let earlier : Set Seed := {seed | app.commandConsistentFrom choose seed [] past}
  let full : Set Seed := {seed | app.commandConsistentFrom choose seed [] past ∧
    read seed = observed}
  have earlierPositive : ∃ seed ∈ earlier, seed ∈ prior.support := by
    obtain ⟨seed, compatible, supported⟩ := positive
    exact ⟨seed, compatible.1, supported⟩
  let current := prior.filter earlier earlierPositive
  have fullPositive : ∃ seed ∈ full, seed ∈ current.support := by
    obtain ⟨seed, compatible, supported⟩ := positive
    exact ⟨seed, compatible, (PMF.mem_support_filter_iff earlierPositive).mpr
      ⟨compatible.1, supported⟩⟩
  have readPositive : ∃ seed ∈ {seed | read seed = observed}, seed ∈ current.support := by
    obtain ⟨seed, compatible, supported⟩ := fullPositive
    exact ⟨seed, compatible.2, supported⟩
  rw [app.schedulerMixture_posterior_eq_filter prior choose past earlierPositive,
    fiberPosterior_eq_filter current read readPositive]
  have same := filter_eq_of_support_eq current {seed | read seed = observed} full
    readPositive fullPositive (fun seed supported => by
      have old := ((PMF.mem_support_filter_iff earlierPositive).mp supported).1
      exact ⟨fun observed => ⟨old, observed⟩, fun compatible => compatible.2⟩)
  rw [same]
  exact filter_filter_of_subset prior earlier full earlierPositive fullPositive
    (fun _ compatible => compatible.1)

end Interaction.ReactiveApplication
