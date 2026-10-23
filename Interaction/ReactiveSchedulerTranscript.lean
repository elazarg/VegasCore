/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerImplementation
import GameTheory.Math.Probability.Conditioning

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

end Interaction.ReactiveApplication
