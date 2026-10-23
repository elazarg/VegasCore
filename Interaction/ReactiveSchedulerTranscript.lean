/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

end Interaction.ReactiveApplication
