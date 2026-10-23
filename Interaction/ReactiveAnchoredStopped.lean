/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAnchoredMixture
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Foreign anchoring preserves the original stopped full-history law -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

omit [Fintype Principal] in
/-- Finite restriction depends only on the raw law at its actual input,
including the total default branch when that law is not menu-covered. -/
theorem restrictPolicy_eq_of_law_eq (who : Principal) (first second : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (same : first past view = second past view) :
    menu.restrictPolicy initial horizon scheduler who first (some (past, view)) =
      menu.restrictPolicy initial horizon scheduler who second (some (past, view)) := by
  classical
  by_cases covered : ∀ action ∈ (second past view).support,
      action ∈ menu.actions who past view
  · have firstCovered : ∀ action ∈ (first past view).support,
        action ∈ menu.actions who past view := by rw [same]; exact covered
    apply pmf_map_injective Subtype.val_injective
    rw [menu.restrictPolicy_map_val initial horizon scheduler who first past view firstCovered,
      menu.restrictPolicy_map_val initial horizon scheduler who second past view covered, same]
  · have firstUncovered : ¬ ∀ action ∈ (first past view).support,
        action ∈ menu.actions who past view := by rw [same]; exact covered
    simp only [restrictPolicy, dite_eq_right firstUncovered, dite_eq_right covered]

end Interaction.ReactiveApplication.ResponseMenu
