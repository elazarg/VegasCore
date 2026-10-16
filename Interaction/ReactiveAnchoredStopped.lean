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

/-- From the full authentic anchor, replaying foreign old responses has no
future effect. The focal policy is kept literally unchanged, and the result
retains the original finite-menu history rather than only its control state. -/
theorem runUntil_foreign_anchored
    (certificate : (E).WellFoundedHistories) (players : Principal → app.Policy)
    (focal : Principal) (anchor : app.Control)
    (trace : (E).Trace (some anchor)) (stopped : (E).History → Prop) :
    (N).runBehavioralUntil certificate (fun who => menu.restrictPolicy initial horizon scheduler
      who ((Function.update (ReactiveApplication.anchoredPolicy anchor.execution players)
        focal (players focal)) who)) stopped ⟨some anchor, trace⟩ =
    (N).runBehavioralUntil certificate (fun who => menu.restrictPolicy initial horizon scheduler
      who (players who)) stopped ⟨some anchor, trace⟩ := by
  classical
  apply (N).runBehavioralUntil_congr certificate stopped ⟨some anchor, trace⟩
  intro later reached _running who
  obtain ⟨fuel, path⟩ := reached
  rcases later with ⟨state, laterTrace⟩
  have observed := menu.info initial horizon scheduler who laterTrace
  change (N).infoOf who laterTrace = app.observe who state at observed
  cases state with
  | none => rw [observed]; rfl
  | some current =>
      by_cases active : current.actor = some who
      · have extends_ := app.reaches_recall_prefix initial horizon scheduler
          (menu.reaches_raw initial horizon scheduler path) anchor current rfl rfl who
        have inputLaw : (Function.update
            (ReactiveApplication.anchoredPolicy anchor.execution players) focal (players focal))
              who (current.execution.recall who) (current.execution.observe app who) =
            players who (current.execution.recall who) (current.execution.observe app who) := by
          by_cases own : who = focal
          · subst who
            rw [Function.update_self]
          · rw [Function.update_of_ne own,
              ReactiveApplication.anchoredPolicy_of_extends anchor.execution players who _ _
                extends_]
        simp only [ReactiveApplication.observe, ite_eq_left active] at observed
        rw [observed]
        exact menu.restrictPolicy_eq_of_law_eq initial horizon scheduler who _ _ _ _ inputLaw
      · simp only [ReactiveApplication.observe, ite_eq_right active] at observed
        rw [observed]
        rfl

end Interaction.ReactiveApplication.ResponseMenu
