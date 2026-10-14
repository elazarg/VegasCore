/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundOccupation
import Interaction.ReactiveMenuOccupation
import GameTheory.Math.Probability.Uniform

/-! # Uniform sampling of actual command-boundary controls -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (scheduler : app.Scheduler) (players : Principal → app.Policy)

/-- The actual control after the next environment command at a fixed round count. -/
def commandControlLaw (initial : PMF app.State) (remaining count : Nat) :
    PMF app.ProtocolState :=
  initial.bind fun state =>
    (app.runRounds scheduler players count (Execution.initial app state)).bind fun before =>
      (scheduler before.environmentRecall (before.observeEnvironment app)).bind fun command =>
        (before.environmentStep app command).map fun active =>
          some ⟨remaining, command.actor? app, active⟩

/-- Uniformly sample precisely one of the actual command indices before the horizon. -/
def occupationControlLaw (initial : PMF app.State) (horizon : Nat) [NeZero horizon] :
    PMF app.ProtocolState :=
  (PMF.uniformOfFintype (Fin horizon)).bind fun time =>
    app.commandControlLaw scheduler players initial (horizon - time.val - 1) time.val

/-- Actual command-boundary expectations retain both initial draws and the full execution. -/
theorem commandControlLaw_expect (initial : PMF app.State) (remaining count : Nat)
    (reward : app.ProtocolState → ℝ) {bound : ℝ}
    (bounded : ∀ state, |reward state| ≤ bound) :
    expect (app.commandControlLaw scheduler players initial remaining count) reward =
      expect initial fun state =>
        expect (app.runRounds scheduler players count (Execution.initial app state))
          (app.roundDecisionReward scheduler reward remaining) := by
  unfold commandControlLaw roundDecisionReward
  rw [expect_bind_tower_bounded _ _ reward bounded]
  apply expect_congr_on_support
  intro state _
  rw [expect_bind_tower_bounded _ _ reward bounded]
  apply expect_congr_on_support
  intro before _
  rw [expect_bind_tower_bounded _ _ reward bounded]
  apply expect_congr_on_support
  intro command _
  exact expect_map _ _ reward

/-- Uniform bounded command sampling gives exact normalized occupation. -/
theorem expect_occupationControlLaw (initial : PMF app.State) (horizon : Nat) [NeZero horizon]
    (reward : app.ProtocolState → ℝ) {bound : ℝ}
    (nonnegative : 0 ≤ bound) (bounded : ∀ state, |reward state| ≤ bound) :
    expect (app.occupationControlLaw scheduler players initial horizon) reward =
      (expect initial fun state => app.roundOccupation scheduler players reward horizon
        (Execution.initial app state)) / horizon := by
  unfold occupationControlLaw
  rw [expect_bind_tower_bounded _ _ reward bounded, expect_uniformFin]
  congr 1
  simp_rw [app.commandControlLaw_expect scheduler players initial _ _ reward bounded]
  rw [← expect_sum initial (fun time : Fin horizon => fun state =>
    expect (app.runRounds scheduler players time.val (Execution.initial app state))
      (app.roundDecisionReward scheduler reward (horizon - time.val - 1))) (fun time =>
        payoffIntegrable_of_bounded initial _ (C := bound) fun state =>
          expect_abs_le_of_bounded nonnegative
            (app.roundDecisionReward_abs_le scheduler reward nonnegative bounded _))]
  apply expect_congr_on_support
  intro state _
  exact (app.roundOccupation_eq_sum_decisions scheduler players reward nonnegative bounded horizon
    (Execution.initial app state)).symm

end Interaction.ReactiveApplication

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) [NeZero horizon] (scheduler : app.Scheduler)
  [Fintype (menu.protocol initial horizon scheduler).History]

/-- Exact active-state occupation mass under a finite menu equals the
normalized actual command-boundary law, across all protocol depths. -/
theorem expect_occupationControlLaw_eq_reach
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (reward : app.ProtocolState → ℝ) {bound : ℝ}
    (nonnegative : 0 ≤ bound) (bounded : ∀ state, |reward state| ≤ bound)
    (idle : ∀ remaining execution, reward (some ⟨remaining, none, execution⟩) = 0)
    (unstarted : reward none = 0) :
    expect (app.occupationControlLaw scheduler
      (menu.decodeProfile initial horizon scheduler profile) initial horizon) reward =
      (∑ history : (menu.protocol initial horizon scheduler).History,
        ((menu.information initial horizon scheduler).historyReachWeight profile history).toReal *
          reward history.state) / horizon := by
  rw [app.expect_occupationControlLaw scheduler _ initial horizon reward nonnegative bounded,
    ← menu.sum_historyReach_reward_eq_roundOccupation initial horizon scheduler profile reward
      nonnegative bounded idle unstarted]

end Interaction.ReactiveApplication.ResponseMenu
