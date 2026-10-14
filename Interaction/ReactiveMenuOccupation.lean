/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveOccupationBellman
import Interaction.ReactiveLocalContinuation
import GameTheory.Analysis.Protocol.SequentialRationality
import GameTheory.Protocol.BehavioralTerminal

/-! # Finite-menu reach weights and actual round occupation -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
  [Fintype (menu.protocol initial horizon scheduler).History]

local notation "model" => menu.information initial horizon scheduler
local notation "protocol" => menu.protocol initial horizon scheduler

/-- Complete reach-weighted active occupation is the actual scheduler-round
reward, with no assumption that equal information has equal protocol depth. -/
theorem sum_historyReach_reward_eq_roundOccupation
    (profile : ∀ who, (model).BehavioralPolicy who) (reward : app.ProtocolState → ℝ)
    {bound : ℝ} (nonnegative : 0 ≤ bound) (bounded : ∀ state, |reward state| ≤ bound)
    (idle : ∀ remaining execution, reward (some ⟨remaining, none, execution⟩) = 0)
    (unstarted : reward none = 0) :
    (∑ history : (protocol).History,
      ((model).historyReachWeight profile history).toReal * reward history.state) =
      expect initial fun state => app.roundOccupation scheduler
        (menu.decodeProfile initial horizon scheduler profile) reward horizon
          (ReactiveApplication.Execution.initial app state) := by
  classical
  let players := menu.decodeProfile initial horizon scheduler profile
  let value := app.controlOccupation scheduler players reward initial horizon
  let potential := fun history : (protocol).History => value history.state
  have stepGain (history : (protocol).History) :
      expect ((model).runBehavioralFrom profile 1 history) potential - potential history =
        -reward history.state := by
    have oneLaw := menu.run_map_controlSteps initial horizon scheduler profile 1 history
    simp only [Function.iterate_one, PMF.pure_bind] at oneLaw
    have expected := congrArg (fun law : PMF app.ProtocolState => expect law value) oneLaw
    rw [expect_map] at expected
    change expect ((model).runBehavioralFrom profile 1 history) potential =
      expect (app.controlStep initial horizon scheduler players history.state) value at expected
    have bellman := app.controlOccupation_bellman scheduler players reward initial horizon
      nonnegative bounded idle unstarted history.state
    change value history.state = reward history.state +
      expect (app.controlStep initial horizon scheduler players history.state) value at bellman
    change expect ((model).runBehavioralFrom profile 1 history) potential -
      value history.state = -reward history.state
    rw [expected]
    linarith
  have finalZero : expect ((model).runBehavioral profile (2 * horizon + 1)) potential = 0 := by
    let certificate := (menu.bounded initial horizon scheduler).wellFoundedHistories
    have completed := (model).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      certificate (menu.bounded initial horizon scheduler) profile (protocol).initHistory
    change expect ((model).runBehavioralFrom profile (2 * horizon + 1)
      (protocol).initHistory) potential = 0
    rw [← completed]
    trans expect ((model).runBehavioralTerminalFrom certificate profile (protocol).initHistory)
      (fun _ => (0 : ℝ))
    · apply expect_congr_on_support
      intro final supported
      have ended := (model).runBehavioralTerminalFrom_support_terminal certificate profile
        (protocol).initHistory final supported
      exact app.controlOccupation_terminal scheduler players reward initial horizon idle
        final.state ended
    · exact expect_constant _ 0
  have telescope := (model).runBehavioral_expect_sub_eq_sum_historyStepGains profile potential
    (menu.bounded initial horizon scheduler)
  simp_rw [stepGain, mul_neg] at telescope
  rw [finalZero, zero_sub, Finset.sum_neg_distrib] at telescope
  change -(expect initial fun state => app.roundOccupation scheduler players reward horizon
    (ReactiveApplication.Execution.initial app state)) =
      -(∑ history : (protocol).History,
        ((model).historyReachWeight profile history).toReal * reward history.state) at telescope
  linarith

end Interaction.ReactiveApplication.ResponseMenu
