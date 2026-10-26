/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceTerminalIndifference
import Vegas.Examples.ProgramPaymentsNativeRepresentation
import Interaction.ReactiveResponseCount
import Interaction.ReactiveRoundTrace

noncomputable section

namespace VegasTests.SourceTerminalCallbacks

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def activatingMixture (scheduler : app.Scheduler) (owner : Principal) : app.Scheduler :=
  fun past view => mix (1 / 2 : ℝ) (by norm_num) (by norm_num) (scheduler past view)
    (PMF.pure (.activate owner))

theorem transition_support_mixture (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (owner : Principal) (before after : app.ProtocolState)
    (joint : Principal → Option app.Action)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    after ∈ (app.transition initial horizon (activatingMixture app scheduler owner) before
      joint).support := by
  cases before with
  | none => exact reached
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who => exact reached
      | none =>
          cases remaining with
          | zero => exact reached
          | succ remaining =>
              simp only [ReactiveApplication.transition, activatingMixture, mix_bind] at *
              exact mem_support_mix_left _ _ _ (by norm_num) reached

def trace_mixture (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (owner : Principal) {state}
    (trace : (menu.protocol initial horizon scheduler).Trace state) :
    (menu.protocol initial horizon (activatingMixture app scheduler owner)).Trace state := by
  induction trace with
  | start => exact .start
  | extend prior joint legal realized ih =>
      exact .extend ih joint legal
        (transition_support_mixture app initial horizon scheduler owner _ _ joint realized)


section Native

open Vegas Vegas.Examples.ProgramPayments
open Vegas.Examples.ProgramPaymentsRuntime
open Vegas.Examples.ProgramPaymentsNativeRepresentation

abbrev nativeApp := Vegas.Examples.ProgramPaymentsNativeRepresentation.app
abbrev nativeMenu := Vegas.Examples.ProgramPaymentsNativeRepresentation.menu
abbrev nativeInitial := Vegas.initialLaw (setup 2)

def scheduler : nativeApp.Scheduler := activatingMixture nativeApp (service 2).scheduler .alice

abbrev nativeProtocol := nativeMenu.protocol nativeInitial 9 scheduler
abbrev nativeModel := nativeMenu.information nativeInitial 9 scheduler

def callbackTrace : nativeProtocol.Trace (some ⟨2, some .alice, activate completed⟩) :=
  Classical.choice (nativeMenu.trace_environment nativeInitial 9 scheduler 2 completed
    (activate completed) (.activate .alice)
    (trace_mixture nativeApp nativeMenu nativeInitial 9 (service 2).scheduler .alice completedTrace)
    (by
      exact mem_support_mix_right (1 / 2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
        ((PMF.mem_support_pure_iff _ _).mpr rfl))
    (by rw [activate_law]; exact (PMF.mem_support_pure_iff _ _).mpr rfl))

def callbackHistory : nativeProtocol.History := ⟨_, callbackTrace⟩

theorem callback_source_terminal :
    NativeSourceTerminal (setup := setup 2) (leaks := leaks 2) callbackHistory.state :=
  completed_config_terminal

/-- A genuine source-initialized, bounded raw commit/reveal history reaches a
further callback after its source program has completed. The former full-horizon
response budget is at least one for EVERY continuation profile, whereas the
payoff-aligned source-completion budget is zero. The altered scheduler is used
only for this operational regression; no all-history service contract is claimed. -/
theorem strict_callback_budget (players : ∀ who, nativeModel.BehavioralPolicy who) :
    let certificate := (nativeMenu.bounded nativeInitial 9 scheduler).wellFoundedHistories
    nativeMenu.expectedResponses nativeInitial 9 scheduler certificate players
        (fun history => NativeSourceTerminal (setup := setup 2) (leaks := leaks 2) history.state)
        callbackHistory = 0 ∧
      1 ≤ nativeMenu.expectedResponses nativeInitial 9 scheduler certificate players
        (fun _ => False) callbackHistory := by
  intro certificate
  constructor
  · unfold ReactiveApplication.ResponseMenu.expectedResponses
    rw [nativeModel.runBehavioralUntil_of_stopped certificate players callback_source_terminal,
      expect_pure, sub_self]
  · have running : ¬ nativeProtocol.terminal callbackHistory.state := by
      change ¬ (2 = 0 ∧ (some Player.alice : Option Player) = none)
      simp
    have drift := nativeMenu.expectedResponses_drift nativeInitial 9 scheduler certificate players
      (fun _ => False) callbackHistory (by trivial) running
    have nonnegative := expect_nonneg
      (nativeModel.runBehavioralFrom players 1 callbackHistory)
      (nativeMenu.expectedResponses nativeInitial 9 scheduler certificate players (fun _ => False))
      (fun next _ => (nativeMenu.expectedResponses_bounds nativeInitial 9 scheduler certificate
        players (fun _ => False) next).1)
    have charged : nativeApp.responseCharge callbackHistory.state = 1 := rfl
    rw [charged, Nat.cast_one] at drift
    linarith

end Native

end VegasTests.SourceTerminalCallbacks
