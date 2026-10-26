/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveDecisionBudget
import GameTheoryExtensions.Analysis.Protocol.StoppedCharge

/-! # Actual response counts and their stopped conditional expectation -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  (app : ReactiveApplication Principal)

/-- Count actual recorded player responses, including silence. Environment
commands, initialization and nature branches do not increment this count. -/
def responseCount : app.ProtocolState → Nat
  | none => 0
  | some control => ∑ who, (control.execution.recall who).length

theorem responseCount_step (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.responseCount after = app.responseCount before + app.responseCharge before := by
  cases before with
  | none =>
    obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
    simp [responseCount, responseCharge, actor, Execution.initial]
  | some control =>
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some who =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      change (∑ observer, ((execution.respond app who _).recall observer).length) =
        (∑ observer, (execution.recall observer).length) + 1
      simp_rw [app.respond_recall_length]
      simp [Finset.sum_add_distrib]
    | none =>
      cases remaining with
      | zero =>
        cases (PMF.mem_support_pure_iff _ _).mp reached
        rfl
      | succ remaining =>
        obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
        change (∑ observer, (next.recall observer).length) =
          (∑ observer, (execution.recall observer).length) + 0
        rw [app.environmentStep_recall execution next command supported, Nat.add_zero]

theorem responseCount_add_remainingResponses_step
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.responseCount after + app.remainingResponses horizon after ≤
      app.responseCount before + app.remainingResponses horizon before := by
  have counted := app.responseCount_step initial horizon scheduler before after joint reached
  have budget := app.remainingResponses_step initial horizon scheduler before after joint reached
  omega

theorem responseCount_add_remainingResponses_le
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      app.responseCount state + app.remainingResponses horizon state ≤ horizon
  | _, .start => by change 0 + horizon ≤ horizon; omega
  | _, .extend prior joint _ reached =>
    (app.responseCount_add_remainingResponses_step initial horizon scheduler _ _ joint
      reached).trans
      (responseCount_add_remainingResponses_le initial horizon scheduler prior)

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
  (scheduler : app.Scheduler)

local notation "E" => menu.protocol initial horizon scheduler
local notation "M" => menu.information initial horizon scheduler

theorem cumulativeCharge_eq_responseCount (history : (E).History) :
    cumulativeCharge (fun current : (E).History => (app.responseCharge current.state : ℝ))
      history = app.responseCount history.state := by
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => simp [cumulativeCharge, traceCharge, responseCount, protocol]
  | @extend source target prior joint legal reached ih =>
      change traceCharge _ prior + (app.responseCharge source : ℝ) =
        (app.responseCount target : ℝ)
      rw [show traceCharge _ prior = (app.responseCount source : ℝ) from ih,
        app.responseCount_step initial horizon scheduler source target joint reached,
        Nat.cast_add]

theorem responseCount_le_horizon (history : (E).History) :
    app.responseCount history.state ≤ horizon :=
  (Nat.le_add_right _ _).trans (app.responseCount_add_remainingResponses_le initial horizon
    scheduler (menu.toRawTrace initial horizon scheduler history.trace))

theorem responseCount_integrable (law : PMF (E).History) :
    PayoffIntegrable law (fun final => (app.responseCount final.state : ℝ)) := by
  apply payoffIntegrable_of_bounded law _ (C := horizon)
  intro history
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast menu.responseCount_le_horizon initial horizon scheduler history

/-- Expected actual responses until the chosen stop, conditional on the entire
current history. Padding and nature contribute no response merely by stepping. -/
def expectedResponses (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (M).BehavioralPolicy who) (stopped : (E).History → Prop)
    (history : (E).History) : ℝ :=
  expect ((M).runBehavioralUntil certificate profile stopped history)
    (fun final => (app.responseCount final.state : ℝ)) - app.responseCount history.state

theorem expectedCharge_eq_expectedResponses (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (M).BehavioralPolicy who) (stopped : (E).History → Prop) :
    (M).expectedCharge certificate profile stopped
      (fun current => (app.responseCharge current.state : ℝ)) =
      menu.expectedResponses initial horizon scheduler certificate profile stopped := by
  funext history
  unfold InformationModel.expectedCharge expectedResponses
  rw [menu.cumulativeCharge_eq_responseCount initial horizon scheduler]
  congr 1
  exact expect_congr_on_support fun final _ =>
    menu.cumulativeCharge_eq_responseCount initial horizon scheduler final

theorem stopped_responseCount_bounds (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (M).BehavioralPolicy who) (stopped : (E).History → Prop)
    (start : (E).History) :
    ∀ final ∈ ((M).runBehavioralUntil certificate profile stopped start).support,
      app.responseCount start.state ≤ app.responseCount final.state ∧
        app.responseCount final.state ≤ app.responseCount start.state +
          app.remainingResponses horizon start.state := by
  have invariant := (M).runBehavioralUntil_support_closed certificate profile stopped
    (fun state => app.responseCount start.state ≤ app.responseCount state ∧
      app.responseCount state + app.remainingResponses horizon state ≤
        app.responseCount start.state + app.remainingResponses horizon start.state)
    (start := start) (by
    intro history _ _ joint legal target holds reached
    have counted := app.responseCount_step initial horizon scheduler history.state target joint
      reached
    have budget := app.responseCount_add_remainingResponses_step initial horizon scheduler
      history.state target joint reached
    constructor <;> omega) ⟨le_rfl, le_rfl⟩
  intro final supported
  have holds := invariant final supported
  exact ⟨holds.1, (Nat.le_add_right _ _).trans holds.2⟩

theorem expectedResponses_bounds (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (M).BehavioralPolicy who) (stopped : (E).History → Prop)
    (history : (E).History) :
    0 ≤ menu.expectedResponses initial horizon scheduler certificate profile stopped history ∧
      menu.expectedResponses initial horizon scheduler certificate profile stopped history ≤
        app.remainingResponses horizon history.state := by
  let law := (M).runBehavioralUntil certificate profile stopped history
  have bounds := menu.stopped_responseCount_bounds initial horizon scheduler certificate profile
    stopped history
  have lower := expect_mono (μ := law)
    (f := fun _ => (app.responseCount history.state : ℝ))
    (g := fun final => (app.responseCount final.state : ℝ))
    (fun final supported => by exact_mod_cast (bounds final supported).1)
    (payoffIntegrable_constant law _)
    (menu.responseCount_integrable initial horizon scheduler law)
  have upper := expect_le_const law (fun final => (app.responseCount final.state : ℝ))
    (menu.responseCount_integrable initial horizon scheduler law)
    ((app.responseCount history.state : ℝ) + app.remainingResponses horizon history.state)
    (fun final supported => by exact_mod_cast (bounds final supported).2)
  simp only [expect_constant] at lower
  change 0 ≤ expect law _ - _ ∧ expect law _ - _ ≤ _
  constructor <;> linarith

theorem expectedResponses_integrable (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (M).BehavioralPolicy who) (stopped : (E).History → Prop)
    (law : PMF (E).History) :
    PayoffIntegrable law (menu.expectedResponses initial horizon scheduler certificate profile
      stopped) := by
  rw [← menu.expectedCharge_eq_expectedResponses initial horizon scheduler]
  exact (M).expectedCharge_integrable (menu.bounded initial horizon scheduler) certificate profile
    stopped _ (bound := 1) (fun _ => Nat.cast_nonneg _)
    (fun current => by exact_mod_cast app.responseCharge_le_one current.state) law

/-- The honest conditional expectation pays exactly one unit at a response
step and zero at every environment or initialization step. -/
theorem expectedResponses_drift (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (M).BehavioralPolicy who) (stopped : (E).History → Prop)
    (history : (E).History) (going : ¬ stopped history) (running : ¬ (E).terminal history.state) :
    (app.responseCharge history.state : ℝ) +
      expect ((M).runBehavioralFrom profile 1 history)
        (menu.expectedResponses initial horizon scheduler certificate profile stopped) =
      menu.expectedResponses initial horizon scheduler certificate profile stopped history := by
  simpa only [menu.expectedCharge_eq_expectedResponses initial horizon scheduler] using
    (M).expectedCharge_drift (menu.bounded initial horizon scheduler) certificate profile stopped
      (fun current => (app.responseCharge current.state : ℝ)) (bound := 1)
      (fun _ => Nat.cast_nonneg _)
      (fun current => by exact_mod_cast app.responseCharge_le_one current.state) history going
      running

end ResponseMenu
end Interaction.ReactiveApplication
