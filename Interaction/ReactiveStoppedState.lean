/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveLocalContinuation
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Play until a stopping set reads only the state it starts from

On the protocol of a response menu, one step of play from a history reads only
its state (`Interaction.ReactiveApplication.ResponseMenu.run_map_controlSteps`).
So when the stopping set reads only states, the expectation of a function of
the state under play until the stopping set is the same from every two
histories at the same state
(`Interaction.ReactiveApplication.ResponseMenu.expect_runBehavioralUntil_eq_of_state_eq`).
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- One step of play from two histories at the same state reaches the same
states. -/
theorem run_one_map_state_eq_of_state_eq
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    {first second : (menu.protocol initial horizon scheduler).History}
    (same : first.state = second.state) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile 1 first).map
        History.state =
      ((menu.information initial horizon scheduler).runBehavioralFrom profile 1 second).map
        History.state := by
  rw [menu.run_map_controlSteps, menu.run_map_controlSteps, same]

open Classical in
/-- **Play until a stopping set reads only the starting state.** When the
stopping set reads only states, a bounded function of the state has the same
expectation under play until the stopping set from two histories at the same
state. -/
theorem expect_runBehavioralUntil_eq_of_state_eq
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (stopped : (menu.protocol initial horizon scheduler).History → Prop)
    (stoppedState : ∀ first second : (menu.protocol initial horizon scheduler).History,
      first.state = second.state → (stopped first ↔ stopped second))
    (payoff : app.ProtocolState → ℝ) {bound : ℝ} (bounded : ∀ state, |payoff state| ≤ bound) :
    ∀ first second : (menu.protocol initial horizon scheduler).History,
      first.state = second.state →
      expect ((menu.information initial horizon scheduler).runBehavioralUntil certificate
          profile stopped first) (fun stop => payoff stop.state) =
        expect ((menu.information initial horizon scheduler).runBehavioralUntil certificate
          profile stopped second) (fun stop => payoff stop.state) := by
  let model := menu.information initial horizon scheduler
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (bounded none)
  have stopBounded : ∀ stop : (menu.protocol initial horizon scheduler).History,
      |payoff stop.state| ≤ bound := fun stop => bounded stop.state
  have untilBounded : ∀ start, |expect (model.runBehavioralUntil certificate profile stopped
      start) (fun stop => payoff stop.state)| ≤ bound := fun start =>
    expect_abs_le_of_bounded boundNonneg stopBounded
  intro first
  induction first using certificate.induction with
  | _ history ih =>
  intro second same
  by_cases halt : stopped history
  · have halted := (stoppedState history second same).mp halt
    rw [model.runBehavioralUntil_of_stopped certificate profile halt,
      model.runBehavioralUntil_of_stopped certificate profile halted, expect_pure, expect_pure,
      same]
  by_cases ended : (menu.protocol initial horizon scheduler).terminal history.state
  · have endedSecond : (menu.protocol initial horizon scheduler).terminal second.state := by
      rw [← same]
      exact ended
    rw [model.runBehavioralUntil_of_terminal certificate profile ended,
      model.runBehavioralUntil_of_terminal certificate profile endedSecond, expect_pure,
      expect_pure, same]
  have haltSecond : ¬ stopped second := fun halted =>
    halt ((stoppedState history second same).mpr halted)
  have endedSecond : ¬ (menu.protocol initial horizon scheduler).terminal second.state := by
    rw [← same]
    exact ended
  let later := fun next => expect (model.runBehavioralUntil certificate profile stopped next)
    (fun stop => payoff stop.state)
  -- The continuation value read off a successor's state.
  let readOff : app.ProtocolState → ℝ := fun state =>
    if reached : ∃ next ∈ (model.runBehavioralFrom profile 1 history).support,
        next.state = state then later reached.choose else 0
  have readOffEq : ∀ next ∈ (model.runBehavioralFrom profile 1 history).support,
      ∀ other : (menu.protocol initial horizon scheduler).History, other.state = next.state →
      later other = readOff next.state := by
    intro next member other otherState
    have reached : ∃ found ∈ (model.runBehavioralFrom profile 1 history).support,
        found.state = next.state := ⟨next, member, rfl⟩
    simp only [readOff, reached, ↓reduceDIte]
    have chosen := reached.choose_spec
    exact (ih reached.choose (model.mem_support_runBehavioralFrom_one profile ended
      chosen.1).1 other (chosen.2.trans otherState.symm)).symm
  rw [model.runBehavioralUntil_of_running certificate profile halt ended,
    model.runBehavioralUntil_of_running certificate profile haltSecond endedSecond,
    expect_bind_tower_bounded _ _ _ stopBounded, expect_bind_tower_bounded _ _ _ stopBounded]
  change expect (model.runBehavioralFrom profile 1 history) later =
    expect (model.runBehavioralFrom profile 1 second) later
  have stateLaws := menu.run_one_map_state_eq_of_state_eq initial horizon scheduler profile same
  rw [expect_congr_on_support (g := readOff ∘ History.state)
      (fun next member => readOffEq next member next rfl),
    expect_congr_on_support (μ := model.runBehavioralFrom profile 1 second)
      (g := readOff ∘ History.state) (fun next member => ?_),
    ← expect_map, ← expect_map, stateLaws]
  have inSecond : next.state ∈ ((model.runBehavioralFrom profile 1 second).map
      History.state).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨next, member, rfl⟩
  rw [← stateLaws, PMF.mem_support_map_iff] at inSecond
  obtain ⟨found, foundMember, foundState⟩ := inSecond
  rw [Function.comp_apply, ← foundState]
  exact readOffEq found foundMember next foundState.symm

end Interaction.ReactiveApplication.ResponseMenu
