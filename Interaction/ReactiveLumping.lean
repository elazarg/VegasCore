/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveLocalContinuation
import GameTheoryExtensions.Math.Probability.ApproximateLumping

/-! # Lumping the native run through a map of protocol states

Behavioral play of a response menu, read on protocol states, iterates the
control step of the decoded profile (`run_map_controlSteps`). So if the control
step keeps a set of states and, read through a map `φ`, is close on unit
payoffs to an image kernel at every state of the set, then play from a history
whose state is in the set, read through `φ`, is close to the image kernel's
iteration from the image of that state
(`Interaction.ReactiveApplication.ResponseMenu.run_map_unitClose`). Two histories
whose states have the same image therefore give every unit payoff of `φ` of the
final state expectations within twice the accumulated error
(`Interaction.ReactiveApplication.ResponseMenu.run_expect_near_of_image_eq`).
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- **The native run lumps approximately.** -/
theorem run_map_unitClose {Y : Type*}
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (φ : app.ProtocolState → Y) (image : Y → PMF Y) (keep : Set app.ProtocolState) (δ : ℝ)
    (kept : ∀ state ∈ keep, ∀ next ∈ (app.controlStep initial horizon scheduler
      (menu.decodeProfile initial horizon scheduler profile) state).support, next ∈ keep)
    (close : ∀ state ∈ keep, UnitClose δ ((app.controlStep initial horizon scheduler
      (menu.decodeProfile initial horizon scheduler profile) state).map φ) (image (φ state)))
    (fuel : Nat) (history : (menu.protocol initial horizon scheduler).History)
    (start : history.state ∈ keep) :
    UnitClose (fuel * δ)
      (((menu.information initial horizon scheduler).runBehavioralFrom profile fuel history).map
        fun final => φ final.state)
      ((fun law => law.bind image)^[fuel] (PMF.pure (φ history.state))) := by
  have stateLaw := menu.run_map_controlSteps initial horizon scheduler profile fuel history
  have lumped := (iterate_bind_map_unitClose _ φ image keep δ kept close fuel history.state
    start).2
  rw [show (((menu.information initial horizon scheduler).runBehavioralFrom profile fuel
      history).map fun final => φ final.state) =
      (((menu.information initial horizon scheduler).runBehavioralFrom profile fuel
        history).map History.state).map φ from (PMF.map_comp _ _ _).symm, stateLaw]
  exact lumped

/-- **Histories with the same image.** Under approximate lumping, two histories
whose states lie in the kept set and have the same image give every unit payoff
of the image of the final state expectations within `2 * fuel * δ`. -/
theorem run_expect_near_of_image_eq {Y : Type*}
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (φ : app.ProtocolState → Y) (image : Y → PMF Y) (keep : Set app.ProtocolState) (δ : ℝ)
    (kept : ∀ state ∈ keep, ∀ next ∈ (app.controlStep initial horizon scheduler
      (menu.decodeProfile initial horizon scheduler profile) state).support, next ∈ keep)
    (close : ∀ state ∈ keep, UnitClose δ ((app.controlStep initial horizon scheduler
      (menu.decodeProfile initial horizon scheduler profile) state).map φ) (image (φ state)))
    (fuel : Nat) (first second : (menu.protocol initial horizon scheduler).History)
    (firstKept : first.state ∈ keep) (secondKept : second.state ∈ keep)
    (same : φ first.state = φ second.state) (payoff : Y → ℝ)
    (unit : ∀ y, 0 ≤ payoff y ∧ payoff y ≤ 1) :
    |expect ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel first)
        (fun final => payoff (φ final.state)) -
      expect ((menu.information initial horizon scheduler).runBehavioralFrom profile fuel second)
        (fun final => payoff (φ final.state))| ≤ 2 * (fuel * δ) := by
  have firstClose := menu.run_map_unitClose initial horizon scheduler profile φ image keep δ kept
    close fuel first firstKept payoff unit
  have secondClose := menu.run_map_unitClose initial horizon scheduler profile φ image keep δ kept
    close fuel second secondKept payoff unit
  rw [expect_map] at firstClose secondClose
  rw [same] at firstClose
  have left := abs_le.mp firstClose
  have right := abs_le.mp secondClose
  simp only [Function.comp_def] at left right
  rw [abs_le]
  constructor <;> linarith [left.1, left.2, right.1, right.2]

end Interaction.ReactiveApplication.ResponseMenu
