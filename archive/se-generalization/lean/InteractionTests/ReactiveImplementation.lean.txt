/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveImplementation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Private state stays outside the reactive game

The first fixture retains a random bit across two submissions. The second
uses an unbounded private counter with no effect on any behavioral response.
-/

noncomputable section

namespace InteractionTests.ReactiveImplementation

open Interaction GameTheory.Math.Probability

private abbrev app : ReactiveApplication Bool where
  State := Unit
  Payload := Bool
  Submission := Bool
  EnvironmentCommand := Empty
  LocalObservation := Unit
  PublicObservation := Unit
  packet := fun _ _ _ => id
  submit state _ _ := state
  handle state _ := some state
  environment _ command := nomatch command
  observePlayer _ _ := ()
  observePublic _ := ()
  observePending _ _ := PMF.pure ∅

private def send (bit : Bool) : app.Action := ⟨some bit⟩

private def retainedBit : app.Implementation Bool where
  initial := (PMF.uniformOfFintype _)
  respond bit _ := PMF.pure (send bit, bit)

private def scheduler : app.Scheduler := fun _ _ => PMF.pure (.activate false)
private def players : Bool → app.Policy := fun _ _ _ => PMF.pure ⟨none⟩
private def initial : app.Execution := .initial app ()

private def activated (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate false⟩] }

private def once (bit : Bool) : app.Execution :=
  (activated initial).respond app false (send bit)

private def twice (bit : Bool) : app.Execution :=
  (activated (once bit)).respond app false (send bit)

theorem private_two (bit : Bool) :
    retainedBit.run false players scheduler 2 initial bit = PMF.pure (twice bit) := by
  simp only [ReactiveApplication.Implementation.run, ReactiveApplication.Implementation.runJoint,
    ReactiveApplication.Implementation.round,
    scheduler, PMF.pure_bind, ReactiveApplication.Execution.environmentStep,
    PMF.pure_map, MessageNetwork.learn_empty, ReactiveApplication.Command.actor?,
    ReactiveApplication.Implementation.resume, ↓reduceIte, retainedBit]
  rfl

/-- Behavioral realization retains the correlation between the two packets. -/
theorem behavioral_two :
    app.runRounds scheduler (Function.update players false retainedBit.policy) 2 initial =
      (PMF.uniformOfFintype Bool).map twice := by
  unfold initial
  rw [← retainedBit.realize_initial false players scheduler 2 ()]
  change (PMF.uniformOfFintype Bool).bind _ = _
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro bit _
  exact private_two bit

theorem correlated_packets (bit : Bool) :
    (twice bit).network.pending = [⟨(false, 0), bit⟩, ⟨(false, 1), bit⟩] ∧
      ((twice bit).recall false).length = 2 := ⟨rfl, rfl⟩

private def counter (initialLaw : PMF Nat) : app.Implementation Nat where
  initial := initialLaw
  respond value _ := PMF.pure (⟨none⟩, value + 1)

/-- Arbitrarily represented private counters add no choices to any game menu,
and give the same behavioral policy even at off-path information states. -/
theorem counter_policy (initialLaw : PMF Nat) (past : List app.PlayerEntry)
    (view : app.PlayerView) : (counter initialLaw).policy past view = PMF.pure ⟨none⟩ := by
  rw [ReactiveApplication.Implementation.policy_eq]
  simp only [counter, PMF.map_bind, PMF.pure_map, PMF.bind_const]

end InteractionTests.ReactiveImplementation
