/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitTimingInformationInformation

/-! # Alice's complete information after the two original silent responses -/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def initialWaitEntry (bit : Bool) : app.PlayerEntry :=
  ⟨(aliceFirst bit).observe app alice, ⟨none⟩, none⟩

theorem quietApplication_alice_view (first second : Bool) (clock : Nat) :
    (quietApplication first clock).playerView alice =
      (quietApplication second clock).playerView alice := by
  let update : (EventGraphRuntime.PlayerView graph × PhasePublicView graph) →
      EventGraphRuntime.PlayerView graph × PhasePublicView graph := fun view =>
    ({ view.1 with publicView := { view.1.publicView with clock := clock } },
      { view.2 with native := { view.2.native with clock := clock } })
  exact congrArg update (initial_alice_playerView first second)

theorem alice_empty_good_input (bit : Bool) :
    nativeInput alice (aliceEmptyGood bit) =
      ([initialWaitEntry bit],
        ReactiveApplication.PlayerView.mk (app := app) (MessageNetwork.empty.observe alice)
          ((quietApplication bit 2).playerView alice) []) := by
  apply Prod.ext
  · rfl
  · change (aliceEmptyGood bit).observe app alice = _
    unfold ReactiveApplication.Execution.observe
    have network : (aliceEmptyGood bit).network = MessageNetwork.empty := by
      simp only [aliceEmptyGood, completeActivation,
        ReactiveApplication.Execution.sampledActivation, quietStart_network,
        MessageNetwork.empty, List.map_nil, List.toFinset_nil, MessageNetwork.learn_empty]
    rw [network]
    change ReactiveApplication.PlayerView.mk (app := app) _
      ((quietStart bit).application.playerView alice)
      [] = _
    rw [quietStart_application]

theorem alice_clock_two_input_private_bit_independent (first second : Bool) :
    nativeInput alice (aliceEmptyGood first) = nativeInput alice (aliceEmptyGood second) := by
  rw [alice_empty_good_input, alice_empty_good_input]
  have views := congrArg Prod.snd (aliceFirst_input_independent first second)
  have entries : initialWaitEntry first = initialWaitEntry second := by
    exact congrArg (fun view : app.PlayerView => (⟨view, ⟨none⟩, none⟩ : app.PlayerEntry)) views
  rw [entries, quietApplication_alice_view first second]

/-- In the good branch the early poll has already recorded Alice's WAIT,
then Bob WAITs and both unused inclusion commands are passive. -/
def beforeAliceThreeGood (bit : Bool) : app.Execution :=
  advance (pause (pause (pause ((bobAfterGood bit ⟨none⟩).respond app bob ⟨none⟩))))

def aliceThreeNoEarlyGood (bit : Bool) : app.Execution :=
  completeActivation (beforeAliceThreeGood bit) alice

/-- In the bad branch Alice's WAIT is recorded after Bob's WAIT. -/
def beforeAliceThreeBad (bit : Bool) : app.Execution :=
  advance (pause ((aliceEmptyBad bit).respond app alice ⟨none⟩))

def aliceThreeNoEarlyBad (bit : Bool) : app.Execution :=
  completeActivation (beforeAliceThreeBad bit) alice

private theorem beforeAliceThreeGood_application (bit : Bool) :
    (beforeAliceThreeGood bit).application = quietApplication bit 3 := by
  apply advance_application _ bit 2
  exact quietStart_application bit

private theorem beforeAliceThreeBad_application (bit : Bool) :
    (beforeAliceThreeBad bit).application = quietApplication bit 3 := by
  apply advance_application _ bit 2
  exact quietStart_application bit

private theorem beforeAliceThreeGood_network (bit : Bool) :
    (beforeAliceThreeGood bit).network = MessageNetwork.empty := by
  simp only [beforeAliceThreeGood, bobAfterGood, aliceEmptyGood, completeActivation, pause,
    advance, PhaseRuntimeState.normalizeExecution, PhaseBindingRepair.rawClock,
    ReactiveApplication.Execution.sampledActivation, ReactiveApplication.Execution.respond,
    quietStart_network, MessageNetwork.empty, List.map_nil, List.toFinset_nil,
    MessageNetwork.learn_empty]

private theorem beforeAliceThreeBad_network (bit : Bool) :
    (beforeAliceThreeBad bit).network = MessageNetwork.empty := by
  simp only [beforeAliceThreeBad, aliceEmptyBad, bobBeforeBad, completeActivation, pause,
    advance, PhaseRuntimeState.normalizeExecution, PhaseBindingRepair.rawClock,
    ReactiveApplication.Execution.sampledActivation, ReactiveApplication.Execution.respond,
    quietStart_network, MessageNetwork.empty, List.map_nil, List.toFinset_nil,
    MessageNetwork.learn_empty]

private theorem aliceThreeNoEarlyGood_input (bit : Bool) :
    nativeInput alice (aliceThreeNoEarlyGood bit) =
      ([initialWaitEntry bit, ⟨(aliceEmptyGood bit).observe app alice, ⟨none⟩, none⟩],
        ReactiveApplication.PlayerView.mk (app := app) (MessageNetwork.empty.observe alice)
          ((quietApplication bit 3).playerView alice) []) := by
  apply Prod.ext
  · rfl
  · change (aliceThreeNoEarlyGood bit).observe app alice = _
    unfold ReactiveApplication.Execution.observe
    have network : (aliceThreeNoEarlyGood bit).network = MessageNetwork.empty := by
      simp only [aliceThreeNoEarlyGood, completeActivation,
        ReactiveApplication.Execution.sampledActivation, beforeAliceThreeGood_network,
        MessageNetwork.empty, List.map_nil, List.toFinset_nil, MessageNetwork.learn_empty]
    rw [network]
    change ReactiveApplication.PlayerView.mk (app := app) _
      ((beforeAliceThreeGood bit).application.playerView alice) [] = _
    rw [beforeAliceThreeGood_application]

private theorem aliceThreeNoEarlyBad_input (bit : Bool) :
    nativeInput alice (aliceThreeNoEarlyBad bit) =
      ([initialWaitEntry bit, ⟨(aliceEmptyBad bit).observe app alice, ⟨none⟩, none⟩],
        ReactiveApplication.PlayerView.mk (app := app) (MessageNetwork.empty.observe alice)
          ((quietApplication bit 3).playerView alice) []) := by
  apply Prod.ext
  · rfl
  · change (aliceThreeNoEarlyBad bit).observe app alice = _
    unfold ReactiveApplication.Execution.observe
    have network : (aliceThreeNoEarlyBad bit).network = MessageNetwork.empty := by
      simp only [aliceThreeNoEarlyBad, completeActivation,
        ReactiveApplication.Execution.sampledActivation, beforeAliceThreeBad_network,
        MessageNetwork.empty, List.map_nil, List.toFinset_nil, MessageNetwork.learn_empty]
    rw [network]
    change ReactiveApplication.PlayerView.mk (app := app) _
      ((beforeAliceThreeBad bit).application.playerView alice) [] = _
    rw [beforeAliceThreeBad_application]

/-- With both actual clock-two actions silent, the entire clock-three Alice
input is identical on the two original poll placements. -/
theorem alice_clock_three_no_early_input (bit : Bool) :
    nativeInput alice (aliceThreeNoEarlyGood bit) =
      nativeInput alice (aliceThreeNoEarlyBad bit) := by
  rw [aliceThreeNoEarlyGood_input, aliceThreeNoEarlyBad_input]
  have views := congrArg Prod.snd (alice_clock_two_empty_input bit)
  change (aliceEmptyGood bit).observe app alice =
    (aliceEmptyBad bit).observe app alice at views
  rw [views]

theorem alice_clock_three_no_early_private_bit_independent (first second : Bool) :
    nativeInput alice (aliceThreeNoEarlyGood first) =
      nativeInput alice (aliceThreeNoEarlyGood second) := by
  rw [aliceThreeNoEarlyGood_input, aliceThreeNoEarlyGood_input]
  have initial := congrArg Prod.snd (aliceFirst_input_independent first second)
  have secondView := congrArg Prod.snd
    (alice_clock_two_input_private_bit_independent first second)
  change (aliceEmptyGood first).observe app alice =
    (aliceEmptyGood second).observe app alice at secondView
  have entries : initialWaitEntry first = initialWaitEntry second := by
    exact congrArg (fun view : app.PlayerView => (⟨view, ⟨none⟩, none⟩ : app.PlayerEntry)) initial
  rw [entries, secondView, quietApplication_alice_view first second]

end Vegas.Examples.CommitTimingInformation
