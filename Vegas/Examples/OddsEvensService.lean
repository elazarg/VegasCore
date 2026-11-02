/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensSetup
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveServiceConditions
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveServiceRounds
import Interaction.ReactivePendingProcessing
import Interaction.ReactivePolicyInvariant

/-! # A periodic physical service on the actual forced-exit application -/

noncomputable section

namespace Vegas.Examples.OddsEvensService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

abbrev fixture := OddsEvens.setup
abbrev compiled := OddsEvens.compiled

def leaks : MessageNetwork.ObservationRule OddsEvens.Player (WitnessedPacket compiled) :=
  fun _ _ => PMF.pure ∅

def runtime : EventGraphRuntime compiled := serviceRuntime fixture .sequential (fun _ => 6)

abbrev app := runtime.reactiveApplication leaks

def initial : PMF app.State := Vegas.initialLaw fixture

instance : leaks.FiniteSupport where
  support_finite _ _ := by simp [leaks]

abbrev cycles := 32
abbrev packetBudget := 2 * cycles
abbrev width := packetBudget + 2 + 4 + 1
abbrev horizon := cycles * width

def command (cursor : Nat) (view : app.EnvironmentView) : app.Command :=
  let cycle := cursor / width
  let slot := cursor % width
  if slot < packetBudget then app.pendingHeadCommand view
  else if slot = packetBudget then
    if cycle % 2 = 1 then .activate OddsEvens.even else .wait
  else if slot = packetBudget + 1 then
    if cycle % 2 = 1 then .activate OddsEvens.odd else .wait
  else if event : slot - (packetBudget + 2) < 4 then
    .application (.expire ⟨slot - (packetBudget + 2), event⟩)
  else .application .advanceClock

def scheduler : app.Scheduler := fun past view => PMF.pure (command past.length view)

theorem cursor_arithmetic (cycle slot : Nat) (inside : slot < width) :
    (cycle * width + slot) / width = cycle ∧ (cycle * width + slot) % width = slot := by
  change (cycle * 71 + slot) / 71 = cycle ∧ (cycle * 71 + slot) % 71 = slot
  change slot < 71 at inside
  omega

theorem processing_command (cycle slot : Nat) (view : app.EnvironmentView)
    (inside : slot < packetBudget) :
    command (cycle * width + slot) view = app.pendingHeadCommand view := by
  have bounded : slot < width := by
    change slot < 64 at inside
    change slot < 71
    omega
  have facts := cursor_arithmetic cycle slot bounded
  simp only [command, facts.2, inside, ↓reduceIte]

theorem even_activation (cycle : Nat) (view : app.EnvironmentView) (odd : cycle % 2 = 1) :
    command (cycle * width + packetBudget) view = .activate OddsEvens.even := by
  have facts := cursor_arithmetic cycle packetBudget (by decide)
  simp [command, facts.1, facts.2, odd]

theorem odd_activation (cycle : Nat) (view : app.EnvironmentView) (odd : cycle % 2 = 1) :
    command (cycle * width + (packetBudget + 1)) view = .activate OddsEvens.odd := by
  have facts := cursor_arithmetic cycle (packetBudget + 1) (by decide)
  simp [command, facts.1, facts.2, odd]

theorem expire_command (cycle : Nat) (event : compiled.EventId) (view : app.EnvironmentView) :
    command (cycle * width + (packetBudget + 2 + event.val)) view =
      .application (.expire event) := by
  have eventBound : event.val < 4 := event.isLt
  have facts := cursor_arithmetic cycle (packetBudget + 2 + event.val) (by
    change 64 + 2 + event.val < 71
    omega)
  have above : ¬ packetBudget + 2 + event.val < packetBudget := by omega
  have notEven : packetBudget + 2 + event.val ≠ packetBudget := by omega
  have notOdd : packetBudget + 2 + event.val ≠ packetBudget + 1 := by omega
  simp only [command, facts.2, above, notEven, notOdd, ↓reduceIte]
  have subtract : packetBudget + 2 + event.val - (packetBudget + 2) = event.val := by omega
  simp only [subtract, eventBound, ↓reduceDIte]

theorem tick_command (cycle : Nat) (view : app.EnvironmentView) :
    command (cycle * width + (width - 1)) view = .application .advanceClock := by
  have facts := cursor_arithmetic cycle (width - 1) (by decide)
  unfold command
  rw [facts.2]
  norm_num [packetBudget, width, cycles]

instance : app.FiniteNature initial scheduler where
  toFiniteEnvironment := inferInstance
  initial_finite := by
    change (Vegas.initialLaw fixture).support.Finite
    exact serviceInitialLaw_support_finite fixture .sequential
  scheduler_finite _ _ := by
    rw [scheduler, PMF.support_pure]
    exact Set.finite_singleton _

/-- Physical rounds preserve completed events and live activation times. -/
theorem runRounds_progress (inputs : compiled.Inputs) (players : OddsEvens.Player → app.Policy)
    (count : Nat) (before after : app.Execution) (valid : before.application.Invariant inputs)
    (reached : after ∈ (app.runRounds scheduler players count before).support) :
    ∃ ticks, State.ServiceProgress inputs ticks before.application after.application := by
  let predicate := fun execution : app.Execution =>
    ∃ ticks, State.ServiceProgress inputs ticks before.application execution.application
  have invariant : app.PolicyInvariant players predicate := {
    respond := by
      intro execution who action previous _
      obtain ⟨ticks, previous⟩ := previous
      exact ⟨_, previous.trans (reactive_respond_progress runtime leaks inputs execution who
        action previous.invariant)⟩
    environment := by
      intro execution next selected previous moved
      obtain ⟨ticks, previous⟩ := previous
      exact ⟨_, previous.trans (reactive_environment_progress runtime leaks inputs execution next
        selected previous.invariant moved)⟩ }
  exact invariant.runRounds scheduler count before after ⟨0, .refl valid⟩ reached

theorem timely : runtime.AsyncTimely (fun _ => 3) (fun _ => 2) := by
  intro event _
  change 3 + 2 < 6
  decide

end Vegas.Examples.OddsEvensService
