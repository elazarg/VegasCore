/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensSetup
import Vegas.Pending.ExclusionServiceProgress
import Vegas.Pending.ExclusionService
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveServiceRounds
import Interaction.ReactivePendingProcessing

/-! # A periodic physical service on the actual forced-exit application -/

noncomputable section

namespace Vegas.Examples.OddsEvensRecoveryService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

abbrev fixture := OddsEvens.setup
abbrev compiled := OddsEvens.compiled

def leaks : MessageNetwork.ObservationRule OddsEvens.Player (WitnessedPacket compiled) :=
  fun _ _ => PMF.pure ∅

def runtime : EventGraphRuntime compiled := serviceRuntime fixture .sequential (fun _ => 6)

abbrev app := recoveryApplication runtime leaks

def initial : PMF app.State := (Vegas.initialLaw fixture).map fun native => ⟨native, ∅⟩

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
  observePending_finite _ _ := by
    change (PMF.pure ∅).support.Finite
    rw [PMF.support_pure]
    exact Set.finite_singleton _
  environment_finite state native := by
    change (state.environment runtime native).support.Finite
    rw [RecoveryState.environment, PMF.support_map]
    exact (runtime.environmentStep_support_finite _ _).image _
  initial_finite := by
    rw [initial, PMF.support_map]
    have nativeFinite : (Vegas.initialLaw fixture).support.Finite := by
      rw [Vegas.initialLaw, serviceInitialLaw, PMF.support_map]
      exact fixture.initialLaw_support_finite.image _
    exact nativeFinite.image _
  scheduler_finite _ _ := by
    rw [scheduler, PMF.support_pure]
    exact Set.finite_singleton _

theorem timely : runtime.AsyncTimely (fun _ => 3) (fun _ => 2) := by
  intro event _
  change 3 + 2 < 6
  decide

end Vegas.Examples.OddsEvensRecoveryService
