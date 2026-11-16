module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveServiceProgress
public import Vegas.Pending.ReactiveStateInvariant
public import Vegas.Pending.ReactiveServiceConditions
public import Interaction.ReactiveRawRoundTrace
public import Interaction.ReactiveServiceRounds
public import Interaction.ReactivePendingProcessing
public import Interaction.ReactivePolicyInvariant

@[expose] public section

/-! # Periodic service for two-player graphs with at most four owned events -/

noncomputable section

namespace Vegas.EventGraphRuntime.PeriodicService

open EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

abbrev cycles := 32
abbrev packetBudget := 2 * cycles
abbrev width := packetBudget + 2 + 4 + 1
abbrev horizon := cycles * width

def timeouts (graph : EventGraph Player L) : EventTimeouts graph := ⟨fun _ => 6⟩

def initial (graph : EventGraph Player L)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputLaw : PMF graph.Inputs) : PMF ((reactiveApplication (timeouts graph)) leaks).State :=
  inputLaw.map State.initial

def command (graph : EventGraph Player L) (roster : Bool ≃ Player)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (cursor : Nat) (view : ((reactiveApplication (timeouts graph)) leaks).EnvironmentView) :
    ((reactiveApplication (timeouts graph)) leaks).Command :=
  let app := (reactiveApplication (timeouts graph)) leaks
  let cycle := cursor / width
  let slot := cursor % width
  if slot < packetBudget then (app).pendingHeadCommand view
  else if slot = packetBudget then
    if cycle % 2 = 1 then .activate (roster false) else .wait
  else if slot = packetBudget + 1 then
    if cycle % 2 = 1 then .activate (roster true) else .wait
  else if slot < packetBudget + 2 + 4 then
    if event : slot - (packetBudget + 2) < graph.order.eventCount then
      .application (.expire ⟨slot - (packetBudget + 2), event⟩)
    else .wait
  else .application .advanceClock

def scheduler (graph : EventGraph Player L) (roster : Bool ≃ Player)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    ((reactiveApplication (timeouts graph)) leaks).Scheduler :=
  fun past view => PMF.pure (command graph roster leaks past.length view)

variable {graph : EventGraph Player L} {roster : Bool ≃ Player}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputLaw : PMF graph.Inputs}

local notation "app" => (reactiveApplication (timeouts graph)) leaks
local notation "deadlines" => timeouts graph
local notation "startLaw" => initial graph leaks inputLaw
local notation "schedule" => scheduler graph roster leaks
local notation "selectedCommand" => command graph roster leaks

theorem cursor_arithmetic (cycle slot : Nat) (inside : slot < width) :
    (cycle * width + slot) / width = cycle ∧ (cycle * width + slot) % width = slot := by
  change (cycle * 71 + slot) / 71 = cycle ∧ (cycle * 71 + slot) % 71 = slot
  change slot < 71 at inside
  omega

theorem processing_command (cycle slot : Nat) (view : (app).EnvironmentView)
    (inside : slot < packetBudget) :
    selectedCommand (cycle * width + slot) view = (app).pendingHeadCommand view := by
  have bounded : slot < width := by
    change slot < 64 at inside
    change slot < 71
    omega
  have facts := cursor_arithmetic cycle slot bounded
  simp only [command, facts.2, inside, ↓reduceIte]

theorem first_activation (cycle : Nat) (view : (app).EnvironmentView) (odd : cycle % 2 = 1) :
    selectedCommand (cycle * width + packetBudget) view = .activate (roster false) := by
  have facts := cursor_arithmetic cycle packetBudget (by decide)
  simp [command, facts.1, facts.2, odd]

theorem second_activation (cycle : Nat) (view : (app).EnvironmentView) (odd : cycle % 2 = 1) :
    selectedCommand (cycle * width + (packetBudget + 1)) view = .activate (roster true) := by
  have facts := cursor_arithmetic cycle (packetBudget + 1) (by decide)
  simp [command, facts.1, facts.2, odd]

theorem expire_command (cycle : Nat) (event : graph.EventId)
    (eventBound : event.val < 4) (view : (app).EnvironmentView) :
    selectedCommand (cycle * width + (packetBudget + 2 + event.val)) view =
      .application (.expire event) := by
  have facts := cursor_arithmetic cycle (packetBudget + 2 + event.val) (by
    change 64 + 2 + event.val < 71
    omega)
  have above : ¬ packetBudget + 2 + event.val < packetBudget := by omega
  have notEven : packetBudget + 2 + event.val ≠ packetBudget := by omega
  have notOdd : packetBudget + 2 + event.val ≠ packetBudget + 1 := by omega
  simp only [command, facts.2, above, notEven, notOdd, ↓reduceIte]
  have subtract : packetBudget + 2 + event.val - (packetBudget + 2) = event.val := by omega
  have within : packetBudget + 2 + event.val < packetBudget + 2 + 4 := by omega
  simp only [within, ↓reduceIte, subtract, event.isLt, ↓reduceDIte]

theorem tick_command (cycle : Nat) (view : (app).EnvironmentView) :
    selectedCommand (cycle * width + (width - 1)) view = .application .advanceClock := by
  have facts := cursor_arithmetic cycle (width - 1) (by decide)
  unfold command
  rw [facts.2]
  norm_num [packetBudget, width, cycles]

/-- Physical rounds preserve completed events and live activation times. -/
theorem runRounds_progress (inputs : graph.Inputs) (players : Player → (app).Policy)
    (count : Nat) (before after : (app).Execution) (valid : before.application.Invariant inputs)
    (reached : after ∈ ((app).runRounds schedule players count before).support) :
    ∃ ticks, State.ServiceProgress inputs ticks before.application after.application := by
  let predicate := fun execution : (app).Execution =>
    ∃ ticks, State.ServiceProgress inputs ticks before.application execution.application
  have invariant : (app).PolicyInvariant players predicate := {
    respond := by
      intro execution who action previous _
      obtain ⟨ticks, previous⟩ := previous
      exact ⟨_, previous.trans (reactive_respond_progress deadlines leaks inputs execution who
        action previous.invariant)⟩
    environment := by
      intro execution next selected previous moved
      obtain ⟨ticks, previous⟩ := previous
      exact ⟨_, previous.trans (reactive_environment_progress deadlines leaks inputs execution next
        selected previous.invariant moved)⟩ }
  exact invariant.runRounds schedule count before after ⟨0, .refl valid⟩ reached

omit [DecidableEq Player] in
theorem timely : (AsyncTimely deadlines) (fun _ => 3) (fun _ => 2) := by
  intro event _
  change 3 + 2 < 6
  decide



end Vegas.EventGraphRuntime.PeriodicService
