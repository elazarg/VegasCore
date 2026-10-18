/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochSlots
import Vegas.Pending.ReservedEpochWorkMonotone

/-! # Actual due expiry in the reserved event sweep -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem expiry_at {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (cycle : Nat) (event : graph.EventId) (view : (app).EnvironmentView) :
    command runtime leaks packetBudget tape
      (cycle * cycleWidth (graph := graph) packetBudget +
        (packetBudget + Fintype.card Player + 1 + event.val)) view =
          .application (.expire event) := by
  let slot := packetBudget + Fintype.card Player + 1 + event.val
  have bounded : slot < cycleWidth (graph := graph) packetBudget := by
    dsimp [slot, cycleWidth]
    omega
  have processing : ¬ slot < packetBudget := by dsimp [slot]; omega
  have owner : ¬ slot - packetBudget < Fintype.card Player := by dsimp [slot]; omega
  have sampling : slot ≠ packetBudget + Fintype.card Player := by dsimp [slot]; omega
  have expiry : slot - (packetBudget + Fintype.card Player + 1) <
      graph.order.eventCount := by dsimp [slot]; omega
  change command runtime leaks packetBudget tape
    (cycle * cycleWidth (graph := graph) packetBudget + slot) view = _
  simp only [command, cursor_mod _ _ _ bounded, processing, ↓reduceIte, owner, ↓reduceDIte,
    sampling, expiry]
  congr 3
  dsimp [slot]
  omega

/-- This is the genuine scheduler round, with arbitrary raw player policies.
No player is invoked in the reserved expiry slot. -/
theorem expiry_round_decreases {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy) (cycle : Nat)
    (before after : (app).Execution) (inputs : graph.Inputs)
    (valid : WorkValid inputs before.application)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : before.application.SeedRequest owner coordinate)
    (due : runtime.deadline coordinate.event ≤ before.application.current.native.clock -
      (before.application.current.native.activatedAt coordinate.event).getD
        before.application.current.native.clock)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget +
        (packetBudget + Fintype.card Player + 1 + coordinate.event.val))
    (reached : after ∈ ((app).round (family runtime leaks packetBudget tape)
      players before).support) :
    workRemaining after.application < workRemaining before.application := by
  have selected := expiry_at runtime leaks packetBudget tape cycle coordinate.event
    (before.observeEnvironment app)
  rw [← cursor] at selected
  obtain ⟨chosen, offered, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have chosenEq := (family_support runtime leaks packetBudget tape before.environmentRecall
    (before.observeEnvironment app) chosen).mp offered
  rw [chosenEq, selected] at dispatched
  obtain ⟨middle, observed, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  change after ∈ (PMF.pure middle).support at continued
  have afterEq : after = middle := (PMF.mem_support_pure_iff _ _).mp continued
  subst after
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at observed
  change middle ∈ ((before.application.environment runtime (.expire coordinate.event)).map
    (fun state => { before with
      application := state
      environmentRecall := before.environmentRecall ++
        [⟨before.observeEnvironment app, .application (.expire coordinate.event)⟩] })).support
      at observed
  rw [PMF.support_map] at observed
  obtain ⟨state, moved, rfl⟩ := observed
  exact expiry_work_decreases runtime leaks before.application state valid.1 valid.2.1
    valid.2.2 owner coordinate request due moved

end Vegas.EventGraphRuntime.ReservedEpoch
