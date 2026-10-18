/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochSlots
import Vegas.Pending.PhaseSeedClockEffects

/-! # One physical clock advance per reserved cycle -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem process_ticks (view : (app).EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (process runtime leaks view) = 0 := by
  unfold process
  cases view.network.pending.head? <;> rfl

omit [Fintype Player] in
theorem sample_ticks (view : (app).EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks (sample runtime leaks view) = 0 := by
  unfold sample
  split
  · split <;> rfl
  · rfl

theorem command_ticks {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (cursor : Nat) (view : (app).EnvironmentView) :
    PhaseSeedCalendar.commandTicks runtime leaks
        (command runtime leaks packetBudget tape cursor view) =
      if cursor % cycleWidth (graph := graph) packetBudget =
        packetBudget + Fintype.card Player + graph.order.eventCount + 1 then 1 else 0 := by
  have bounded := Nat.mod_lt cursor (cycleWidth_pos (graph := graph) packetBudget)
  unfold command
  dsimp
  split
  · rename_i processing
    have notLast : cursor % cycleWidth (graph := graph) packetBudget ≠
        packetBudget + Fintype.card Player + graph.order.eventCount + 1 := by omega
    rw [ite_eq_right notLast]
    split
    · exact process_ticks runtime leaks view
    · rfl
  · rename_i notProcessing
    split
    · rename_i owned
      have notLast : cursor % cycleWidth (graph := graph) packetBudget ≠
          packetBudget + Fintype.card Player + graph.order.eventCount + 1 := by omega
      rw [ite_eq_right notLast]
      split <;> rfl
    · rename_i notOwned
      split
      · rename_i sampling
        rw [sample_ticks]
        have notLast : cursor % cycleWidth (graph := graph) packetBudget ≠
            packetBudget + Fintype.card Player + graph.order.eventCount + 1 := by omega
        simp only [notLast, ↓reduceIte]
      · rename_i notSampling
        split
        · rename_i expiry
          have notLast : cursor % cycleWidth (graph := graph) packetBudget ≠
              packetBudget + Fintype.card Player + graph.order.eventCount + 1 := by omega
          simp only [PhaseSeedCalendar.commandTicks, EnvironmentCommand.clockTicks,
            notLast, ↓reduceIte]
        · rename_i notExpiry
          have last : cursor % cycleWidth (graph := graph) packetBudget =
              packetBudget + Fintype.card Player + graph.order.eventCount + 1 := by
            change cursor % cycleWidth (graph := graph) packetBudget <
              packetBudget + Fintype.card Player + graph.order.eventCount + 2 at bounded
            omega
          simp only [PhaseSeedCalendar.commandTicks, EnvironmentCommand.clockTicks,
            last, ↓reduceIte]

omit [DecidableEq Player] in
theorem cycle_succ (packetBudget cursor : Nat) :
    (cursor + 1) / cycleWidth (graph := graph) packetBudget =
      cursor / cycleWidth (graph := graph) packetBudget +
        if cursor % cycleWidth (graph := graph) packetBudget =
          packetBudget + Fintype.card Player + graph.order.eventCount + 1 then 1 else 0 := by
  let width := cycleWidth (graph := graph) packetBudget
  let cycle := cursor / width
  let slot := cursor % width
  have positive : 0 < width := cycleWidth_pos (graph := graph) packetBudget
  have bounded : slot < width := Nat.mod_lt cursor positive
  have decomposition : cycle * width + slot = cursor := by
    dsimp [cycle, slot]
    simpa only [Nat.mul_comm] using Nat.div_add_mod cursor width
  have lastIndex : packetBudget + Fintype.card Player + graph.order.eventCount + 1 = width - 1 := by
    dsimp [width, cycleWidth]
  change (cursor + 1) / width = cycle + if slot = _ then 1 else 0
  by_cases last : slot = width - 1
  · have next : cursor + 1 = (cycle + 1) * width + 0 := by
      rw [Nat.add_mul]
      omega
    rw [next, cursor_div _ _ _ positive, lastIndex, ite_eq_left last]
  · have early : slot + 1 < width := by omega
    have next : cursor + 1 = cycle * width + (slot + 1) := by omega
    rw [next, cursor_div _ _ _ early, lastIndex, ite_eq_right last, Nat.add_zero]

end Vegas.EventGraphRuntime.ReservedEpoch
