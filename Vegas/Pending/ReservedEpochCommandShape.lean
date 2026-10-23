/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochSlots

/-! # Packet inclusion occurs only in marked reserved processing slots -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem sample_ne_include (view : (app).EnvironmentView) (identifier : MessageId Player) :
    sample runtime leaks view ≠ .include identifier := by
  unfold sample
  split
  · split_ifs <;> simp
  · simp

theorem include_requires_processing {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (cursor : Nat) (view : (app).EnvironmentView)
    (identifier : MessageId Player)
    (selected : command runtime leaks packetBudget tape cursor view = .include identifier) :
    cursor % cycleWidth (graph := graph) packetBudget < packetBudget ∧
      tape.processes (cursor / cycleWidth (graph := graph) packetBudget) = true := by
  dsimp only [command] at selected
  split_ifs at selected with processing marked ownerSlot active sampleSlot eventSlot
  · exact ⟨processing, marked⟩
  · exact (sample_ne_include runtime leaks view identifier selected).elim

theorem no_include_between_epochs {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (sentCycle slot cycle : Nat)
    (afterProcessing : packetBudget ≤ slot)
    (quiet : ∀ later, sentCycle < later → later < cycle → tape.processes later = false)
    (cursor : Nat) (view : (app).EnvironmentView)
    (later : sentCycle * cycleWidth (graph := graph) packetBudget + slot ≤ cursor)
    (earlier : cursor < cycle * cycleWidth (graph := graph) packetBudget)
    (identifier : MessageId Player) :
    command runtime leaks packetBudget tape cursor view ≠ .include identifier := by
  intro included
  obtain ⟨reserved, marked⟩ := include_requires_processing runtime leaks packetBudget tape cursor
    view identifier included
  have before : cursor / cycleWidth (graph := graph) packetBudget < cycle :=
    (Nat.div_lt_iff_lt_mul (cycleWidth_pos packetBudget)).mpr earlier
  have after : sentCycle ≤ cursor / cycleWidth (graph := graph) packetBudget :=
    (Nat.le_div_iff_mul_le (cycleWidth_pos packetBudget)).mpr (by omega)
  by_cases same : cursor / cycleWidth (graph := graph) packetBudget = sentCycle
  · have divided := Nat.mod_add_div cursor (cycleWidth (graph := graph) packetBudget)
    rw [same, Nat.mul_comm _ sentCycle] at divided
    omega
  · have starting : sentCycle < cursor / cycleWidth (graph := graph) packetBudget := by omega
    have absent := quiet (cursor / cycleWidth (graph := graph) packetBudget) starting before
    rw [absent] at marked
    cases marked

end Vegas.EventGraphRuntime.ReservedEpoch
