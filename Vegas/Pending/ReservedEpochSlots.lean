/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochScheduler

/-! # Exogenous positions of reserved service operations -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] in
theorem cursor_div (packetBudget cycle slot : Nat)
    (bounded : slot < cycleWidth (graph := graph) packetBudget) :
    (cycle * cycleWidth (graph := graph) packetBudget + slot) /
      cycleWidth (graph := graph) packetBudget = cycle := by
  simpa only [Nat.mul_comm, Nat.div_eq_of_lt bounded, Nat.add_zero] using
    Nat.mul_add_div (cycleWidth_pos (graph := graph) packetBudget) cycle slot

omit [DecidableEq Player] in
theorem cursor_mod (packetBudget cycle slot : Nat)
    (bounded : slot < cycleWidth (graph := graph) packetBudget) :
    (cycle * cycleWidth (graph := graph) packetBudget + slot) %
      cycleWidth (graph := graph) packetBudget = slot := by
  simp [Nat.add_mod, Nat.mod_eq_of_lt bounded]

theorem processing_at {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (cycle slot : Nat) (view : (app).EnvironmentView) (reserved : slot < packetBudget)
    (epoch : tape.processes cycle = true) :
    command runtime leaks packetBudget tape
      (cycle * cycleWidth (graph := graph) packetBudget + slot) view =
        process runtime leaks view := by
  have bounded : slot < cycleWidth (graph := graph) packetBudget := by
    unfold cycleWidth
    omega
  apply processing_command runtime leaks
  · simpa only [cursor_mod _ _ _ bounded] using reserved
  · simpa only [cursor_div _ _ _ bounded] using epoch

theorem activation_at {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (cycle : Nat) (position : Fin (Fintype.card Player)) (view : (app).EnvironmentView)
    (offered : tape.activates cycle (tape.owner cycle position) = true) :
    command runtime leaks packetBudget tape
      (cycle * cycleWidth (graph := graph) packetBudget + (packetBudget + position.val)) view =
        .activate (tape.owner cycle position) := by
  have bounded : packetBudget + position.val < cycleWidth (graph := graph) packetBudget := by
    unfold cycleWidth
    omega
  have notProcessing : ¬ packetBudget + position.val < packetBudget := by omega
  simp only [command, cursor_div _ _ _ bounded, cursor_mod _ _ _ bounded,
    notProcessing, ↓reduceIte, Nat.add_sub_cancel_left]
  simp only [position.isLt, ↓reduceDIte, offered, ↓reduceIte]

/-- An owner's reserved offer position is independent of every application,
packet and receipt observation, including foreign responses earlier in the cycle. -/
theorem activation_view_independent {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (cycle : Nat) (position : Fin (Fintype.card Player))
    (left right : (app).EnvironmentView)
    (offered : tape.activates cycle (tape.owner cycle position) = true) :
    command runtime leaks packetBudget tape
        (cycle * cycleWidth (graph := graph) packetBudget + (packetBudget + position.val)) left =
      command runtime leaks packetBudget tape
        (cycle * cycleWidth (graph := graph) packetBudget +
          (packetBudget + position.val)) right := by
  rw [activation_at runtime leaks packetBudget tape cycle position left offered,
    activation_at runtime leaks packetBudget tape cycle position right offered]

omit [DecidableEq Player] in
theorem every_owner_position {length : Nat} (tape : Tape Player length)
    (cycle : Nat) (owner : Player) :
    ∃ position : Fin (Fintype.card Player), tape.owner cycle position = owner :=
  tape.owner_surjective cycle owner

theorem advance_at {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (cycle : Nat) (view : (app).EnvironmentView) :
    command runtime leaks packetBudget tape
      (cycle * cycleWidth (graph := graph) packetBudget +
        (packetBudget + Fintype.card Player + graph.order.eventCount + 1)) view =
          .application .advanceClock := by
  let slot := packetBudget + Fintype.card Player + graph.order.eventCount + 1
  have bounded : slot < cycleWidth (graph := graph) packetBudget := by
    dsimp [slot, cycleWidth]
    omega
  have processing : ¬ slot < packetBudget := by dsimp [slot]; omega
  have owner : ¬ slot - packetBudget < Fintype.card Player := by dsimp [slot]; omega
  have sampling : slot ≠ packetBudget + Fintype.card Player := by dsimp [slot]; omega
  have expiry : ¬ slot - (packetBudget + Fintype.card Player + 1) <
      graph.order.eventCount := by dsimp [slot]; omega
  change command runtime leaks packetBudget tape
    (cycle * cycleWidth (graph := graph) packetBudget + slot) view = _
  simp [command, cursor_mod _ _ _ bounded,
    processing, owner, sampling, expiry]

end Vegas.EventGraphRuntime.ReservedEpoch
