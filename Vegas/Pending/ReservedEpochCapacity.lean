/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochSlots

/-! # Submission capacity counted before the physical horizon

Only owner slots can solicit a submission. Packet-processing and expiry
padding therefore do not enter the submission budget.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction

variable {Player : Type} [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def activationCapacity (packetBudget cursor : Nat) : Nat :=
  (cursor / cycleWidth (graph := graph) packetBudget) * Fintype.card Player +
    min (cursor % cycleWidth (graph := graph) packetBudget - packetBudget) (Fintype.card Player)

def ownerSlot (packetBudget cursor : Nat) : Prop :=
  packetBudget ≤ cursor % cycleWidth (graph := graph) packetBudget ∧
    cursor % cycleWidth (graph := graph) packetBudget < packetBudget + Fintype.card Player

instance (packetBudget cursor : Nat) :
    Decidable (ownerSlot (graph := graph) packetBudget cursor) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem activationCapacity_at (packetBudget cycle slot : Nat)
    (bounded : slot < cycleWidth (graph := graph) packetBudget) :
    activationCapacity (graph := graph) packetBudget
        (cycle * cycleWidth (graph := graph) packetBudget + slot) =
      cycle * Fintype.card Player + min (slot - packetBudget) (Fintype.card Player) := by
  simp only [activationCapacity, cursor_div _ _ _ bounded, cursor_mod _ _ _ bounded]

theorem activationCapacity_step_at (packetBudget cycle slot : Nat)
    (bounded : slot < cycleWidth (graph := graph) packetBudget) :
    activationCapacity (graph := graph) packetBudget
        (cycle * cycleWidth (graph := graph) packetBudget + slot + 1) =
      activationCapacity (graph := graph) packetBudget
          (cycle * cycleWidth (graph := graph) packetBudget + slot) +
        if packetBudget ≤ slot ∧ slot < packetBudget + Fintype.card Player then 1 else 0 := by
  by_cases next : slot + 1 < cycleWidth (graph := graph) packetBudget
  · have cursorEq : cycle * cycleWidth (graph := graph) packetBudget + slot + 1 =
        cycle * cycleWidth (graph := graph) packetBudget + (slot + 1) := by omega
    rw [cursorEq, activationCapacity_at _ _ _ next, activationCapacity_at _ _ _ bounded]
    split_ifs <;> omega
  · have last : slot + 1 = cycleWidth (graph := graph) packetBudget := by omega
    have cursorEq : cycle * cycleWidth (graph := graph) packetBudget + slot + 1 =
        (cycle + 1) * cycleWidth (graph := graph) packetBudget + 0 := by
      rw [Nat.add_mul]
      omega
    rw [cursorEq, activationCapacity_at _ _ _ (cycleWidth_pos (graph := graph) packetBudget),
      activationCapacity_at _ _ _ bounded]
    have afterOwners : packetBudget + Fintype.card Player ≤ slot := by
      unfold cycleWidth at last
      omega
    simp only [Nat.zero_sub, min_eq_left (Nat.zero_le _), Nat.add_zero]
    rw [min_eq_right (by omega), ite_eq_right (by omega), Nat.add_mul]
    omega

theorem activationCapacity_step (packetBudget cursor : Nat) :
    activationCapacity (graph := graph) packetBudget (cursor + 1) =
      activationCapacity (graph := graph) packetBudget cursor +
        if ownerSlot (graph := graph) packetBudget cursor then 1 else 0 := by
  have bounded := Nat.mod_lt cursor (cycleWidth_pos (graph := graph) packetBudget)
  have step := activationCapacity_step_at (graph := graph) packetBudget
    (cursor / cycleWidth (graph := graph) packetBudget)
    (cursor % cycleWidth (graph := graph) packetBudget) bounded
  have decomposition : cursor / cycleWidth (graph := graph) packetBudget *
      cycleWidth (graph := graph) packetBudget +
        cursor % cycleWidth (graph := graph) packetBudget = cursor := by
    simpa only [Nat.mul_comm] using
      Nat.div_add_mod cursor (cycleWidth (graph := graph) packetBudget)
  simpa only [decomposition, ownerSlot] using step

theorem activationCapacity_mono (packetBudget : Nat) :
    Monotone (activationCapacity (graph := graph) packetBudget) := by
  apply monotone_nat_of_le_succ
  intro cursor
  rw [activationCapacity_step]
  omega

theorem activationCapacity_cycles (packetBudget cycles : Nat) :
    activationCapacity (graph := graph) packetBudget
      (cycles * cycleWidth (graph := graph) packetBudget) = cycles * Fintype.card Player := by
  simpa using activationCapacity_at (graph := graph) packetBudget cycles 0
    (cycleWidth_pos (graph := graph) packetBudget)

end Vegas.EventGraphRuntime.ReservedEpoch
