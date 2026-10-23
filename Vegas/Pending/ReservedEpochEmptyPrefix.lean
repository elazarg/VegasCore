/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochEmptyProcessing

/-! # Exact empty processing prefixes for arbitrary reserved capacity -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def emptyPrefix : Nat → (app).Execution → (app).Execution
  | 0, execution => execution
  | count + 1, execution => emptyPrefix count
      { execution with environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .wait⟩] }

theorem emptyPrefix_application (count : Nat) (execution : (app).Execution) :
    (emptyPrefix runtime leaks count execution).application = execution.application := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih => exact ih _

theorem emptyPrefix_network (count : Nat) (execution : (app).Execution) :
    (emptyPrefix runtime leaks count execution).network = execution.network := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih => exact ih _

theorem emptyPrefix_recall (count : Nat) (execution : (app).Execution) :
    (emptyPrefix runtime leaks count execution).recall = execution.recall := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih => exact ih _

theorem emptyPrefix_receipts (count : Nat) (execution : (app).Execution) :
    (emptyPrefix runtime leaks count execution).receipts = execution.receipts := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih => exact ih _

theorem emptyPrefix_length (count : Nat) (execution : (app).Execution) :
    (emptyPrefix runtime leaks count execution).environmentRecall.length =
      execution.environmentRecall.length + count := by
  induction count generalizing execution with
  | zero => simp only [emptyPrefix, Nat.add_zero]
  | succ count ih =>
      rw [emptyPrefix, ih, List.length_append, List.length_singleton]
      omega

variable [Fintype Player]

theorem empty_processing_prefix_law {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (cycle slot count : Nat) (before : (app).Execution)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget + slot)
    (reserved : slot + count ≤ packetBudget) (epoch : tape.processes cycle = true)
    (empty : before.network.pending = []) :
    (app).runRounds (family runtime leaks packetBudget tape) players count before =
      PMF.pure (emptyPrefix runtime leaks count before) := by
  induction count generalizing slot before with
  | zero => rfl
  | succ count ih =>
      let next : (app).Execution := { before with environmentRecall :=
        before.environmentRecall ++ [⟨before.observeEnvironment app, .wait⟩] }
      have law := empty_processing_round runtime leaks packetBudget tape players cycle slot before
        cursor (by omega) epoch empty
      change (app).round (family runtime leaks packetBudget tape) players before = PMF.pure next
        at law
      have nextCursor : next.environmentRecall.length =
          cycle * cycleWidth (graph := graph) packetBudget + (slot + 1) := by
        dsimp [next]
        rw [List.length_append, List.length_singleton, cursor]
        omega
      change ((app).round (family runtime leaks packetBudget tape) players before).bind _ = _
      rw [law, PMF.pure_bind]
      exact ih (slot + 1) next nextCursor (by omega) empty

end Vegas.EventGraphRuntime.ReservedEpoch
