/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochDelivery
import Interaction.ReactiveStopping

/-! # Empty padding slots preserve actual network and receipt state -/

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

theorem empty_processing_round {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (players : Player → (app).Policy) (cycle slot : Nat) (before : (app).Execution)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget + slot)
    (reserved : slot < packetBudget) (epoch : tape.processes cycle = true)
    (empty : before.network.pending = []) :
    (app).round (family runtime leaks packetBudget tape) players before =
      PMF.pure { before with environmentRecall := before.environmentRecall ++
        [⟨before.observeEnvironment app, .wait⟩] } := by
  have selected : command runtime leaks packetBudget tape before.environmentRecall.length
      (before.observeEnvironment app) = .wait := by
    rw [cursor, processing_at runtime leaks packetBudget tape cycle slot _ reserved epoch]
    exact processing_empty runtime leaks (before.observeEnvironment app) empty
  simp [ReactiveApplication.round, family, selected, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume]

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

theorem empty_processing_segment {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (players : Player → (app).Policy) (cycle slot count : Nat) (before after : (app).Execution)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget + slot)
    (reserved : slot + count ≤ packetBudget) (epoch : tape.processes cycle = true)
    (empty : before.network.pending = [])
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      count before).support) :
    after.network = before.network ∧ after.receipts = before.receipts ∧
      after.environmentRecall.length = before.environmentRecall.length + count ∧
      after.application = before.application := by
  rw [empty_processing_prefix_law runtime leaks packetBudget tape players cycle slot count
    before cursor reserved epoch empty] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  exact ⟨emptyPrefix_network runtime leaks count before,
    emptyPrefix_receipts runtime leaks count before, emptyPrefix_length runtime leaks count before,
    emptyPrefix_application runtime leaks count before⟩

theorem full_processing_epoch_clears {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy) (cycle : Nat)
    (before after : (app).Execution)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget)
    (capacity : before.network.pending.length ≤ packetBudget) (epoch : tape.processes cycle = true)
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      packetBudget before).support) :
    after.network.pending = [] ∧ after.network.ledger =
      before.network.ledger ++ before.network.pending ∧ before.receipts <+: after.receipts ∧
      (∀ message ∈ before.network.pending,
        message ∈ after.network.ledger ∧ ∃ accepted, (message.id, accepted) ∈ after.receipts) := by
  have splitCount : packetBudget =
      before.network.pending.length + (packetBudget - before.network.pending.length) := by omega
  have splitLaw := (app).runRounds_add (family runtime leaks packetBudget tape) players
    before.network.pending.length (packetBudget - before.network.pending.length) before
  rw [← splitCount] at splitLaw
  rw [splitLaw] at reached
  obtain ⟨middle, prefixReached, suffixReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have cleared := processing_segment runtime leaks packetBudget tape players cycle 0
    before.network.pending before middle (by simpa only [Nat.add_zero] using cursor)
      (by simpa only [Nat.zero_add] using capacity) epoch rfl prefixReached
  have middleCursor := (app).runRounds_environmentRecall_length
    (family runtime leaks packetBudget tape) players before.network.pending.length before middle
      prefixReached
  rw [cursor] at middleCursor
  obtain ⟨network, receipts, _recalled, _application⟩ :=
    empty_processing_segment runtime leaks packetBudget tape
    players cycle before.network.pending.length (packetBudget - before.network.pending.length)
      middle after middleCursor (by omega) epoch cleared.1 suffixReached
  rw [network, receipts]
  refine ⟨cleared.1, cleared.2.1, cleared.2.2.1, ?_⟩
  intro message member
  refine ⟨?_, cleared.2.2.2.1 message member⟩
  rw [cleared.2.1]
  exact List.mem_append_right _ member

end Vegas.EventGraphRuntime.ReservedEpoch
