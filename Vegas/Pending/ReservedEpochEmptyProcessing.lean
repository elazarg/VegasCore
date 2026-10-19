/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochDelivery
import Interaction.ReactiveStopping

/-! # Empty padding slots preserve actual network and receipt state -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

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
  induction count generalizing slot before after with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rfl, rfl, by omega, rfl⟩
  | succ count ih =>
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      rw [empty_processing_round runtime leaks packetBudget tape players cycle slot before
        cursor (by omega) epoch empty] at moved
      let padded : (app).Execution := { before with
        environmentRecall := before.environmentRecall ++ [⟨before.observeEnvironment app, .wait⟩] }
      have actual : middle = padded := (PMF.mem_support_pure_iff _ _).mp moved
      subst middle
      have nextCursor : padded.environmentRecall.length =
          cycle * cycleWidth (graph := graph) packetBudget + (slot + 1) := by
        dsimp [padded]
        rw [List.length_append, List.length_singleton, cursor]
        omega
      obtain ⟨network, receipts, recalled, application⟩ := ih (slot + 1) padded after nextCursor
        (by omega) empty rest
      exact ⟨network, receipts, by
        simp only [padded, List.length_append, List.length_singleton] at recalled
        omega, application⟩

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
