/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochDelivery
import Vegas.Pending.ReservedEpochEmptyProcessing

/-! # The actual application updates of a complete reserved processing batch -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem processing_prefix_application {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy) (cycle slot : Nat)
    (packets untouched : List (Message Player (app).Payload)) (before after : (app).Execution)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget + slot)
    (room : slot + packets.length ≤ packetBudget) (epoch : tape.processes cycle = true)
    (pending : before.network.pending = packets ++ untouched)
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      packets.length before).support) :
    after.network.pending = untouched ∧ after.application = packets.foldl
      (fun state message => ((app).handle state message).getD state) before.application := by
  induction packets generalizing slot before after with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨pending, rfl⟩
  | cons message rest ih =>
      have headPending : before.network.pending = message :: (rest ++ untouched) := pending
      have reserved : slot < packetBudget := by simp only [List.length_cons] at room; omega
      have round : (app).round (family runtime leaks packetBudget tape) players before =
          (app).dispatch players (process runtime leaks (before.observeEnvironment app))
            before := by
        simp only [ReactiveApplication.round, family, PMF.pure_bind]
        rw [cursor, processing_at runtime leaks packetBudget tape cycle slot _ reserved epoch]
      simp only [List.length_cons, ReactiveApplication.runRounds, round] at reached
      obtain ⟨middle, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have step := process_step runtime leaks players before middle message (rest ++ untouched)
        headPending moved
      have physical : middle.application = ((app).handle before.application message).getD
          before.application := by
        rw [process_dispatch runtime leaks players before message (rest ++ untouched)
          headPending] at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        have found : before.network.lookup message.id = some message := by
          simp [MessageNetwork.lookup, headPending]
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found]
      have nextCursor : middle.environmentRecall.length =
          cycle * cycleWidth (graph := graph) packetBudget + (slot + 1) := by
        rw [step.2.2.2.2, cursor]
        omega
      have nextRoom : slot + 1 + rest.length ≤ packetBudget := by
        simp only [List.length_cons] at room
        omega
      have tail := ih (slot + 1) middle after nextCursor nextRoom step.1 continued
      refine ⟨tail.1, ?_⟩
      rw [tail.2, physical]
      rfl

theorem processing_epoch_application {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy) (cycle : Nat)
    (before after : (app).Execution)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget)
    (capacity : before.network.pending.length ≤ packetBudget) (epoch : tape.processes cycle = true)
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      packetBudget before).support) :
    after.application = before.network.pending.foldl
      (fun state message => ((app).handle state message).getD state) before.application := by
  have splitCount : packetBudget = before.network.pending.length +
      (packetBudget - before.network.pending.length) := by omega
  have splitLaw := (app).runRounds_add (family runtime leaks packetBudget tape) players
    before.network.pending.length (packetBudget - before.network.pending.length) before
  rw [← splitCount] at splitLaw
  rw [splitLaw] at reached
  obtain ⟨middle, prefixReached, suffixReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have processed := processing_prefix_application runtime leaks packetBudget tape players cycle 0
    before.network.pending [] before middle (by simpa only [Nat.add_zero] using cursor)
      (by simpa only [Nat.zero_add] using capacity) epoch (by simp only [List.append_nil])
        prefixReached
  have cleared := processing_segment runtime leaks packetBudget tape players cycle 0
    before.network.pending before middle (by simpa only [Nat.add_zero] using cursor)
      (by simpa only [Nat.zero_add] using capacity) epoch rfl prefixReached
  have middleCursor := (app).runRounds_environmentRecall_length
    (family runtime leaks packetBudget tape) players before.network.pending.length before middle
      prefixReached
  rw [cursor] at middleCursor
  have padding := empty_processing_segment runtime leaks packetBudget tape players cycle
    before.network.pending.length (packetBudget - before.network.pending.length) middle after
      middleCursor (by omega) epoch cleared.1 suffixReached
  exact padding.2.2.2.trans processed.2

end Vegas.EventGraphRuntime.ReservedEpoch
