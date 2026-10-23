/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochRequestTimer
import Vegas.Pending.ReservedEpochResolution
import Vegas.Pending.ReservedEpochClockAccounting
import Interaction.ReactiveStopping

/-! # Bounded-cycle semantic progress from a genuine owner request -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Player responses are arbitrary. The expiry sweep alone bounds the time
for which a real owner request can coexist with unchanged semantic work. -/
theorem requested_interval_decreases {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) (cycle limit : Nat)
    (deadline : ∀ event, runtime.deadline event ≤ limit)
    (before after : (app).Execution) (valid : WorkValid inputs before.application)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget)
    (clock : before.application.current.native.clock = cycle)
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : before.application.SeedRequest owner coordinate)
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      ((limit + 2) * cycleWidth (graph := graph) packetBudget) before).support) :
    workRemaining after.application < workRemaining before.application := by
  let width := cycleWidth (graph := graph) packetBudget
  let slot := packetBudget + Fintype.card Player + 1 + coordinate.event.val
  let offset := (limit + 1) * width + slot
  let rest := width - slot - 1
  have slotBound : slot < width := by dsimp [slot, width, cycleWidth]; omega
  have duration : (limit + 2) * width = offset + (rest + 1) := by
    dsimp [offset, rest]
    have expand : (limit + 2) * width = (limit + 1) * width + width := by ring
    omega
  change after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
    ((limit + 2) * width) before).support at reached
  rw [duration, (app).runRounds_add] at reached
  obtain ⟨middle, prefixReached, suffixReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨next, moved, finished⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ suffixReached)
  have middleValid := (work_bounded_invariant runtime leaks
    (family runtime leaks packetBudget tape) inputs (workRemaining before.application)).runRounds
      players offset before middle ⟨valid, le_rfl⟩ prefixReached
  have nextValid := (work_bounded_invariant runtime leaks
    (family runtime leaks packetBudget tape) inputs (workRemaining middle.application)).round
      players middle next ⟨middleValid.1, le_rfl⟩ moved
  have finalBound := runRounds_work_le runtime leaks (family runtime leaks packetBudget tape)
    players rest inputs next after nextValid.1 finished
  by_contra notStrict
  have flat : workRemaining middle.application = workRemaining before.application := by omega
  have activatedSome := (valid.1.active.activated_iff coordinate.event).mpr
    ⟨request.2.2.1, by simp only [request.2.2.2.1, Option.isSome_some]⟩
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp activatedSome
  have enteredBound : entered ≤ cycle := by
    rw [← clock]
    exact valid.1.active.activated_le coordinate.event entered activated
  obtain ⟨middleRequest, middleActivated⟩ := runRounds_flat_request runtime leaks
    (family runtime leaks packetBudget tape) players ordered offset inputs before middle valid
      owner coordinate entered request activated prefixReached flat
  have middleCursor := (app).runRounds_environmentRecall_length
    (family runtime leaks packetBudget tape) players offset before middle prefixReached
  have cursorEq : middle.environmentRecall.length = (cycle + limit + 1) * width + slot := by
    rw [middleCursor, cursor]
    dsimp [offset]
    ring
  have aligned : ClockAligned runtime leaks packetBudget inputs 0 before := by
    refine ⟨valid.1, ?_⟩
    rw [cursor]
    have divided : cycle * width / width = cycle := by
      simpa only [Nat.add_zero] using cursor_div packetBudget cycle 0
        (cycleWidth_pos packetBudget)
    change before.application.current.native.clock = 0 + cycle * width / width
    rw [Nat.zero_add, divided]
    exact clock
  have middleClock := (clock_aligned_invariant runtime leaks packetBudget tape inputs 0).runRounds
    players offset before middle aligned prefixReached
  have atClock : middle.application.current.native.clock = cycle + limit + 1 := by
    rw [middleClock.2, cursorEq, cursor_div packetBudget _ slot slotBound, Nat.zero_add]
  have due : runtime.deadline coordinate.event ≤ middle.application.current.native.clock -
      (middle.application.current.native.activatedAt coordinate.event).getD
        middle.application.current.native.clock := by
    rw [middleActivated, Option.getD_some, atClock]
    have bound := deadline coordinate.event
    omega
  have strict := expiry_round_decreases runtime leaks packetBudget tape players
    (cycle + limit + 1) middle next inputs middleValid.1 owner coordinate middleRequest due
      cursorEq moved
  omega

end Vegas.EventGraphRuntime.ReservedEpoch
