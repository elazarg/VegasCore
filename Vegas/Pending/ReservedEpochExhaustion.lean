/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochGeometry

/-! # A noncircular cycle bound completes every raw execution -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem intervals_work_bound {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) (limit : Nat)
    (deadline : ∀ event, runtime.deadline event ≤ limit) (blocks cycle : Nat)
    (before after : (app).Execution) (geometry : ProgressGeometry inputs before.application)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget)
    (clock : before.application.current.native.clock = cycle)
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      (blocks * (limit + 2) * cycleWidth (graph := graph) packetBudget) before).support)
    (nonempty : after.application.phases ≠ []) :
    workRemaining after.application + blocks ≤ workRemaining before.application := by
  induction blocks generalizing cycle before after with
  | zero =>
      simp only [Nat.zero_mul, ReactiveApplication.runRounds, PMF.mem_support_pure_iff] at reached
      subst after
      omega
  | succ blocks ih =>
      let width := cycleWidth (graph := graph) packetBudget
      let duration := (limit + 2) * width
      have splitCount : (blocks + 1) * (limit + 2) * width =
          duration + blocks * (limit + 2) * width := by dsimp [duration]; ring
      change after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
        ((blocks + 1) * (limit + 2) * width) before).support at reached
      rw [splitCount, (app).runRounds_add] at reached
      obtain ⟨middle, prefixReached, suffixReached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have middleGeometry := ((progress_geometry_invariant runtime leaks ordered
        inputs).policyInvariant app players).runRounds (family runtime leaks packetBudget tape)
          duration before middle geometry prefixReached
      have middleNonempty := runRounds_nonempty_before runtime leaks
        (family runtime leaks packetBudget tape) players (blocks * (limit + 2) * width)
          middle after middleGeometry.valid.2.1 suffixReached nonempty
      have beforeNonempty := runRounds_nonempty_before runtime leaks
        (family runtime leaks packetBudget tape) players duration before middle
          geometry.valid.2.1 prefixReached middleNonempty
      have strict := nonterminal_interval_decreases runtime leaks packetBudget tape players
        ordered inputs cycle limit deadline before middle geometry.valid geometry.frontier
          geometry.live geometry.quiescent cursor clock beforeNonempty prefixReached
      have middleCursor := (app).runRounds_environmentRecall_length
        (family runtime leaks packetBudget tape) players duration before middle prefixReached
      have nextCursor : middle.environmentRecall.length = (cycle + limit + 2) * width := by
        rw [middleCursor, cursor]
        dsimp [duration]
        ring
      have initialAligned : ClockAligned runtime leaks packetBudget inputs 0 before := by
        refine ⟨geometry.valid.1, ?_⟩
        rw [cursor]
        have divided : cycle * width / width = cycle := by
          simpa only [Nat.add_zero] using cursor_div packetBudget cycle 0
            (cycleWidth_pos packetBudget)
        change before.application.current.native.clock = 0 + cycle * width / width
        rw [Nat.zero_add, divided]
        exact clock
      have middleAligned := (clock_aligned_invariant runtime leaks packetBudget tape
        inputs 0).runRounds players duration before middle initialAligned prefixReached
      have nextClock : middle.application.current.native.clock = cycle + limit + 2 := by
        rw [middleAligned.2, nextCursor]
        have divided : (cycle + limit + 2) * width / width = cycle + limit + 2 := by
          simpa only [Nat.add_zero] using cursor_div packetBudget (cycle + limit + 2) 0
            (cycleWidth_pos packetBudget)
        change 0 + (cycle + limit + 2) * width / width = cycle + limit + 2
        rw [Nat.zero_add, divided]
      have bound := ih (cycle + limit + 2) middle after middleGeometry nextCursor nextClock
        suffixReached nonempty
      omega

def maximumDeadline : Nat := Finset.univ.sup runtime.deadline

def completionCycles : Nat := (workBound graph + 1) * (maximumDeadline runtime + 2)

/-- The number of cycles depends on logical events, players and deadlines only.
Packet padding, candidate supply, player policies and the joint tape do not enter it. -/
theorem runRounds_complete {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : RuntimePhase.PartitionRegular plan.phases)
    (players : Player → (app).Policy) (inputs : graph.Inputs) (final : (app).Execution)
    (reached : final ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      (completionCycles runtime * cycleWidth (graph := graph) packetBudget)
        (ReactiveApplication.Execution.initial app
          (PhaseRuntimeState.initial plan inputs))).support) :
    final.application.phases = [] ∧ final.application.current.native.config.cut.completed =
      Finset.univ := by
  let before := ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan inputs)
  have initialGeometry := initial_progress_geometry plan ordered maximal inputs
  have finished : final.application.phases = [] := by
    by_contra unfinished
    have bound := intervals_work_bound runtime leaks packetBudget tape players ordered inputs
      (maximumDeadline runtime) (fun event => Finset.le_sup (Finset.mem_univ event))
      (workBound graph + 1) 0 before final initialGeometry (by
        simp only [before, ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_mul])
      (initial_clock plan inputs) reached unfinished
    have upper := workRemaining_le_bound before.application
    omega
  have finalGeometry := ((progress_geometry_invariant runtime leaks ordered inputs).policyInvariant
    app players).runRounds (family runtime leaks packetBudget tape) _ before final initialGeometry
      reached
  exact ⟨finished, finalGeometry.frontier.terminal finished⟩

end Vegas.EventGraphRuntime.ReservedEpoch
