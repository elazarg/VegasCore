/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochReceiptBatch
import Vegas.Pending.ReservedEpochEmissionTime
import Vegas.Pending.ReservedEpochClockAccounting
import Interaction.ReactiveAnchoredTrace
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveMonitoring
import Interaction.ReactiveServiceRounds

/-! # A clock bound for delivery of every raw submitted envelope -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem idle_emission_receipt {length : Nat} (cycles : Nat) (tape : Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (remaining : Nat) (execution : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (horizon (graph := graph) cycles)
        (family runtime leaks (submissionBudget (Player := Player) cycles) tape)).Trace
          (some ⟨remaining, none, execution⟩))
    (owner : Player) (entry : (app).PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (message : Message Player (app).Payload) (emitted : entry.emitted = some message)
    (elapsed : entry.beforeView.application.1.publicView.clock + (processingGap + 1) <
      execution.application.current.native.clock) :
    ∃ accepted, (message.id, accepted) ∈ execution.receipts := by
  let capacity := submissionBudget (Player := Player) cycles
  let width := cycleWidth (graph := graph) capacity
  let scheduler := family runtime leaks capacity tape
  let fallback : Player → (app).Policy := fun _ => (app).silentPolicy
  let players := (app).anchoredPolicy execution fallback
  let used := horizon (graph := graph) cycles - remaining
  obtain ⟨bounded, supported⟩ := ReactiveApplication.mem_roundsFrom_anchoredPolicy_of_trace
    (inputs.map (PhaseRuntimeState.initial plan)) (horizon (graph := graph) cycles)
      scheduler fallback trace
  change execution ∈ ((inputs.map (PhaseRuntimeState.initial plan)).bind fun state =>
    (app).runRounds scheduler players used
      (ReactiveApplication.Execution.initial app state)).support at supported
  obtain ⟨initial, initialized, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  rw [PMF.support_map] at initialized
  obtain ⟨draw, _drawSupported, rfl⟩ := initialized
  let start := ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan draw)
  have clock := clock_history runtime leaks capacity tape plan inputs
    (horizon (graph := graph) cycles) ⟨remaining, none, execution⟩ trace
  have recalled := (app).runRounds_environmentRecall_length scheduler players used start execution
    reached
  have recalledEq : execution.environmentRecall.length = used := by
    simpa only [start, ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add]
      using recalled
  have usedBound : used ≤ horizon (graph := graph) cycles := Nat.sub_le _ _
  have clockBound : execution.application.current.native.clock ≤ cycles := by
    rw [clock, recalledEq]
    have divided : used / width ≤ (cycles * width) / width :=
      Nat.div_le_div_right usedBound
    have endDiv : (cycles * width) / width = cycles := by
      simpa only [Nat.add_zero] using cursor_div capacity cycles 0 (cycleWidth_pos capacity)
    rw [endDiv] at divided
    exact divided
  let sent := entry.beforeView.application.1.publicView.clock
  have started : sent + 1 < cycles := by dsimp [sent]; omega
  obtain ⟨cycle, lower, upper, epoch⟩ := gaps.processing (sent + 1) started
  have cycleBefore : cycle < execution.application.current.native.clock := by
    dsimp [sent] at lower upper
    omega
  have room : cycle * width + capacity ≤ used := by
    have capacityBound : capacity < width := by dsimp [width, cycleWidth]; omega
    have scaled := Nat.mul_le_mul_right width (Nat.succ_le_of_lt cycleBefore)
    change (cycle + 1) * width ≤ execution.application.current.native.clock * width at scaled
    rw [clock, recalledEq] at scaled
    change (cycle + 1) * width ≤ (used / width) * width at scaled
    rw [Nat.add_mul, Nat.one_mul] at scaled
    have division := Nat.div_mul_le_self used width
    omega
  have splitCount : cycle * width + (used - cycle * width) = used := by omega
  have splitLaw := (app).runRounds_add scheduler players (cycle * width)
    (used - cycle * width) start
  rw [splitCount] at splitLaw
  rw [splitLaw] at reached
  obtain ⟨before, prefixReached, suffixReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have initialAligned : ClockAligned runtime leaks capacity draw 0 start := by
    refine ⟨(PhaseRuntimeState.initial_invariant plan draw).1, ?_⟩
    simpa only [start, ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_div,
      Nat.zero_add] using initial_clock plan draw
  have beforeAligned := (clock_aligned_invariant runtime leaks capacity tape draw 0).runRounds
    players (cycle * width) start before initialAligned prefixReached
  have beforeCursor : before.environmentRecall.length = cycle * width := by
    simpa only [start, ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add] using
      (app).runRounds_environmentRecall_length scheduler players (cycle * width) start before
        prefixReached
  have beforeClock : before.application.current.native.clock = cycle := by
    rw [beforeAligned.2, beforeCursor, Nat.zero_add]
    simpa only [Nat.add_zero] using cursor_div capacity cycle 0 (cycleWidth_pos capacity)
  have priorEntry := old_response_mem_before runtime leaks scheduler players
    (used - cycle * width) before execution suffixReached owner entry recorded (by
      rw [beforeClock]
      dsimp [sent] at lower
      omega)
  have prefixRounds : before ∈ ((app).roundsFrom
      (PMF.pure (PhaseRuntimeState.initial plan draw)) scheduler players
        (cycle * width)).support := by
    simpa only [ReactiveApplication.roundsFrom, PMF.pure_bind] using prefixReached
  obtain ⟨beforeTrace⟩ := (app).raw_trace_roundsFrom
    (PMF.pure (PhaseRuntimeState.initial plan draw)) (horizon (graph := graph) cycles) scheduler
      players (cycle * width) (by omega) before prefixRounds
  have inputRecall := (app).history_inputRecall (PMF.pure (PhaseRuntimeState.initial plan draw))
    (horizon (graph := graph) cycles) scheduler beforeTrace
  have input : message ∈ before.network.inputs := by
    have remembered : message ∈ (app).outputs (before.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, priorEntry, emitted⟩
    rw [← inputRecall owner] at remembered
    exact (List.mem_filter.mp remembered).1
  have restSplit : capacity + (used - cycle * width - capacity) = used - cycle * width := by omega
  have restLaw := (app).runRounds_add scheduler players capacity
    (used - cycle * width - capacity) before
  rw [restSplit] at restLaw
  rw [restLaw] at suffixReached
  obtain ⟨afterEpoch, processed, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ suffixReached)
  have covered := epoch_covers_submitted runtime leaks cycles tape
    (PMF.pure (PhaseRuntimeState.initial plan draw)) _ cycle before afterEpoch beforeTrace
      beforeCursor epoch players processed
  obtain ⟨accepted, receipted⟩ := (covered.2 message input).2
  exact ⟨accepted, ((app).receipt_policyInvariant players (message.id, accepted)).runRounds
    scheduler (used - cycle * width - capacity) afterEpoch execution receipted continued⟩

end Vegas.EventGraphRuntime.ReservedEpoch
