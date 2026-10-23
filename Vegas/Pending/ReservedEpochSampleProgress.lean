/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochResolution
import Vegas.Pending.PhaseSampleProgress

/-! # A ready source sample consumes work at the reserved sample slot -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

include leaks in
theorem sample_work_decreases {inputs : graph.Inputs} (before after : PhaseRuntimeState graph)
    (valid : WorkValid inputs before) (frontier : before.Frontier) (phase : RuntimePhase graph)
    (head : before.phases.head? = some phase) (kind : phase.kind = .sample)
    (event : graph.EventId) (atLow : event.val = phase.low)
    (ready : before.current.native.config.cut.Ready event) (chance : graph.actor? event = none)
    (reached : after ∈ (before.environment runtime (.executeSample event)).support) :
    workRemaining after < workRemaining before := by
  have progress := (phaseApplication_namespace_progress runtime leaks).environment
    before (.executeSample event) after reached valid.2.1
  have budget := (phaseApplication_seedBudget runtime leaks).environment
    before (.executeSample event) after valid.2.2 reached
  have strict := before.sample_advances_phase runtime after frontier phase head kind event atLow
    ready chance reached
  have different : before.attempt ≠ after.attempt := by
    intro same
    have equal := congrArg CommitAttemptId.phase same
    omega
  exact work_decreases_of_namespace before after progress.2 progress.1
    (PhaseRuntimeState.phaseLow_le_count after.phases) budget.generation_le_card different
theorem sample_at {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (cycle : Nat) (execution : (app).Execution) (phase : RuntimePhase graph)
    (head : execution.application.phases.head? = some phase) (kind : phase.kind = .sample)
    (event : graph.EventId) (atLow : event.val = phase.low) :
    command runtime leaks packetBudget tape
      (cycle * cycleWidth (graph := graph) packetBudget +
        (packetBudget + Fintype.card Player)) (execution.observeEnvironment app) =
          .application (.executeSample event) := by
  let slot := packetBudget + Fintype.card Player
  have bounded : slot < cycleWidth (graph := graph) packetBudget := by
    dsimp [slot, cycleWidth]
    omega
  have notProcessing : ¬ slot < packetBudget := by dsimp [slot]; omega
  have notOwner : ¬ slot - packetBudget < Fintype.card Player := by dsimp [slot]; omega
  have lowBound : phase.low < graph.order.eventCount := by rw [← atLow]; exact event.isLt
  change command runtime leaks packetBudget tape
    (cycle * cycleWidth (graph := graph) packetBudget + slot) _ = _
  simp only [command, cursor_mod _ _ _ bounded, notProcessing, ↓reduceIte, notOwner,
    ↓reduceDIte, slot, ↓reduceIte, sample, ReactiveApplication.Execution.observeEnvironment,
    phaseApplication, PhaseRuntimeState.publicView, head, Option.map_some, kind,
    lowBound, ↓reduceDIte]
  congr 3
  exact atLow.symm

theorem sample_round_decreases {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy) (cycle : Nat)
    (before after : (app).Execution) (inputs : graph.Inputs)
    (valid : WorkValid inputs before.application) (frontier : before.application.Frontier)
    (phase : RuntimePhase graph)
    (head : before.application.phases.head? = some phase) (kind : phase.kind = .sample)
    (event : graph.EventId) (atLow : event.val = phase.low)
    (ready : before.application.current.native.config.cut.Ready event)
    (chance : graph.actor? event = none)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget + (packetBudget + Fintype.card Player))
    (reached : after ∈ ((app).round (family runtime leaks packetBudget tape)
      players before).support) :
    workRemaining after.application < workRemaining before.application := by
  have selected := sample_at runtime leaks packetBudget tape cycle before phase head kind
    event atLow
  rw [← cursor] at selected
  obtain ⟨chosen, offered, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have chosenEq := (family_support runtime leaks packetBudget tape before.environmentRecall
    (before.observeEnvironment app) chosen).mp offered
  rw [chosenEq, selected] at dispatched
  obtain ⟨middle, observed, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  change after ∈ (PMF.pure middle).support at continued
  have afterEq : after = middle := (PMF.mem_support_pure_iff _ _).mp continued
  subst after
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at observed
  rw [PMF.support_map] at observed
  obtain ⟨state, moved, rfl⟩ := observed
  exact sample_work_decreases runtime leaks before.application state valid frontier phase head kind
    event atLow ready chance moved

end Vegas.EventGraphRuntime.ReservedEpoch
