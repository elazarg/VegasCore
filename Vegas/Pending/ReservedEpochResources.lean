/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochCompletion
import Vegas.Pending.PhaseCandidateSupply

/-! # Traffic and candidate reserves chosen after semantic exhaustion -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] in
theorem completionCycles_pos : 0 < completionCycles runtime := by
  unfold completionCycles
  positivity

omit [DecidableEq Player] in
theorem executionHorizon_pos : 0 < executionHorizon runtime := by
  exact Nat.mul_pos (completionCycles_pos runtime) (cycleWidth_pos _)

theorem actual_traffic_bound {length : Nat} (tape : Tape Player length)
    (initial : PMF (app).State) (current : (app).Control)
    (trace : ((app).protocol initial (executionHorizon runtime)
      (family runtime leaks (packetCapacity runtime) tape)).Trace (some current)) :
    current.execution.network.inputs.length ≤ packetCapacity runtime :=
  inputs_le_cycles runtime leaks (packetCapacity runtime) tape initial (completionCycles runtime)
    current trace

/-- A reserve at least as large as the proved physical horizon supplies a fresh
candidate even after arbitrary raw preparations and semantic retries. -/
theorem active_fresh_candidate (bounds : MessageBounds graph)
    (capacity : executionHorizon runtime ≤ bounds.candidateCount)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (scheduler : (app).Scheduler)
    (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime) scheduler).Trace (some current))
    (owner : Player) (active : current.actor = some owner) :
    ∃ serial, serial < bounds.candidateCount ∧ reactiveFreshSlot
      (current.execution.observe app owner).application.1 = some serial := by
  obtain ⟨serial, bounded, selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon runtime leaks
    plan inputs (executionHorizon runtime) scheduler current trace owner active
  exact ⟨serial, bounded.trans_le capacity, selected⟩

end Vegas.EventGraphRuntime.ReservedEpoch
