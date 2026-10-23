/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ReservedEpochStoppedWord

/-! # Complete failure footprints of the original resolved commitment image -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The real primitive underlying a closing image preserves every already
completed public failure verdict before any normalization or retry. -/
theorem phaseClosingEffect_publicFailureExtension (before after : (app).Execution)
    (raw : RecoveryState graph) (effect : PhaseClosingEffect runtime leaks before after raw) :
    before.application.current.native.PublicFailureExtension raw.native := by
  rcases effect with included | applied
  · obtain ⟨id, message, native, _found, _stepped, handled, rfl⟩ := included
    exact (completionStep_handle runtime before.application.current.native native
      ⟨message.id, message.payload.packet.call⟩ handled).publicFailureExtension
  · obtain ⟨command, native, _stepped, moved, rfl⟩ := applied
    exact (completionStep_environmentStep runtime before.application.current.native native command
      moved).publicFailureExtension

/-- The ORIGINAL drained commitment image has the saved old failure prefix,
its actual accepted-handle complement inside this phase, and no failures at
later ranks. The normalized endpoint is deliberately absent from the readout. -/
theorem original_binding_publicFailure_iff (ordered : graph.RevealRelaxedOrdered)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (before : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some before))
    (after : (app).Execution) (raw : RecoveryState graph)
    (changed : after.application.attempt ≠ before.execution.application.attempt)
    (effect : PhaseClosingEffect runtime leaks before.execution after raw)
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (finished : phase.Finished (phase.drain raw))
    (event : graph.EventId) :
    (phase.drain raw).native.PublicFailure event ↔
      if event.val < phase.low then before.execution.application.entry.native.PublicFailure event
      else if event.val < phase.high then raw.native.accepted (.inr event) = none else False := by
  classical
  have record := closing_receipt_record runtime leaks ordered plan inputs horizon scheduler before
    trace after raw changed effect
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have positioned := record.exclusion.frontier.positioned
  change PhaseRuntimeState.Positioned before.execution.application.phases
    before.execution.application.entry raw at positioned
  rw [phases] at positioned
  change before.execution.application.entry.native.config.cut.IsPrefix phase.low ∧
    raw.native.config.cut.Within phase.low phase.high at positioned
  have checkpoint := phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon
    scheduler trace
  change before.execution.application.entry.native.PublicFailureExtension
    before.execution.application.current.native at checkpoint
  have preserved := (checkpoint.trans
    (phaseClosingEffect_publicFailureExtension runtime leaks before.execution after raw
      effect)).trans
      (phase.drain_publicFailureExtension raw)
  by_cases earlier : event.val < phase.low
  · simp only [earlier, ↓reduceIte]
    exact preserved.failures event ((positioned.1.2 event).mpr earlier)
  · by_cases inside : event.val < phase.high
    · simp only [earlier, inside, ↓reduceIte]
      have member := (phase.mem_events event).mpr ⟨by omega, inside⟩
      obtain ⟨owner, payload, binding⟩ := commitment ▸ phase.fields event (by omega) inside
      rw [State.publicFailure_iff_accepted_none (phase.drain raw).native event owner payload binding
        (finished member), (phase.drain_tables raw).1]
    · simp only [earlier, inside, ↓reduceIte, iff_false]
      intro failed
      have completed := failed.completed
      have completedPrefix := phase.finished_prefix (phase.drain raw)
        (phase.drain_within raw positioned.2) finished
      have rank := (completedPrefix.2 event).mp completed
      omega


end Vegas.EventGraphRuntime.ReservedEpoch
