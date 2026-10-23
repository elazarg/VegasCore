/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalAcceptedHistory
import Vegas.Pending.PhaseStoredCheckpoint

/-! # Actual execution frames for proposal replay through normalization -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A transient application image is compared with its genuine external
execution. Only the first installed phase needs exact entry/generation data;
later automatic intervals are strictly future phases of the same envelope frame.
No intermediate counted execution or source archive equality is part of this frame. -/
structure NormalizationFrame (anchor : (app).Control) (state : PhaseRuntimeState graph) : Prop where
  lower : anchor.execution.application.attempt.phase ≤ state.attempt.phase
  savedOrigins : OpeningOrigins anchor.execution.network.inputs state.entry.native
  currentOrigins : OpeningOrigins anchor.execution.network.inputs state.current.native
  current : state.attempt.phase = anchor.execution.application.attempt.phase →
    state.phases = anchor.execution.application.phases ∧
      state.generation = anchor.execution.application.generation ∧
      state.entry = anchor.execution.application.entry ∧
      KeepsStore anchor.execution.application.current.native state.current.native

variable {runtime leaks}

/-- Draining automatic instructions keeps every submitted-packet origin and
all previously installed cells; it does not create an external callback. -/
theorem NormalizationFrame.drain {anchor : (app).Control} {state : PhaseRuntimeState graph}
    (frame : NormalizationFrame runtime leaks anchor state) (phase : RuntimePhase graph) :
    NormalizationFrame runtime leaks anchor
      {state with current := phase.drain state.current} := by
  refine ⟨frame.lower, frame.savedOrigins, frame.currentOrigins.drain state.current.excluded phase,
    ?_⟩
  intro same
  obtain ⟨phases, generation, entry, kept⟩ := frame.current same
  exact ⟨phases, generation, entry, fun field value present =>
    phase.drain_keepsStore state.current field value (kept field value present)⟩

/-- After advancing to a strictly future interval, retained origin evidence
suffices. No participant could have submitted a counted packet there yet. -/
theorem NormalizationFrame.future (anchor : (app).Control) (state : PhaseRuntimeState graph)
    (future : anchor.execution.application.attempt.phase < state.attempt.phase)
    (saved : OpeningOrigins anchor.execution.network.inputs state.entry.native)
    (current : OpeningOrigins anchor.execution.network.inputs state.current.native) :
    NormalizationFrame runtime leaks anchor state := by
  refine ⟨future.le, saved, current, ?_⟩
  intro equal
  omega

end Vegas.EventGraphRuntime.PhaseProposal
