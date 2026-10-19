/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptControls
import Vegas.Pending.PhaseRetiredCompletion
import Vegas.Pending.PhaseResolution

/-! # Actual retry transitions retain the completed event of each survivor -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- If normalization changes generation while an owner survives, its event
is recorded as completed in the exact old attempt before rollback. -/
theorem normalize_retry_survivor_record (state : PhaseRuntimeState graph)
    (active : state.current.FailureCoverage)
    (phase : RuntimePhase graph) (installed : phase ∈ state.phases.head?)
    (event : graph.EventId) (inside : event ∈ phase.events) (owner : Player)
    (acting : graph.actor? event = some owner)
    (surviving : owner ∉ state.normalize.current.excluded)
    (changed : state.normalize.generation ≠ state.generation) :
    ∃ record ∈ state.normalize.retired, record.attempt = state.attempt ∧
      event ∈ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
        ¬ record.state.PublicFailure event := by
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have physical := (settle_physical state.phases state.generation state.entry state.current
    state.retired).1
  have survives : owner ∉ state.current.excluded := by
    simpa only [normalize, physical] using surviving
  have result := settle_retry_survivor_record phase remaining state.generation state.entry
    state.current state.retired event inside owner acting survives active
  simpa only [normalize, phases, attempt, List.head?_cons, Option.map_some, Option.getD_some]
    using result (by simpa only [normalize, phases] using changed)

end PhaseRuntimeState

/-- Every actual operation that changes generation records the surviving
owner's current event as completed and nonfailed in the old attempt. -/
theorem phaseApplication_retryCompletion (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      before.current.FailureCoverage → ∀ phase ∈ before.phases.head?,
        ∀ event ∈ phase.events, ∀ owner, graph.actor? event = some owner →
          owner ∉ after.current.excluded → after.generation ≠ before.generation →
          ∃ record ∈ after.retired, record.attempt = before.attempt ∧
            event ∈ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
              ¬ record.state.PublicFailure event) where
  refl _ _ _ _ _ _ _ _ _ changed := (changed rfl).elim
  submit _ _ _ _ _ _ _ _ _ _ _ changed := (changed rfl).elim
  handle state message next accepted active phase installed event inside owner acting surviving
      changed := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.normalize_retry_survivor_record
        { state with current := state.current.inclusionResult message.payload.packet.call native }
        (active.inclusionResult runtime _ native handled) phase installed event inside owner
        acting surviving changed
    · cases accepted
  environment state command next reached active phase installed event inside owner acting surviving
      changed := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact PhaseRuntimeState.normalize_retry_survivor_record
        { state with current := state.current.environmentResult command native }
        (active.environmentResult runtime command native supported) phase installed event inside
        owner acting surviving changed
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (changed rfl).elim

end Vegas.EventGraphRuntime
