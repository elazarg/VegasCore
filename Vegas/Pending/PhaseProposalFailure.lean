/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalRetention
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseSavedExclusionReadback

/-! # Submitted openings cannot be suppressed by source-earlier failures -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
theorem publication_failure_kept {before after : EventGraphRuntime.State graph}
    (kept : KeepsStore before after) (event : graph.EventId) (payload : L.Ty)
    (publication : graph.outputLayout event = .publication payload)
    (completed : event ∈ before.config.cut.completed) :
    after.PublicFailure event ↔ before.PublicFailure event := by
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
    ((before.config.output_available event).mpr completed)
  have retained : after.config.outputs event = some value := kept (.inr event) value stored
  have output := retained.trans stored.symm
  simp only [State.PublicFailure, PublicView.missedBinding, publication,
    Bool.false_eq_true, false_or]
  unfold RecoveryState.publicationFailed
  cases nodeView graph event <;> simp only [output]

variable [Fintype Player] (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Readiness orders earlier events of the SAME owner. Hence an actually
submitted opening is not removed by the source-order exclusion scan, even if
another owner's independent opening was physically processed first. -/
theorem submitted_proposal_owner_not_in_scan
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase graph) (kind : phase.kind = .reveal)
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw))
    (sameAttempt : coordinate.attempt = current.execution.application.attempt)
    (inside : coordinate.event ∈ phase.events)
    (saved : current.execution.application.entry.native.config.cut.IsPrefix phase.low)
    (image : EventGraphRuntime.State graph)
    (kept : KeepsStore current.execution.application.current.native image)
    (failures : current.execution.application.entry.native.PublicFailureExtension image) :
    message.sender ∉ current.execution.application.entry.excluded ∪
      image.failureOwnersBefore coordinate.event.val := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state support
    obtain ⟨input, _support, rfl⟩ := PMF.support_map .. ▸ support
    exact PhaseRuntimeState.initial_ordered plan input
  obtain ⟨before, prior, material, candidate, retained, _active, request, _call, _offered,
    _stamp⟩ := submitted_proposal_callback runtime leaks bounds plan ordered inputs horizon
      scheduler current trace message submitted coordinate raw proposed
  have rawPrior := menu.toRawTrace initial horizon scheduler prior
  have rawTrace := menu.toRawTrace initial horizon scheduler trace
  have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized rawPrior
  have same := request.1.symm.trans sameAttempt
  have entryEq := (phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
    scheduler before current prior trace retained firstOrdered).2.2 same
  have firstCoverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    rawPrior
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler rawTrace
  have entrySafe : message.sender ∉ current.execution.application.entry.excluded := by
    intro excluded
    apply request.2.2.2.2
    exact firstCoverage.inherited (entryEq.symm ▸ excluded)
  intro excluded
  rcases Finset.mem_union.mp excluded with inherited | scanned
  · exact entrySafe inherited
  · obtain ⟨earlier, lower, actor, failed⟩ := (Finset.mem_filter.mp scanned).2
    by_cases old : earlier.val < phase.low
    · have completed := (saved.2 earlier).mpr old
      exact entrySafe (coverage.saved.covered earlier message.sender actor
        ((failures.failures earlier completed).mp failed))
    · have interval := (phase.mem_events coordinate.event).mp inside
      have publication := phase.fields earlier (by omega) (by omega)
      rw [kind] at publication
      obtain ⟨payload, publication⟩ := publication
      obtain ⟨completed, safe⟩ := requested_earlier_own_completed_not_failed runtime leaks plan
        ordered inputs horizon scheduler before rawPrior message.sender coordinate request
        earlier actor lower
      have prefixKeep := same_attempt_prefix_keeps_store runtime leaks menu initial initialized
        horizon scheduler before current prior trace retained same
      have allKept : KeepsStore before.execution.application.current.native image :=
        fun field value stored => kept field value (prefixKeep field value stored)
      exact safe
        ((publication_failure_kept allKept earlier payload publication completed).mp failed)

end Vegas.EventGraphRuntime.PhaseProposal
