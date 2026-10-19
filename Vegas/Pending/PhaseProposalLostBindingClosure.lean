/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalLostBinding
import Vegas.Pending.PhaseAttemptReceiptSnapshot

/-! # Unaccepted fields in the original primitive closing result

The actual inclusion or environment witness precedes normalization. Its
accepted-table projection links a lost binding to every earlier owned callback.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The genuine primitive result retains every previously accepted handle,
even when its actual normalized endpoint has restored an older checkpoint. -/
theorem PhaseClosingEffect.accepted_preserved
    {before after : (app).Execution} {current : RecoveryState graph}
    (effect : PhaseClosingEffect runtime leaks before after current)
    (field : graph.Field) (candidate : Handle graph)
    (accepted : before.application.current.native.accepted field = some candidate) :
    current.native.accepted field = some candidate := by
  rcases effect with ⟨_id, message, native, _found, _reached, handled, rfl⟩ |
    ⟨command, native, _reached, supported, rfl⟩
  · change native.accepted field = some candidate
    exact handle_preserves_accepted runtime before.application.current.native native
      ⟨message.id, message.payload.packet.call⟩ handled field candidate accepted
  · change native.accepted field = some candidate
    rw [(environmentStep_tables runtime before.application.current.native native command
      supported).1]
    exact accepted

/-- A missing original closing handle was also absent immediately before the
primitive command. This is not inferred from the restored live table. -/
theorem PhaseClosingEffect.unaccepted_before
    {before after : (app).Execution} {current : RecoveryState graph}
    (effect : PhaseClosingEffect runtime leaks before after current)
    (field : graph.Field) (unaccepted : current.native.accepted field = none) :
    before.application.current.native.accepted field = none := by
  cases selected : before.application.current.native.accepted field with
  | none => rfl
  | some candidate =>
      have retained := effect.accepted_preserved runtime leaks field candidate selected
      rw [unaccepted] at retained
      cases retained

/-- Use the original drained snapshot to route omission backwards through the
actual primitive closing command, preserving inherited exclusions. -/
theorem PhaseClosingEffect.unaccepted_before_of_drain
    {before after : (app).Execution} {current : RecoveryState graph}
    (effect : PhaseClosingEffect runtime leaks before after current)
    (phase : RuntimePhase graph) (field : graph.Field)
    (unaccepted : (phase.drain current).native.accepted field = none) :
    before.application.current.native.accepted field = none := by
  apply effect.unaccepted_before runtime leaks field
  rwa [(phase.drain_tables current).1] at unaccepted

section Counted

variable [Fintype Player] (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- A genuine original closing omission rules out every retained later owned
ready callback in that attempt. No equality with the post-reset live store is
required, and the initializer and original trace remain literal. -/
theorem phase_closing_unaccepted_no_later_owned_request
    (scheduler : (app).Scheduler) (ordered : graph.RevealRelaxedOrdered)
    (before closing : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some closing))
    (kept : TracePrefix prior trace)
    (same : before.execution.application.attempt = closing.execution.application.attempt)
    (after : (app).Execution) (current : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution after current)
    (phase : RuntimePhase graph)
    (installed : before.execution.application.phases.head? = some phase)
    (owner : Player) (earlier event : graph.EventId) (priorPayload payload : L.Ty)
    (priorBinding : graph.outputLayout earlier = .binding owner priorPayload)
    (binding : graph.outputLayout event = .binding owner payload)
    (inside : earlier ∈ phase.events)
    (unaccepted : (phase.drain current).native.accepted (.inr earlier) = none)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, event⟩) : ¬ earlier.val < event.val := by
  have absent := effect.unaccepted_before_of_drain runtime leaks phase (.inr earlier) unaccepted
  exact phase_unaccepted_no_later_owned_request runtime leaks bounds plan inputs horizon scheduler
    ordered before closing prior trace kept same phase installed owner earlier event priorPayload
      payload priorBinding binding inside absent request

end Counted

end Vegas.EventGraphRuntime
