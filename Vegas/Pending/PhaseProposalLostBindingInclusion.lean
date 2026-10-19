/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalLostBindingClosure
import Vegas.Pending.PhaseProposalShadowRejectedTrace

/-! # Actual rejected processing of a binding omitted at closure

An original omitted association rules out successful processing at any
retained include step of that attempt. The counterpart rejection follows
from public admission gates, independently of the private prepared value.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Successful binding processing installs its literal handle in the live
association table when the normalized result retains the same attempt. -/
theorem phase_handle_binding_accepted_of_same_attempt
    (before after : PhaseRuntimeState graph) (ordered : before.Ordered)
    (message : Message Player (CommitAttemptPacket graph))
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (handled : before.handle runtime message = some after)
    (same : before.attempt = after.attempt) :
    after.current.native.accepted (.inr event) = some candidate := by
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · obtain ⟨native, accepted, rfl⟩ := Option.map_eq_some_iff.mp handled
    have table := (handle_commitment_tables runtime before.current.native native message.id event
      candidate (by simpa only [call] using accepted)).2.1
    have present : native.accepted (.inr event) = some candidate := by
      rw [table, Function.update_self]
    exact PhaseRuntimeState.normalize_preserves_accepted
      ({ before with current := before.current.inclusionResult message.payload.packet.call native }
        : PhaseRuntimeState graph) ordered same (.inr event) candidate present
  · cases handled


/-- At the namespace-changing INCLUDE itself, the original raw native result
would record the named handle before any restore. An omitted original
snapshot therefore rules out that call, even though the normalized successor
may have discarded unrelated accepted associations. -/
theorem phase_closing_inclusion_call_ne_of_omission
    (before : RecoveryState graph)
    (message : Message Player (CommitAttemptPacket graph)) (native : State graph)
    (handled : handle runtime before.native
      ⟨message.id, message.payload.packet.call⟩ = some native)
    (phase : RuntimePhase graph) (event : graph.EventId) (candidate : Handle graph)
    (unaccepted : (phase.drain
      (before.inclusionResult message.payload.packet.call native)).native.accepted
        (.inr event) = none) :
    message.payload.packet.call ≠ .commitment event candidate := by
  intro call
  have table := (handle_commitment_tables runtime before.native native message.id event candidate
    (by simpa only [call] using handled)).2.1
  rw [(phase.drain_tables (before.inclusionResult message.payload.packet.call native)).1]
    at unaccepted
  change native.accepted (.inr event) = none at unaccepted
  rw [table, Function.update_self] at unaccepted
  cases unaccepted

section Counted

variable [Fintype Player] (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- Every real include of the eventually omitted binding rejects. Both the
include suffix and the later original closing witness are actual counted
trace data; no counterpart handler outcome is supplied. -/
theorem phase_lost_binding_include_rejected
    (scheduler : (app).Scheduler) (remaining : Nat)
    (before : (app).Execution)
    (beforeTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, before⟩))
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : before.network.lookup id = some message)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (closing : (app).Control)
    (closingTrace : ((menu).protocol initial horizon scheduler).Trace (some closing))
    (includedTrace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, { before.includePending app id with
        environmentRecall := before.environmentRecall ++
          [⟨before.observeEnvironment app, .include id⟩] }⟩))
    (retained : TracePrefix includedTrace closingTrace)
    (sameBefore : before.application.attempt = closing.execution.application.attempt)
    (sameIncluded : (before.includePending app id).application.attempt =
      closing.execution.application.attempt)
    (after : (app).Execution) (current : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution after current)
    (phase : RuntimePhase graph)
    (unaccepted : (phase.drain current).native.accepted (.inr event) = none) :
    before.application.handle runtime message = none := by
  have absent := effect.unaccepted_before_of_drain runtime leaks phase (.inr event) unaccepted
  cases handled : before.application.handle runtime message with
  | none => rfl
  | some image =>
      let included : (app).Execution := { before.includePending app id with
        environmentRecall := before.environmentRecall ++
          [⟨before.observeEnvironment app, .include id⟩] }
      have application : included.application = image := by
        simp only [included, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found,
          show (app).handle before.application message = some image from handled,
          Option.getD_some]
      have initialized : ∀ state ∈ (initial).support, state.Ordered := by
        intro state member
        obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
        exact PhaseRuntimeState.initial_ordered plan draw
      have beforeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
        scheduler initialized ((menu).toRawTrace initial horizon scheduler beforeTrace)
      have sameImage : before.application.attempt = image.attempt := by
        rw [← application]
        exact sameBefore.trans sameIncluded.symm
      have installed := phase_handle_binding_accepted_of_same_attempt runtime before.application
        image beforeOrdered message event candidate call handled sameImage
      have includedOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
        scheduler initialized ((menu).toRawTrace initial horizon scheduler includedTrace)
      have present : included.application.current.native.accepted (.inr event) =
          some candidate := by rw [application]; exact installed
      have kept := phase_prefix_accepted runtime leaks menu initial horizon scheduler
        ⟨remaining, none, included⟩ closing includedTrace closingTrace retained includedOrdered
          sameIncluded (.inr event) candidate present
      rw [absent] at kept
      cases kept

end Counted

end Vegas.EventGraphRuntime
