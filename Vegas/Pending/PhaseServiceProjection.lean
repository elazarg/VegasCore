/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseServiceContract
import Vegas.Pending.PhaseNativeProjection

/-! # Primitive service guarantees after forgetting attempt tags

Opportunity forgets an extra witness. Protected inclusion also needs the factual
retention of the protected packet's attempt while its event remains unfinished.
Neither result asserts an all-history trace lift or a converse service contract.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (PhaseNativeProjection.nativeLeaks leaks plan)

/-- The actual phase activation witness supplies the original native witness
when its additional attempt equality is forgotten. -/
theorem OpportunityAt.nativeProjection (execution : (P).Execution) (delay : graph.EventId → Nat)
    (opportunity : OpportunityAt runtime leaks execution delay) :
    Vegas.EventGraphRuntime.OpportunityAt runtime (PhaseNativeProjection.nativeLeaks leaks plan)
      (PhaseNativeProjection.execution runtime leaks plan execution) delay := by
  intro event owner entered acting ready activated elapsed
  obtain ⟨entry, member, command, _attempt, entryReady, entryActivated⟩ :=
    opportunity event owner entered acting ready activated elapsed
  refine ⟨PhaseNativeProjection.environmentEntry runtime leaks plan entry,
    List.mem_map.mpr ⟨entry, member, rfl⟩, ?_, entryActivated, entryReady⟩
  change PhaseNativeProjection.command runtime leaks plan entry.command = .activate owner
  rw [command]
  rfl

/-- Native per-event sole-identifier protection follows from physical-coordinate
protection once the actual recorded packet retains its current attempt. The
coordinate premise concerns only that packet, not unrelated traffic. -/
theorem ProtectedInclusionAt.nativeProjection
    (execution : (P).Execution) (bound : graph.EventId → Nat)
    (inclusion : ProtectedInclusionAt runtime leaks execution bound)
    (retainedAttempt : ∀ (event : graph.EventId) (owner : Player),
      graph.actor? event = some owner →
      ∀ (earlier later : List (P).PlayerEntry) entry message,
      execution.recall owner = earlier ++ entry :: later →
      entry.emitted = some message → message.sender = owner →
      message.payload.packet.call.event? graph = some event →
      entry.beforeView.application.1.publicView.EventReady event →
      event ∉ execution.application.current.native.config.cut.completed →
      message.payload.attempt = execution.application.attempt) :
    Vegas.EventGraphRuntime.ProtectedInclusionAt runtime
      (PhaseNativeProjection.nativeLeaks leaks plan)
      (PhaseNativeProjection.execution runtime leaks plan execution) bound := by
  intro event owner acting earlier later entry message recalled sent sender named ready unique
    unfinished elapsed
  change (execution.recall owner).map (PhaseNativeProjection.playerEntry runtime leaks plan) =
    earlier ++ entry :: later at recalled
  obtain ⟨first, tail, split, firstEq, tailEq⟩ := List.map_eq_append_iff.mp recalled
  obtain ⟨original, rest, tailSplit, entryEq, restEq⟩ := List.map_eq_cons_iff.mp tailEq
  subst earlier
  subst entry
  subst later
  subst tail
  change original.emitted.map (Message.mapPayload CommitAttemptPacket.packet) = some message at sent
  obtain ⟨physical, physicalSent, rfl⟩ := Option.map_eq_some_iff.mp sent
  have currentAttempt := retainedAttempt event owner acting first rest original physical split
    physicalSent sender named ready unfinished
  apply inclusion ⟨physical.payload.attempt, event⟩ owner acting first rest original physical split
    physicalSent sender rfl named ready ?_ currentAttempt.symm unfinished elapsed
  intro other member duplicate
  have projectedMember : PhaseNativeProjection.playerEntry runtime leaks plan other ∈
      first.map (PhaseNativeProjection.playerEntry runtime leaks plan) ++
        rest.map (PhaseNativeProjection.playerEntry runtime leaks plan) := by
    rw [← List.map_append]
    exact List.mem_map.mpr ⟨other, member, rfl⟩
  apply unique (PhaseNativeProjection.playerEntry runtime leaks plan other) projectedMember
  obtain ⟨packet, emitted, author, _attempt, address, different⟩ := duplicate
  refine ⟨Message.mapPayload CommitAttemptPacket.packet packet, ?_, author, address, different⟩
  change other.emitted.map (Message.mapPayload CommitAttemptPacket.packet) = _
  rw [emitted]
  rfl

end Vegas.EventGraphRuntime.PhaseService
