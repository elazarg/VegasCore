/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceContract
import Vegas.Pending.PhaseNativeTrace
import Vegas.Pending.ReactiveEventStability

/-! # Actual physical service contracts at clear native prefixes -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- Erasing an actual same-attempt activation retains its original readiness
stamp and recorded native view. No scheduler is reconstructed globally. -/
theorem opportunityAt_projection (current : (P).Execution) (delay : graph.EventId → Nat)
    (service : PhaseService.OpportunityAt runtime leaks current delay) :
    OpportunityAt runtime (nativeLeaks leaks plan)
      (execution runtime leaks plan current) delay := by
  intro event owner entered owned ready stamp passed
  obtain ⟨entry, member, activated, _sameAttempt, wasReady, wasStamp⟩ :=
    service event owner entered owned ready stamp passed
  refine ⟨environmentEntry runtime leaks plan entry, List.mem_map.mpr ⟨entry, member, rfl⟩,
    ?_, wasStamp, wasReady⟩
  change command runtime leaks plan entry.command = .activate owner
  rw [activated]
  rfl

private theorem attempt_of_ready [Fintype Player] (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (event : graph.EventId) (ready : current.execution.application.current.native.config.cut.Ready
      event) : current.execution.application.attempt = ⟨plan.eventPhase event, 0⟩ := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have frontier := (phaseApplication_live runtime leaks).history _ horizon scheduler
    (fun initial supported => by
      obtain ⟨input, _support, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_frontier plan input,
        PhaseRuntimeState.initial_live plan input⟩) raw
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler raw
  have geometry := phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler raw
  obtain ⟨phase, head, inside⟩ := current.execution.application.ready_current_phase ordered
    frontier.1 frontier.2 geometry.2.2 event ready
  change current.execution.application.phases.head? = some phase at head
  have member : phase ∈ plan.phases := suffix.subset (List.mem_of_mem_head? head)
  have static := plan.eventPhase_of_mem phase member event inside
  have generation := (phase_clear_history runtime leaks plan inputs horizon scheduler current
    raw clear).1
  simp only [PhaseRuntimeState.attempt, head, Option.map_some, Option.getD_some, generation,
    static]

/-- At an actual clear counted prefix, the attempt-aware sole-packet guarantee
implies the original native condition. All emitted records and receipts remain
those of the actual physical history. -/
theorem protectedInclusionAt_projection [Fintype Player] (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (bound : graph.EventId → Nat)
    (service : PhaseService.ProtectedInclusionAt runtime leaks current.execution bound) :
    ProtectedInclusionAt runtime (nativeLeaks leaks plan)
      (execution runtime leaks plan current.execution) bound := by
  intro event owner owned earlier later entry message split emitted authored named wasReady sole
    unfinished passed
  change (current.execution.recall owner).map (playerEntry runtime leaks plan) =
    earlier ++ entry :: later at split
  obtain ⟨first, tail, recallEq, firstEq, tailEq⟩ := List.map_eq_append_iff.mp split
  obtain ⟨original, rest, tailEq', originalEq, restEq⟩ := List.map_eq_cons_iff.mp tailEq
  subst tail
  subst earlier
  subst entry
  subst later
  obtain ⟨packet, packetEmitted, packetEq⟩ := Option.map_eq_some_iff.mp emitted
  subst message
  change packet.payload.packet.call.event? graph = some event at named
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have member : original ∈ current.execution.recall owner := by
    rw [recallEq]
    exact List.mem_append_right _ List.mem_cons_self
  have recalled := PhaseCount.countRecall_history runtime leaks raw
  have output : packet ∈ (P).outputs (current.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨original, member, packetEmitted⟩
  rw [← recalled.1 owner] at output
  have authentic := (List.mem_filter.mp output).1
  have nativeTrace := nativeTrace runtime leaks plan bounds ordered maximal inputs horizon scheduler
    trace (fun _ same => by cases same; exact clear)
  have stable := entryEventStable_history runtime (nativeLeaks leaks plan)
    (inputs.map State.initial) horizon (nativeScheduler runtime leaks plan scheduler) nativeTrace
  have nativeMember : playerEntry runtime leaks plan original ∈
      (execution runtime leaks plan current.execution).recall owner :=
    List.mem_map.mpr ⟨original, member, rfl⟩
  obtain ⟨extra, order, _⟩ := stable owner _ nativeMember event wasReady unfinished
  have ready := ready_of_eventReady_extends order wasReady unfinished
  have currentAttempt := attempt_of_ready runtime leaks plan bounds ordered maximal inputs horizon
    scheduler trace clear event ready
  have recovered := PhaseCount.stamp_nativeMessage_of_clear runtime leaks plan bounds inputs
    horizon scheduler trace clear packet authentic
  have packetAttempt : packet.payload.attempt = ⟨plan.eventPhase event, 0⟩ := by
    have same := congrArg CommitAttemptPacket.attempt recovered
    simpa only [RuntimePhasePlan.stampPacket, named, Option.map_some, Option.getD_some] using
      same.symm
  have unique : ∀ other ∈ first ++ rest,
      ¬ PhaseService.EmitsOtherFor runtime leaks other
        ⟨packet.payload.attempt, event⟩ packet.id := by
    intro other otherMember another
    obtain ⟨otherPacket, otherEmitted, sender, _attempt, otherNamed, different⟩ := another
    apply sole (playerEntry runtime leaks plan other)
    · rw [← List.map_append]
      exact List.mem_map.mpr ⟨other, otherMember, rfl⟩
    · refine ⟨Message.mapPayload CommitAttemptPacket.packet otherPacket, ?_, sender,
        otherNamed, different⟩
      change other.emitted.map (Message.mapPayload CommitAttemptPacket.packet) = _
      rw [otherEmitted]
      rfl
  exact service ⟨packet.payload.attempt, event⟩ owner owned first rest original packet recallEq
    packetEmitted authored rfl named wasReady unique (currentAttempt.trans packetAttempt.symm)
    unfinished passed

/-- Restriction of the original physical opportunity contract to an actual
counted prefix uses the raw trace, preserving its deviation quantifier. -/
theorem opportunity_projection [Fintype Player] (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (delay : graph.EventId → Nat)
    (service : PhaseService.Opportunity runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler delay) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)) :
    OpportunityAt runtime (nativeLeaks leaks plan) (execution runtime leaks plan current.execution)
      delay :=
  opportunityAt_projection runtime leaks plan current.execution delay
    (service current ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon
      scheduler trace))

/-- Restrict the physical protected-inclusion contract only at the actual clear
prefix where native reconstruction is faithful. -/
theorem protectedInclusion_projection [Fintype Player] (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (bound : graph.EventId → Nat)
    (service : PhaseService.ProtectedInclusion runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler bound) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) :
    ProtectedInclusionAt runtime (nativeLeaks leaks plan)
      (execution runtime leaks plan current.execution) bound :=
  protectedInclusionAt_projection runtime leaks plan bounds ordered maximal inputs horizon scheduler
    trace clear bound (service current ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
      _ horizon scheduler trace))

end Vegas.EventGraphRuntime.PhaseNativeProjection
