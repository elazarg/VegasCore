/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearTraceProgress
import Vegas.Pending.PhaseReadyRequests
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseBindingRepairCompletion
import Vegas.Pending.PhaseNativeInvariant

/-! # Earlier opening callbacks before a clear binding decision -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- A ready publication from an earlier actual prefix has completed before a
later clear binding request. Independent publications do not cross a phase barrier. -/
theorem phase_opening_completed_before_binding (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (beforeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (afterTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (clear : after.execution.application.current.excluded = ∅)
    (event : graph.EventId) (payload : L.Ty)
    (publication : graph.outputLayout event = .publication payload)
    (ready : before.execution.application.current.native.config.cut.Ready event)
    (bindingEvent : graph.EventId) (owner : Player) (bindingPayload : L.Ty)
    (binding : graph.outputLayout bindingEvent = .binding owner bindingPayload)
    (requested : after.execution.application.SeedRequest owner
      ⟨after.execution.application.attempt, bindingEvent⟩) :
    event ∈ after.execution.application.current.native.config.cut.completed := by
  rcases phase_ready_or_completed_of_clear_prefix runtime leaks
    (PhaseCount.onePacketMenu runtime leaks bounds) _ horizon scheduler before after beforeTrace
      afterTrace isPrefix clear event ready with completed | stillReady
  · exact completed
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler
    afterTrace
  have initiallyLive : ∀ state ∈ (inputs.map (PhaseRuntimeState.initial plan)).support,
      state.Frontier ∧ state.Live := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact ⟨PhaseRuntimeState.initial_frontier plan draw, PhaseRuntimeState.initial_live plan draw⟩
  have live := (phaseApplication_live runtime leaks).history _ horizon scheduler initiallyLive raw
  have geometry := phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler raw
  obtain ⟨phase, head, eventMember⟩ := after.execution.application.ready_current_phase ordered
    live.1 live.2 geometry.2.2 event stillReady
  obtain ⟨other, otherHead, bindingMember⟩ := requested.2.1
  have same : phase = other := by
    exact Option.some.inj ((Option.mem_def.mp head).symm.trans (Option.mem_def.mp otherHead))
  subst other
  obtain ⟨lower, upper⟩ := (phase.mem_events event).mp eventMember
  obtain ⟨bindingLower, bindingUpper⟩ := (phase.mem_events bindingEvent).mp bindingMember
  have publicKind := phase.fields event lower upper
  have bindingKind := phase.fields bindingEvent bindingLower bindingUpper
  cases kind : phase.kind <;> rw [kind] at publicKind bindingKind
  · obtain ⟨otherOwner, otherPayload, impossible⟩ := publicKind
    rw [publication] at impossible
    cases impossible
  · obtain ⟨otherPayload, impossible⟩ := bindingKind
    rw [binding] at impossible
    cases impossible
  · obtain ⟨otherPayload, impossible⟩ := bindingKind
    rw [binding] at impossible
    cases impossible

/-- Actual success at the final clear completed publication is read back at
the earlier callback. No intended-source or successful-opening premise is supplied. -/
theorem phase_opening_binding_success_before_binding (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (beforeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (afterTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (clear : after.execution.application.current.excluded = ∅)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (ref : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload ref checks)
    (node : nodeView graph event = .resolve owner payload ref checks outputEq codeEq)
    (ready : before.execution.application.current.native.config.cut.Ready event)
    (bindingEvent : graph.EventId) (bindingOwner : Player) (bindingPayload : L.Ty)
    (binding : graph.outputLayout bindingEvent = .binding bindingOwner bindingPayload)
    (requested : after.execution.application.SeedRequest bindingOwner
      ⟨after.execution.application.attempt, bindingEvent⟩) :
    ∃ value, ref.get? before.execution.application.current.native.config.store =
      some (.success value) := by
  have completed := phase_opening_completed_before_binding runtime leaks bounds plan ordered
    maximal inputs horizon scheduler before after beforeTrace afterTrace isPrefix clear event
      payload outputEq ready bindingEvent bindingOwner bindingPayload binding requested
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler
    afterTrace
  have covered := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  obtain ⟨value, stored⟩ := covered.active.completed_publication_binding clear
    valid.active.reachable
    event owner payload ref checks outputEq codeEq node completed
  have progress := phase_clear_nativeProgress_of_prefix runtime leaks
    (PhaseCount.onePacketMenu runtime leaks bounds) _ horizon scheduler before after beforeTrace
      afterTrace isPrefix clear
  have available := before.execution.application.current.native.config.read_available ready (by
    rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
    exact Finset.mem_insert_self _ _)
  obtain ⟨result, present⟩ := Option.isSome_iff_exists.mp (ref.get?_isSome _ available)
  have retained := ref.get?_preserved _ _ progress.2.1 result present
  have resultEq := Option.some.inj (retained.symm.trans stored)
  exact ⟨value, present.trans (congrArg some resultEq)⟩

end Vegas.EventGraphRuntime
