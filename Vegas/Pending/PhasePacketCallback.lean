/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseNativeTrace
import Vegas.Pending.PhaseClearTraceProgress
import Vegas.Pending.ReactiveEmissionTokens
import Interaction.ReactiveRecordedResponse

/-! # The actual callback and firstness of an owned physical packet -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- A real owned packet at a clear counted history retains its actual legal
supported callback at the same request, before any previous own packet for
that coordinate. Neither a source policy nor a packet shape is assumed. -/
theorem packet_callback (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (owner : Player)
    (policy : (P).Policy) (consistent : policy.Consistent (current.execution.recall owner))
    (coordinate : CommitAttemptEvent graph)
    (message : Message Player (CommitAttemptPacket graph))
    (output : message ∈ (P).outputs (current.execution.recall owner))
    (named : PhaseCount.event? message.payload = some coordinate) :
    ∃ (entry : (P).PlayerEntry) (before : (P).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
      (material : WitnessedSubmission graph),
      entry ∈ current.execution.recall owner ∧ entry.emitted = some message ∧
      TracePrefix prior trace ∧ before.actor = some owner ∧
      before.execution.application.SeedRequest owner coordinate ∧
      entry.beforeView = before.execution.observe P owner ∧
      entry.action.transmission = some material ∧
      material.call.packet.event? graph = some coordinate.event ∧
      entry.action ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (before.execution.recall owner) (before.execution.observe P owner) ∧
      entry.action ∈ (policy (before.execution.recall owner)
        (before.execution.observe P owner)).support ∧
      (∀ previous ∈ (P).outputs (before.execution.recall owner),
        PhaseCount.event? previous.payload ≠ some coordinate) ∧
      ∃ after, current.execution.recall owner =
        before.execution.recall owner ++ entry :: after := by
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨entry, recorded, emitted⟩ := List.mem_filterMap.mp output
  have raw := menu.toRawTrace initial horizon scheduler trace
  have nativePrior := nativeTrace runtime leaks plan bounds ordered maximal inputs horizon scheduler
    trace (fun _ same => by cases same; exact clear)
  let nativeEntry := playerEntry runtime leaks plan entry
  have nativeRecorded : nativeEntry ∈ (execution runtime leaks plan current.execution).recall
      owner := List.mem_map.mpr ⟨entry, recorded, rfl⟩
  have nativeEmitted : nativeEntry.emitted =
      some (Message.mapPayload CommitAttemptPacket.packet message) := by
    change entry.emitted.map (Message.mapPayload CommitAttemptPacket.packet) = _
    rw [emitted]
    rfl
  have emission := reactiveEmission_history runtime (nativeLeaks leaks plan)
    (inputs.map State.initial) horizon (nativeScheduler runtime leaks plan scheduler)
      (control runtime leaks plan current) nativePrior owner
  obtain ⟨material, transmitted⟩ : ∃ material, entry.action.transmission = some material := by
    cases sent : entry.action.transmission with
    | none =>
        have absent := emission.1 nativeEntry nativeRecorded sent
        rw [nativeEmitted] at absent
        cases absent
    | some material => exact ⟨material, rfl⟩
  obtain ⟨nativeMessage, nativeSent, call⟩ :=
    emission.2 nativeEntry nativeRecorded material transmitted
  have sameMessage : nativeMessage = Message.mapPayload CommitAttemptPacket.packet message :=
    Option.some.inj (nativeSent.symm.trans nativeEmitted)
  have materialNamed : material.call.packet.event? graph = some coordinate.event := by
    unfold PhaseCount.event? at named
    obtain ⟨actual, addressed, same⟩ := Option.map_eq_some_iff.mp named
    have sameEvent : actual = coordinate.event := congrArg CommitAttemptEvent.event same
    rw [sameEvent] at addressed
    rw [sameMessage] at call
    exact call.symm ▸ addressed
  obtain ⟨before, prior, retained, acting, viewed, offered, after, recalled⟩ :=
    menu.recorded_response_prefix initial horizon scheduler current trace owner entry recorded
  have faithful := recalled ▸ consistent
  rw [← List.singleton_append, ← List.append_assoc] at faithful
  have sampled := (policy.consistent_snoc_iff (before.execution.recall owner) entry).mp
    (ReactiveApplication.Policy.Consistent.of_append faithful)
  have supported : entry.action ∈ (policy (before.execution.recall owner)
      (before.execution.observe P owner)).support := viewed ▸ sampled.2
  have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before current prior trace retained clear).1
  have sentMember : (⟨some material⟩ : (P).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds
      owner (before.execution.recall owner) (before.execution.observe P owner) := by
    have same : entry.action = (⟨some material⟩ : (P).Action) := by
      cases action : entry.action with
      | mk transmission =>
          rw [action] at transmitted
          exact congrArg ReactiveApplication.Action.mk transmitted
    rwa [same] at offered
  rcases before with ⟨remaining, actor, physical⟩
  cases acting
  obtain ⟨actual, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds plan
    inputs horizon scheduler remaining owner physical prior beforeClear material sentMember
  have addressed := PhaseCount.onePacket_event_of_request runtime leaks bounds plan ordered inputs
    horizon scheduler remaining owner physical prior actual request material sentMember
  have sameEvent : actual.event = coordinate.event :=
    Option.some.inj (addressed.symm.trans materialNamed)
  have packetAttempt : message.payload.attempt = coordinate.attempt := by
    unfold PhaseCount.event? at named
    obtain ⟨event, _addressed, same⟩ := Option.map_eq_some_iff.mp named
    exact congrArg CommitAttemptEvent.attempt same
  have stamped := phase_recalled_emission_attempt runtime leaks initial horizon scheduler raw owner
    entry recorded message emitted
  rw [viewed] at stamped
  have sameAttempt : physical.application.attempt = coordinate.attempt :=
    stamped.symm.trans packetAttempt
  have same : actual = coordinate := by
    rcases actual with ⟨attempt, event⟩
    rcases coordinate with ⟨otherAttempt, otherEvent⟩
    dsimp only at request sameAttempt sameEvent
    cases sameEvent
    cases request.1
    cases sameAttempt
    rfl
  rw [same] at request
  have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan ordered inputs horizon
    scheduler remaining owner physical prior coordinate request material sentMember
  exact ⟨entry, ⟨remaining, some owner, physical⟩, prior, material, recorded, emitted, retained,
    rfl, request, viewed, transmitted, materialNamed, offered, supported, unsent, after, recalled⟩

end Vegas.EventGraphRuntime.PhaseNativeProjection
