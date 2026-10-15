/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseRecordedRequest
import Vegas.Pending.PhaseNativePlayerInput
import Vegas.Pending.ReactivePolicyFacts

/-! # Native submission and private-decision freshness at clear unsent requests -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Erasing physical tags does not create an old submission for a current
unsent request: every authentic clear packet reconstructs its unique source tag. -/
theorem phase_unsent_native_submitted_false
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (event : graph.EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩) :
    runtime.reactiveAlreadySubmitted (PhaseNativeProjection.nativeLeaks leaks plan)
      ((PhaseNativeProjection.execution runtime leaks plan control.execution).recall who)
      event = false := by
  let nativeLeaks := PhaseNativeProjection.nativeLeaks leaks plan
  let past := (control.execution.recall who).map
    (PhaseNativeProjection.playerEntry runtime leaks plan)
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have address := phase_request_address_of_clear runtime leaks plan inputs horizon scheduler raw
    clear who ⟨control.execution.application.attempt, event⟩ request
  have recalled := (phaseApplication runtime leaks).history_inputRecall _ horizon scheduler raw
  cases submitted : runtime.reactiveAlreadySubmitted nativeLeaks past event with
  | false => exact submitted
  | true =>
      have named := (runtime.reactiveAlreadySubmitted_iff nativeLeaks past event).mp submitted
      obtain ⟨nativeEntry, nativeMember, nativeNamed⟩ := List.mem_filterMap.mp named
      obtain ⟨entry, member, rfl⟩ := List.mem_map.mp nativeMember
      cases emitted : entry.emitted with
      | none =>
          simp only [PhaseNativeProjection.playerEntry, emitted, Option.map_none,
            Option.bind_none] at nativeNamed
          cases nativeNamed
      | some message =>
          have call : message.payload.packet.call.event? graph = some event := by
            simpa only [PhaseNativeProjection.playerEntry, emitted, Option.map_some,
              Option.bind_some, Message.mapPayload] using nativeNamed
          have output : message ∈ (phaseApplication runtime leaks).outputs
              (control.execution.recall who) := List.mem_filterMap.mpr ⟨entry, member, emitted⟩
          have authentic : message ∈ control.execution.network.inputs := by
            have actual := output
            rw [← recalled who] at actual
            exact (List.mem_filter.mp actual).1
          have stamped := PhaseCount.stamp_nativeMessage_of_clear runtime leaks plan bounds inputs
            horizon scheduler trace clear message authentic
          have messageAddress : message.payload.attempt = ⟨plan.eventPhase event, 0⟩ := by
            have tagged := congrArg CommitAttemptPacket.attempt stamped.symm
            simpa only [RuntimePhasePlan.stampPacket, call, Option.map_some, Option.getD_some]
              using tagged
          have same := messageAddress.trans address.symm
          exact (unsent message output (by
            simp only [PhaseCount.event?, call, Option.map_some, same])).elim

/-- When actual earlier callbacks to a current request all transmitted, no
private memory can validate an old silent decision for that request. -/
theorem phase_native_decided_false_of_nonsilent_requests
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (event : graph.EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (nonsilent : ∀ entry ∈ control.execution.recall who,
      PhaseRuntimeState.requests entry.beforeView.application.2 who
        ⟨control.execution.application.attempt, event⟩ → entry.action.transmission.isSome = true)
    (intentions : List (Option graph.Completion)) :
    runtime.reactiveAlreadyDecided (PhaseNativeProjection.nativeLeaks leaks plan) who
      ((PhaseNativeProjection.execution runtime leaks plan control.execution).recall who)
      intentions event = false := by
  classical
  cases decided : runtime.reactiveAlreadyDecided (PhaseNativeProjection.nativeLeaks leaks plan)
      who ((PhaseNativeProjection.execution runtime leaks plan control.execution).recall who)
      intentions event with
  | false => rfl
  | true =>
      obtain ⟨nativeEntry, remembered, zipped, named, matching⟩ := of_decide_eq_true decided
      have nativeMember := (List.of_mem_zip zipped).1
      obtain ⟨entry, member, rfl⟩ := List.mem_map.mp nativeMember
      have turn : entry.beforeView.application.1.publicView.ownTurn? who = some event :=
        matching.2.2.2.1.trans (congrArg some named)
      have requested := phase_recorded_request_of_native_turn runtime leaks bounds plan ordered
        maximal inputs horizon scheduler trace clear who event request entry member turn
      have sent := nonsilent entry member requested
      have silent : entry.action.transmission = none := matching.2.1
      rw [silent] at sent
      cases sent

end Vegas.EventGraphRuntime
