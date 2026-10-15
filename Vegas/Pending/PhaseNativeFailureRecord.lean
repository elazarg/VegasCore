/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeInclusion
import Vegas.Pending.PhaseFailureCoverage

/-! # Actual physical exclusions retain their native first-failure owners -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- At an actual clear physical prefix, every publicly failed native event is
absent and every accepted binding has its genuine completion receipt. -/
theorem clear_publicRecord (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) :
    PublicExclusionRecord current.execution.application.current := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have valid :=
    (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw).active
  refine ⟨valid.receipts, fun owner => ⟨?_, ?_⟩⟩
  · intro member
    simp only [clear, Finset.notMem_empty] at member
  · rintro ⟨event, acting, failed⟩
    exact valid.covered event owner acting failed

/-- The native inclusion result, before any phase rollback, records exactly the
owners excluded by the real physical inclusion. -/
theorem includePending_exclusionRecord (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (id : MessageId Player) :
    PublicExclusionRecord
      (⟨((execution runtime leaks plan current.execution).includePending N id).application,
        (current.execution.includePending P id).application.current.excluded⟩ :
        RecoveryState graph) := by
  have valid := clear_publicRecord runtime leaks plan bounds inputs horizon scheduler trace clear
  have handles (message : Message Player (CommitAttemptPacket graph))
      (selected : (current.execution.network.includePending id).1 = some message) :=
    handle_map_of_clear runtime leaks plan bounds ordered maximal inputs horizon scheduler trace
      clear message (included_authentic runtime leaks plan bounds inputs horizon scheduler trace
        id message selected)
  simp only [ReactiveApplication.Execution.includePending, execution]
  rw [← MessageNetwork.mapPayload_includePending]
  generalize queued : current.execution.network.includePending id = pair
  rcases pair with ⟨envelope, network⟩
  cases envelope with
  | none => exact valid
  | some message =>
      have selected : (current.execution.network.includePending id).1 = some message :=
        congrArg Prod.fst queued
      dsimp only []
      have handled := handles message selected
      change (P).handle current.execution.application message = _ at handled
      erw [handled]
      simp only [Option.map_some]
      cases accepted : (N).handle current.execution.application.current.native
          (Message.mapPayload CommitAttemptPacket.packet message) with
      | none =>
          simp only [Option.map_none, Option.getD_none]
          exact valid
      | some native =>
          simp only [Option.map_some, Option.getD_some]
          have physical := (PhaseRuntimeState.settle_physical
            current.execution.application.phases current.execution.application.generation
            current.execution.application.entry
            (current.execution.application.current.inclusionResult
              message.payload.packet.call native)
            current.execution.application.retired).1
          change _ = (current.execution.application.current.inclusionResult
            message.payload.packet.call native).excluded at physical
          change PublicExclusionRecord
            (⟨native, (PhaseRuntimeState.settle current.execution.application.phases
              current.execution.application.generation current.execution.application.entry
              (current.execution.application.current.inclusionResult
                message.payload.packet.call native)
              current.execution.application.retired).current.excluded⟩ : RecoveryState graph)
          rw [physical]
          obtain ⟨_token, rawAccepted⟩ := reactiveApplication_handle_eq_some runtime
            (nativeLeaks leaks plan) _ _ _ accepted
          change runtime.handle current.execution.application.current.native
            ⟨message.id, message.payload.packet.call⟩ = some native at rawAccepted
          exact valid.inclusionResult runtime ⟨message.id, message.payload.packet.call⟩ native
            rawAccepted

end Vegas.EventGraphRuntime.PhaseNativeProjection
