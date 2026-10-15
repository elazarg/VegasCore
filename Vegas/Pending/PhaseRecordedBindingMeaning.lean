/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeTrace
import Vegas.Pending.PhasePreparedBinding
import Vegas.Pending.ReactiveBinding
import Vegas.Pending.RecordedBindingReadback
import Vegas.Pending.PhaseBindingInvariant

/-! # Original authored binding meanings at actual clear phase histories -/

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

/-- Projecting the genuine clear trace transports its original authored result
through the native immutable-catalogue theorem, without resampling the binding. -/
theorem recorded_binding_result_of_clear (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) (entry : (P).PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (declared : entry.action = phaseBindingResponse runtime leaks who event payload result serial)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh) :
    control.execution.application.current.native.bindingResult (who, .prepared serial) payload =
      result := by
  have nativeTrace := nativeTrace runtime leaks plan bounds ordered maximal inputs horizon
    scheduler trace (fun current same => by cases same; exact clear)
  have remembered : playerEntry runtime leaks plan entry ∈
      (execution runtime leaks plan control.execution).recall who := List.mem_map.mpr
    ⟨entry, retained, rfl⟩
  have meaning := runtime.recordedBindingMeaning_history (nativeLeaks leaks plan)
    (inputs.map State.initial) horizon (nativeScheduler runtime leaks plan scheduler)
    (PhaseNativeProjection.control runtime leaks plan control) nativeTrace who
      (playerEntry runtime leaks plan entry) remembered event payload result serial
      (by change action runtime leaks plan entry.action = _; rw [declared]; rfl) fresh
  exact meaning.2

/-- The action in the actual completed graph history is exactly the result of
its original authored fresh binding response. Both the complete native trace and
accepted association are checked on this same actual clear phase execution. -/
theorem completed_binding_action_of_recorded (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding who payload)
    (result : PublicationResult (L.Val payload)) (serial : Nat) (entry : (P).PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (declared : entry.action = phaseBindingResponse runtime leaks who event payload result serial)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (accepted : control.execution.application.current.native.accepted (.inr event) =
      some (who, .prepared serial))
    (completed : event ∈ control.execution.application.current.native.config.cut.completed) :
    ∃ original : graph.Action event,
      ⟨event, original⟩ ∈ control.execution.application.current.native.config.history ∧
      cast (congrArg EventField.Action binding) original = result := by
  have nativeTrace := nativeTrace runtime leaks plan bounds ordered maximal inputs horizon
    scheduler trace (fun current same => by cases same; exact clear)
  obtain ⟨draw, _supported, valid⟩ := runtime.reactive_history_invariant
    (nativeLeaks leaks plan) inputs horizon (nativeScheduler runtime leaks plan scheduler)
      nativeTrace
  have bindings := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace)
  obtain ⟨original, recorded, meaning⟩ := bindings.active.completed_binding_action
    valid.reachable event who payload binding completed
  rw [accepted, Option.elim_some] at meaning
  exact ⟨original, recorded, meaning.trans (recorded_binding_result_of_clear runtime leaks plan
    bounds ordered maximal inputs horizon scheduler trace clear who event payload result serial
      entry retained declared fresh)⟩

end Vegas.EventGraphRuntime.PhaseNativeProjection
