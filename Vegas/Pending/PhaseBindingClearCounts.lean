/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingInclusionTrace
import Vegas.Pending.PhasePacketAddress

/-! # Static count admission derived from clear physical attempt histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Clear physical histories reconstruct every actual namespace from the
static event. Consequently their authentic physical first-packet verdict
implies the ordinary native verdict after namespace erasure. -/
theorem native_countPermits_of_clear (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs) :
    countPermits ((execution runtime leaks control.execution).network.inputs)
      (PhaseCount.nativeMessage message) = true := by
  have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs horizon
    scheduler trace
  have permitted := (PhaseCount.permits_eq_true_iff _ _).mp (physical.clean.2 message member)
  apply (countPermits_eq_true_iff _ _).mpr
  refine ⟨permitted.1, permitted.2.1, ?_⟩
  intro other earlier sameEvent
  obtain ⟨prior, before, rfl⟩ :=
    (PhaseCount.earlier_native control.execution.network.inputs message other).mp earlier
  apply permitted.2.2.1 prior before
  have first := PhaseCount.stamp_nativeMessage_of_clear runtime leaks plan bounds inputs horizon
    scheduler trace clear prior before.1
  have second := PhaseCount.stamp_nativeMessage_of_clear runtime leaks plan bounds inputs horizon
    scheduler trace clear message member
  rw [← first, ← second]
  dsimp only [PhaseCount.nativeMessage] at sameEvent
  simp only [PhaseCount.event?, RuntimePhasePlan.stampPacket]
  rw [sameEvent]

omit [Fintype Player] in
/-- Namespace erasure preserves structural recall accounting. This does not
assert any passive-observation support under the native proof carrier. -/
theorem native_countRecall (physical : (phaseApplication runtime leaks).Execution)
    (count : PhaseCount.CountRecall runtime leaks physical) :
    runtime.CountRecall (nativeLeaks (graph := graph))
      (execution runtime leaks physical) := by
  refine ⟨?_, ?_, ?_⟩
  · intro who
    change ((physical.network.inputs.map PhaseCount.nativeMessage).filter
      (fun input => input.sender = who)) =
        (runtime.reactiveApplication (nativeLeaks (graph := graph))).outputs
          ((physical.recall who).map (entry runtime leaks))
    rw [outputs, ← count.1 who]
    simp only [List.filter_map, Function.comp_def, PhaseCount.nativeMessage, Message.sender]
    rfl
  · intro who
    change physical.network.nextSerial who =
      (runtime.reactiveApplication (nativeLeaks (graph := graph))).submissionCount
        ((physical.recall who).map (entry runtime leaks))
    rw [count.2.1 who]
    simp only [ReactiveApplication.submissionCount, List.countP_map, Function.comp_def,
      entry, action, ReactiveApplication.Action.isSubmission]
    apply congrArg (fun test => (physical.recall who).countP test)
    funext recorded
    rcases recorded with ⟨before, ⟨transmission⟩, emitted⟩
    cases transmission <;> rfl
  · intro who
    change (((physical.network.inputs.map PhaseCount.nativeMessage).filter
      (fun input => input.sender = who)).map (fun input => input.id.2)) =
        List.range (physical.network.nextSerial who)
    convert count.2.2 who using 1
    simp only [List.filter_map, List.map_map, Function.comp_def, PhaseCount.nativeMessage,
      Message.sender]
    rfl

/-- The complete native count invariant follows from the actual clear
physical trace; static firstness is proved by namespace reconstruction. -/
theorem native_countClean_of_clear (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    runtime.CountClean (nativeLeaks (graph := graph))
      (execution runtime leaks control.execution) := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  refine ⟨native_countRecall runtime leaks control.execution
    (PhaseCount.countRecall_history runtime leaks raw), ?_⟩
  intro message member
  obtain ⟨physical, present, rfl⟩ := List.mem_map.mp member
  exact native_countPermits_of_clear runtime leaks bounds plan inputs horizon scheduler trace clear
    physical present

end Vegas.EventGraphRuntime.PhaseBindingRepair
