/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSlotHistory
import Vegas.Pending.PhaseBindingRepairFrame

/-! # Exact eligible slots across actual physical binding repair frames -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Actual slot eligibility is unchanged by the retained binding-memory frame.
Both menu guards are discharged from their actual initialized callbacks;
counted raw response menus need not have equal cardinality. -/
theorem binding_slots_eq_of_history
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (left right : (phaseApplication runtime leaks).Control)
    (leftExecution : left.execution = original) (rightExecution : right.execution = repaired)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some left))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some right))
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (leftRequest : original.application.SeedRequest owner
      ⟨original.application.attempt, event⟩)
    (rightRequest : repaired.application.SeedRequest owner
      ⟨repaired.application.attempt, event⟩)
    (leftUnsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (original.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩)
    (rightUnsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (repaired.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨repaired.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload (original.recall owner)
        (original.observe (phaseApplication runtime leaks) owner) =
      PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload (repaired.recall owner)
        (repaired.observe (phaseApplication runtime leaks) owner) := by
  classical
  ext serial
  have forward (selected : serial ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner
      event payload (original.recall owner)
        (original.observe (phaseApplication runtime leaks) owner)) :
      serial ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
        (repaired.recall owner) (repaired.observe (phaseApplication runtime leaks) owner) := by
    obtain ⟨bounded, fresh, _covered⟩ := Finset.mem_filter.mp selected
    change original.application.current.native.candidates.lookup (owner, .prepared serial) =
      .fresh at fresh
    have imageFresh := (frame.live.slots (.prepared serial)).mp fresh
    have member := PhaseCount.mem_phaseBindingSlots_of_history runtime leaks bounds
      (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler right rightTrace
      owner event payload binding (rightExecution.symm ▸ rightRequest)
      (rightExecution.symm ▸ rightUnsent)
      values serial (Finset.mem_range.mp bounded) (rightExecution.symm ▸ imageFresh)
    simpa only [rightExecution] using member
  constructor
  · exact forward
  · intro selected
    obtain ⟨bounded, fresh, _covered⟩ := Finset.mem_filter.mp selected
    change repaired.application.current.native.candidates.lookup (owner, .prepared serial) =
      .fresh at fresh
    have sourceFresh := (frame.live.slots (.prepared serial)).mpr fresh
    have member := PhaseCount.mem_phaseBindingSlots_of_history runtime leaks bounds
      (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler left leftTrace
      owner event payload binding (leftExecution.symm ▸ leftRequest)
      (leftExecution.symm ▸ leftUnsent)
      values serial (Finset.mem_range.mp bounded) (leftExecution.symm ▸ sourceFresh)
    simpa only [leftExecution] using member

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
