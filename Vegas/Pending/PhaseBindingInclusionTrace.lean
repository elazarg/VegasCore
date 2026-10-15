/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingIncludeDispatcher

/-! # Actual same-scheduler inclusion histories for phased binding repairs -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- A genuinely selected include extends the constructed image prefix under
the original scheduler. All missing, rejected and accepted packet cases retain
both frontiers and complete focal inputs. Submitted records remain an explicit
response-induction invariant, rather than a conclusion of this one-step lemma. -/
theorem counted_include_trace
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (recorded : memory.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
      (execution runtime leaks original) (execution runtime leaks repaired))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (remaining : Nat)
    (left : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, original⟩))
    (right : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, repaired⟩))
    (id : MessageId Player)
    (selected : (ReactiveApplication.Command.include id) ∈
      (scheduler original.environmentRecall
        (original.observeEnvironment (phaseApplication runtime leaks))).support)
    (clear : (original.includePending (phaseApplication runtime leaks)
      id).application.current.excluded = ∅) :
    let leftNext := { original.includePending (phaseApplication runtime leaks) id with
      environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
    let rightNext := { repaired.includePending (phaseApplication runtime leaks) id with
      environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
    Frame runtime leaks memory owner leftNext rightNext ∧
      Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨remaining, none, rightNext⟩)) := by
  refine ⟨?_, frame.include_trace (PhaseCount.onePacketMenu runtime leaks bounds)
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler remaining right id selected⟩
  cases found : original.network.lookup id with
  | none => exact frame.include_missing id found
  | some message =>
      have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs horizon
        scheduler left
      obtain ⟨entry, entryMember, material, _, emitted, _⟩ :=
        physical.origins.lookup id message found
      have output : message ∈ (phaseApplication runtime leaks).outputs
          (original.recall message.sender) :=
        List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩
      rw [← physical.clean.1.1 message.sender] at output
      have member : message ∈ original.network.inputs := (List.mem_filter.mp output).1
      have same : message.id = id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      subst id
      exact frame.counted_inclusion onlyBindings recorded bounds plan inputs horizon scheduler
        (remaining + 1) none left right message member found clear

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
