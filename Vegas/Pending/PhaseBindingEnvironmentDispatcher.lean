/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingResponseDispatcher
import Vegas.Pending.PhaseBindingApplicationReplay
import Vegas.Pending.PhaseBindingInclusionTrace

/-! # Every actual environment command extends a recorded phased repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- The original selected command and actual transition support are retained.
The repaired supported outcome and its genuine history are constructed; both
submitted-binding frontiers survive every application and network command. -/
theorem environment_records (frame : Frame runtime leaks memory owner original repaired)
    (recorded : memory.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
      (execution runtime leaks original) (execution runtime leaks repaired))
    (onlyBindings : memory.shadow.OwnBindings owner)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (left : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, original⟩))
    (right : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, repaired⟩))
    (command : (phaseApplication runtime leaks).Command)
    (selected : command ∈ (scheduler original.environmentRecall
      (original.observeEnvironment (phaseApplication runtime leaks))).support)
    (next : (phaseApplication runtime leaks).Execution)
    (moved : next ∈ (original.environmentStep (phaseApplication runtime leaks) command).support)
    (clear : next.application.current.excluded = ∅) :
    ∃ image ∈ (repaired.environmentStep (phaseApplication runtime leaks) command).support,
      Frame runtime leaks memory owner next image ∧
      memory.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
        (execution runtime leaks next) (execution runtime leaks image) ∧
      Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨remaining, command.actor? (phaseApplication runtime leaks), image⟩)) := by
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have chosen : command ∈
      (scheduler repaired.environmentRecall (repaired.observeEnvironment app)).support := by
    rw [← frame.scheduler_law scheduler]
    exact selected
  suffices coupled : ∃ image ∈ (repaired.environmentStep app command).support,
      Frame runtime leaks memory owner next image from by
    obtain ⟨image, supported, paired⟩ := coupled
    exact ⟨image, supported, paired,
      submittedRecords_environmentStep recorded command moved supported,
      menu.trace_environment initial horizon scheduler remaining repaired image command right
        chosen supported⟩
  cases command with
  | application command => exact frame.application_coupling onlyBindings command next moved clear
  | wait =>
      rw [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at moved
      subst next
      refine ⟨_, ?_, frame.wait⟩
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff]
      rfl
  | activate actor =>
      unfold ReactiveApplication.Execution.environmentStep at moved
      obtain ⟨middle, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨sample, observed, rfl⟩ := PMF.support_map .. ▸ supported
      refine ⟨_, ?_, frame.activate actor sample⟩
      unfold ReactiveApplication.Execution.environmentStep
      rw [PMF.support_map]
      refine ⟨{ repaired with network := repaired.network.learn actor sample }, ?_, rfl⟩
      rw [PMF.support_map]
      refine ⟨sample, ?_, rfl⟩
      change sample ∈ (leaks actor repaired.network.pending).support
      change sample ∈ (leaks actor original.network.pending).support at observed
      rwa [← frame.network]
  | «include» id =>
      rw [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at moved
      subst next
      have paired := frame.counted_include_trace onlyBindings recorded bounds plan inputs horizon
        scheduler remaining left right id selected clear
      refine ⟨_, ?_, paired.1⟩
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff]
      rfl

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
