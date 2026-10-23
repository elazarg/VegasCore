/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCompletionStamp
import Interaction.MessageNetworkInvariant
import Interaction.ReactiveProvenance
import Vegas.Pending.PhaseExclusionRecord

/-! # Authentic current-attempt messages for completed owned events -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Completed nonexcluded owned events have authentic outputs in their active
attempt, unless they belong to the saved semantic prefix. -/
def LiveCompletionStamp (execution : (app).Execution) : Prop :=
  CompletionStamp (fun who => (app).outputs (execution.recall who)) execution.application.attempt
    execution.application.current

theorem liveCompletionStamp_respond (execution : (app).Execution)
    (who : Player) (response : (app).Action) (valid : LiveCompletionStamp runtime leaks execution) :
    LiveCompletionStamp runtime leaks (execution.respond (app) who response) := by
  have contains : ∀ observer, (app).outputs (execution.recall observer) ⊆
      (app).outputs ((execution.respond (app) who response).recall observer) := by
    intro observer message member
    obtain ⟨entry, present, emitted⟩ := List.mem_filterMap.mp member
    exact List.mem_filterMap.mpr ⟨entry,
      (app).respond_recall_mono execution who observer response present, emitted⟩
  cases response with
  | mk transmission =>
      cases transmission with
      | none => exact valid.mono contains
      | some material =>
          apply (valid.mono contains).copy
          · change (submitStep (material.call.register execution.application.current.native who)
              who material.call.packet).config = _
            rw [submitStep_config, (material.call.register_facts who _).1]
          · rfl

private theorem liveCompletionStamp_handle (execution : (app).Execution)
    (next : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (valid : LiveCompletionStamp runtime leaks execution)
    (record : execution.application.ExclusionRecord)
    (issued : execution.Issued (app) message)
    (handled : execution.application.handle runtime message = some next) :
    LiveCompletionStamp runtime leaks {execution with application := next} := by
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · rename_i allowed
    obtain ⟨native, accepted, rfl⟩ := Option.map_eq_some_iff.mp handled
    have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
    have tagValid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).1
    change (decide (message.payload.attempt = execution.application.attempt) &&
      message.payload.packet.tokenValid) = true at tagValid
    have current : message.payload.attempt = execution.application.attempt :=
      decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp tagValid).1
    apply PhaseRuntimeState.normalize_completionStamp _ _
      (PhaseRuntimeState.raw_handle_frontier runtime _ record.frontier _ native authorized accepted)
    obtain ⟨entry, present, material, transmission, emitted, packet⟩ := issued
    exact valid.inclusionResult runtime message native accepted
      (List.mem_filterMap.mpr ⟨entry, present, emitted⟩) current
  · cases handled

theorem liveCompletionStamp_environment (execution next : (app).Execution)
    (command : (app).Command) (valid : LiveCompletionStamp runtime leaks execution)
    (record : execution.application.ExclusionRecord) (origins : execution.Provenance (app))
    (reached : next ∈ (execution.environmentStep (app) command).support) :
    LiveCompletionStamp runtime leaks next := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact valid
      | some message =>
          change LiveCompletionStamp runtime leaks {execution with
            application := ((app).handle execution.application message).getD execution.application}
          cases accepted : (app).handle execution.application message with
          | none => exact valid
          | some state =>
              exact liveCompletionStamp_handle runtime leaks execution state message valid record
                (origins.lookup id message found) accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (execution.application.environment runtime command).support at changed
      unfold PhaseRuntimeState.environment at changed
      split at changed
      · rename_i allowed
        rw [PMF.support_map] at changed
        obtain ⟨native, nativeMoved, rfl⟩ := changed
        apply PhaseRuntimeState.normalize_completionStamp _ _
          (PhaseRuntimeState.raw_environment_frontier runtime _ record.frontier _ native allowed
            nativeMoved)
        exact valid.environmentResult runtime command native nativeMoved
      · rw [PMF.mem_support_pure_iff] at changed
        subst state
        exact valid

/-- Arbitrary initialized legal histories preserve authentic current-attempt
outputs for completed events of owners who have not been excluded. -/
theorem phaseLiveCompletionStamp_history (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) : LiveCompletionStamp runtime leaks control.execution := by
  have invariant : (app).ServiceInvariant scheduler (fun execution =>
      LiveCompletionStamp runtime leaks execution ∧ execution.application.ExclusionRecord ∧
        execution.Provenance (app)) := {
    respond := fun execution who response valid =>
      ⟨liveCompletionStamp_respond runtime leaks execution who response valid.1,
        (phaseApplication_exclusionRecord runtime leaks).respond execution who response valid.2.1,
        (app).respond_provenance execution who response valid.2.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨liveCompletionStamp_environment runtime leaks execution next command valid.1 valid.2.1
          valid.2.2 reached,
        (phaseApplication_exclusionRecord runtime leaks).environmentStep execution next command
          valid.2.1 reached,
        (app).environment_provenance execution next command valid.2.2 reached⟩ }
  exact (invariant.history _ horizon (by
    intro state supported
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨?_, PhaseRuntimeState.initial_exclusionRecord plan draw,
      MessageNetwork.Satisfies.empty⟩
    apply PhaseRuntimeState.settle_completionStamp _ _ _ _ _ _
      (PhaseRuntimeState.initial_checkpoint_frontier plan draw)
    intro event owner acting completed active
    exact (Finset.notMem_empty event completed).elim) trace).1

/-- Every completed event in the installed phase, whose owner remains active,
has an actual authentic submitted message naming it in the current attempt. -/
theorem phase_completed_owned_message (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control))
    (phase : RuntimePhase graph)
    (installed : control.execution.application.phases.head? = some phase)
    (event : graph.EventId) (member : event ∈ phase.events) (owner : Player)
    (acting : graph.actor? event = some owner)
    (completed : event ∈ control.execution.application.current.native.config.cut.completed)
    (active : owner ∉ control.execution.application.current.excluded) :
    ∃ message ∈ control.execution.network.inputs, message.sender = owner ∧
      message.payload.attempt = control.execution.application.attempt ∧
      message.payload.packet.call.event? graph = some event := by
  have stamped := phaseLiveCompletionStamp_history runtime leaks plan inputs horizon scheduler trace
  rcases stamped event owner acting completed active with before | ⟨message, present, sender,
      named, current⟩
  · have low : control.execution.application.attempt.phase = phase.low := by
      simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
    have lower := ((phase.mem_events event).mp member).1
    omega
  · have recalledInputs := (app).history_inputRecall
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler trace
    change control.execution.InputRecall (app) at recalledInputs
    have remembered := recalledInputs owner
    have submitted : message ∈ control.execution.network.inputs.filter
        (fun input => input.sender = owner) := by
      rw [remembered]
      exact present
    exact ⟨message, (List.mem_filter.mp submitted).1, sender, current, named⟩

end Vegas.EventGraphRuntime
