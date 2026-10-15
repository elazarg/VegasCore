/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseLatestBindings

/-! # Latest surviving signed handles at actual counted histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Actual semantic checkpoints, signed namespace history and permanent count
cleanliness together identify the surviving physical binding handle. -/
structure PhysicalBindings (execution : (app).Execution) : Prop where
  saved : LatestBindingTable execution.network.inputs execution.application.entry.native
  active : LatestBindingTable execution.network.inputs execution.application.current.native
  stamp : LiveBindingStamp runtime leaks execution
  record : execution.application.ExclusionRecord
  namespaces : InputNamespaces runtime leaks execution
  clean : CountClean runtime leaks execution
  origins : execution.Provenance (app)

private theorem saved_bindingStamp (execution : (app).Execution)
    (valid : execution.application.ExclusionRecord) :
    BindingStamp (fun who => (app).outputs (execution.recall who)) execution.application.attempt
      execution.application.entry.native := by
  apply BindingStamp.of_before
  intro event candidate installed
  cases phases : execution.application.phases with
  | nil =>
      simpa only [PhaseRuntimeState.attempt, phases, List.head?_nil, Option.map_none,
        Option.getD_none] using event.isLt
  | cons phase rest =>
      have positioned := valid.frontier.positioned
      rw [phases] at positioned
      have lower := (positioned.1.2 event).mp (valid.saved event candidate installed)
      simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some] using lower

private theorem physicalBindings_respond (execution : (app).Execution)
    (who : Player) (response : (app).Action) (valid : PhysicalBindings runtime leaks execution)
    (permitted : response.transmission = none ∨ OnePacketResponse runtime leaks who
      (execution.recall who) (execution.observe (app) who) response) :
    PhysicalBindings runtime leaks (execution.respond (app) who response) := by
  have nextClean := countClean_respond runtime leaks execution valid.clean who response permitted
  refine ⟨?_, ?_, liveBindingStamp_respond runtime leaks execution who response valid.stamp,
    (phaseApplication_exclusionRecord runtime leaks).respond execution who response valid.record,
    valid.namespaces.respond who response, nextClean,
    (app).respond_provenance execution who response valid.origins⟩
  · cases response with
    | mk transmission =>
        cases transmission with
        | none => exact valid.saved
        | some material =>
            let message := localEnvelope runtime leaks who (execution.recall who)
              (execution.observe (app) who) material
            have inputs := (permits_respond runtime leaks execution valid.clean.1 who material).1
            change LatestBindingTable _ execution.application.entry.native
            rw [inputs]
            apply valid.saved.append message
            intro event candidate installed sender handle
            exact response_ne_accepted_binding runtime leaks execution valid.clean who material
              nextClean execution.application.entry.native
              (saved_bindingStamp runtime leaks execution valid.record) event candidate installed
              sender handle
  · cases response with
    | mk transmission =>
        cases transmission with
        | none => exact valid.active
        | some material =>
            let message := localEnvelope runtime leaks who (execution.recall who)
              (execution.observe (app) who) material
            have inputs := (permits_respond runtime leaks execution valid.clean.1 who material).1
            rw [inputs]
            apply (valid.active.append message ?_).copy
            · change (submitStep (material.call.register execution.application.current.native who)
                who material.call.packet).accepted = _
              rw [submitStep_accepted, Submission.register_accepted]
            · intro event candidate installed sender handle
              exact response_ne_accepted_binding runtime leaks execution valid.clean who material
                nextClean execution.application.current.native valid.stamp event candidate installed
                sender handle

private theorem latestBindings_handle (execution : (app).Execution)
    (next : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (valid : PhysicalBindings runtime leaks execution) (member : message ∈ execution.network.inputs)
    (handled : execution.application.handle runtime message = some next) :
    LatestBindingTable execution.network.inputs next.entry.native ∧
      LatestBindingTable execution.network.inputs next.current.native := by
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · rename_i allowed
    obtain ⟨native, accepted, rfl⟩ := Option.map_eq_some_iff.mp handled
    have tagValid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).1
    change (decide (message.payload.attempt = execution.application.attempt) &&
      message.payload.packet.tokenValid) = true at tagValid
    have current : message.payload.attempt = execution.application.attempt :=
      decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp tagValid).1
    apply PhaseRuntimeState.settle_latestBindings
    · exact valid.saved
    · rcases handle_tables_cases runtime execution.application.current.native native _ accepted with
        ⟨event, candidate, call, _, table, owner⟩ | ⟨table, _⟩
      · intro field handle installed
        change native.accepted (.inr field) = some handle at installed
        rw [table] at installed
        by_cases same : field = event
        · subst field
          rw [Function.update_self] at installed
          cases Option.some.inj installed
          exact ⟨message, member, owner.symm, call,
            current_binding_latest runtime leaks execution valid.namespaces valid.clean
              message member current event candidate call⟩
        · rw [Function.update_of_ne (by simpa using same)] at installed
          exact valid.active field handle installed
      · exact valid.active.copy table
  · cases handled

private theorem latestBindings_environment (execution next : (app).Execution)
    (command : (app).Command) (valid : PhysicalBindings runtime leaks execution)
    (reached : next ∈ (execution.environmentStep (app) command).support) :
    LatestBindingTable next.network.inputs next.application.entry.native ∧
      LatestBindingTable next.network.inputs next.application.current.native := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨valid.saved, valid.active⟩
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨valid.saved, valid.active⟩
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact ⟨valid.saved, valid.active⟩
      | some message =>
          change LatestBindingTable execution.network.inputs
              (((app).handle execution.application message).getD
                execution.application).entry.native ∧
            LatestBindingTable execution.network.inputs
              (((app).handle execution.application message).getD
                execution.application).current.native
          cases accepted : (app).handle execution.application message with
          | none => exact ⟨valid.saved, valid.active⟩
          | some state =>
              exact latestBindings_handle runtime leaks execution state message valid
                (((app).retained_envelopes_mem_inputs execution valid.origins
                  valid.clean.1.1).lookup
                  id message found) accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (execution.application.environment runtime command).support at changed
      unfold PhaseRuntimeState.environment at changed
      split at changed
      · rw [PMF.support_map] at changed
        obtain ⟨native, nativeMoved, rfl⟩ := changed
        exact PhaseRuntimeState.settle_latestBindings _ _ _ _ _ _ valid.saved
          (valid.active.copy (environmentStep_tables runtime _ _ command nativeMoved).1)
      · rw [PMF.mem_support_pure_iff] at changed
        subst state
        exact ⟨valid.saved, valid.active⟩

/-- Every actual counted history identifies each saved and live accepted handle
with the latest authentic own binding for that static source field. -/
theorem physicalBindings_history [Fintype Player] (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    PhysicalBindings runtime leaks control.execution := by
  have invariant : (onePacketMenu runtime leaks bounds).ServiceInvariant scheduler
      (PhysicalBindings runtime leaks) := {
    respond := fun execution who response valid member =>
      physicalBindings_respond runtime leaks execution who response valid
        ((mem_onePacketActions runtime leaks bounds who _ _ response).mp member).2
    environment := fun execution next command valid _ reached => by
      obtain ⟨saved, active⟩ := latestBindings_environment runtime leaks execution next command
        valid reached
      exact ⟨saved, active,
        liveBindingStamp_environment runtime leaks execution next command valid.stamp valid.record
          valid.origins reached,
        (phaseApplication_exclusionRecord runtime leaks).environmentStep execution next command
          valid.record reached,
        valid.namespaces.environment command reached,
        countClean_environment runtime leaks execution next command valid.clean reached,
        (app).environment_provenance execution next command valid.origins reached⟩ }
  apply invariant.history _ horizon _ trace
  intro state supported
  obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
  have vacant : LatestBindingTable [] (State.initial draw) := by
    intro event candidate installed
    obtain ⟨input, owner, payload, impossible, rest⟩ :=
      State.initial_accepted_eq_some draw (.inr event) candidate installed
    cases impossible
  obtain ⟨saved, active⟩ := PhaseRuntimeState.settle_latestBindings [] plan.phases 0
    ⟨State.initial draw, ∅⟩ ⟨State.initial draw, ∅⟩ [] vacant vacant
  refine ⟨saved, active, ?_, PhaseRuntimeState.initial_exclusionRecord plan draw,
    InputNamespaces.initial _ (PhaseRuntimeState.initial_ordered plan draw),
    countClean_initial runtime leaks _, MessageNetwork.Satisfies.empty⟩
  apply PhaseRuntimeState.settle_bindingStamp _ _ _ _ _ _ plan.adjacent
  · intro phase member event candidate installed
    obtain ⟨input, owner, payload, impossible, rest⟩ :=
      State.initial_accepted_eq_some draw (.inr event) candidate installed
    cases impossible
  · intro phase member event candidate installed
    obtain ⟨input, owner, payload, impossible, rest⟩ :=
      State.initial_accepted_eq_some draw (.inr event) candidate installed
    cases impossible
  · intro event candidate installed
    obtain ⟨input, owner, payload, impossible, rest⟩ :=
      State.initial_accepted_eq_some draw (.inr event) candidate installed
    cases impossible

end Vegas.EventGraphRuntime.PhaseCount
