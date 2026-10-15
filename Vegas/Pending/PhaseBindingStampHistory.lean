/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingStamp

/-! # Actual history provenance of live binding attempt stamps -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Exact semantic frontiers turn native receipt completeness into the
rank bounds needed by physical stamp preservation. -/
theorem normalize_bindingStamp
    (outputs : Player → List (Message Player (CommitAttemptPacket graph)))
    (state : PhaseRuntimeState graph) (frontier : state.Frontier)
    (saved : state.entry.native.ReceiptsComplete) (active : state.current.native.ReceiptsComplete)
    (stamped : BindingStamp outputs state.attempt state.current.native) :
    BindingStamp outputs state.normalize.attempt state.normalize.current.native := by
  apply settle_bindingStamp outputs state.phases state.generation state.entry state.current
    state.retired frontier.adjacent
  · intro phase member event candidate installed
    cases phases : state.phases with
    | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
    | cons current rest =>
        have same : phase = current := by
          symm
          simpa only [phases, List.head?_cons, Option.mem_some_iff] using member
        subst phase
        have positioned := frontier.positioned
        rw [phases] at positioned
        exact (positioned.1.2 event).mp (saved event candidate installed)
  · intro phase member event candidate installed
    cases phases : state.phases with
    | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
    | cons current rest =>
        have same : phase = current := by
          symm
          simpa only [phases, List.head?_cons, Option.mem_some_iff] using member
        subst phase
        have positioned := frontier.positioned
        rw [phases] at positioned
        exact positioned.2.2 event (active event candidate installed)
  · exact stamped

end PhaseRuntimeState

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Current-interval accepted bindings have actual current-attempt owner outputs. -/
def LiveBindingStamp (execution : (app).Execution) : Prop :=
  BindingStamp (fun who => (app).outputs (execution.recall who)) execution.application.attempt
    execution.application.current.native

theorem liveBindingStamp_respond (execution : (app).Execution)
    (who : Player) (response : (app).Action) (valid : LiveBindingStamp runtime leaks execution) :
    LiveBindingStamp runtime leaks (execution.respond (app) who response) := by
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
          change (submitStep (material.call.register execution.application.current.native who)
            who material.call.packet).accepted = _
          rw [submitStep_accepted, Submission.register_accepted]

/-- Raw native acceptance preserves every typed binding meaning, including
fresh candidates whose freeze merely changes one failure representation. -/
theorem raw_handle_bindingResult (state next : State graph)
    (message : Message Player (Payload graph))
    (accepted : EventGraphRuntime.handle runtime state message = some next)
    (candidate : Handle graph) (payload : L.Ty) :
    next.bindingResult candidate payload = state.bindingResult candidate payload := by
  rcases handle_tables_cases runtime state next message accepted with
    ⟨event, selected, call, candidates, table, owner⟩ | ⟨table, candidates⟩
  · unfold State.bindingResult
    rw [candidates]
    by_cases same : candidate = selected
    · subst candidate
      rw [CommitmentCandidates.lookup_freeze_self]
      cases state.candidates.lookup selected <;> rfl
    · rw [CommitmentCandidates.lookup_freeze_other _ _ _ same]
  · unfold State.bindingResult
    rw [candidates]

/-- Native acceptance records the real authored packet before phase normalization. -/
theorem raw_handle_bindingStamp (execution : (app).Execution)
    (native : State graph) (message : Message Player (CommitAttemptPacket graph))
    (valid : LiveBindingStamp runtime leaks execution)
    (issued : execution.Issued (app) message)
    (current : message.payload.attempt = execution.application.attempt)
    (accepted : EventGraphRuntime.handle runtime execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native) :
    BindingStamp (fun who => (app).outputs (execution.recall who))
      execution.application.attempt native := by
  rcases handle_tables_cases runtime execution.application.current.native native _ accepted with
    ⟨event, candidate, call, _, table, owner⟩ | ⟨table, _⟩
  · intro field handle installed
    change native.accepted (.inr field) = some handle at installed
    rw [table] at installed
    by_cases same : field = event
    · subst field
      rw [Function.update_self] at installed
      cases Option.some.inj installed
      obtain ⟨entry, present, material, transmission, emitted, packet⟩ := issued
      exact Or.inr ⟨message, List.mem_filterMap.mpr ⟨entry,
        by simpa only [Message.sender, owner] using present, emitted⟩, owner.symm, call, current⟩
    · rw [Function.update_of_ne (by simpa using same)] at installed
      exact valid field handle installed
  · exact valid.copy table

private theorem liveBindingStamp_handle (execution : (app).Execution)
    (next : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (valid : LiveBindingStamp runtime leaks execution)
    (record : execution.application.ExclusionRecord)
    (issued : execution.Issued (app) message)
    (handled : execution.application.handle runtime message = some next) :
    LiveBindingStamp runtime leaks {execution with application := next} := by
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
    apply PhaseRuntimeState.normalize_bindingStamp _ _
      (PhaseRuntimeState.raw_handle_frontier runtime _ record.frontier _ native authorized accepted)
      record.saved (record.active.step (completionStep_handle runtime _ native _ accepted))
    exact raw_handle_bindingStamp runtime leaks execution native message valid issued current
      accepted
  · cases handled

theorem liveBindingStamp_environment (execution next : (app).Execution)
    (command : (app).Command) (valid : LiveBindingStamp runtime leaks execution)
    (record : execution.application.ExclusionRecord) (origins : execution.Provenance (app))
    (reached : next ∈ (execution.environmentStep (app) command).support) :
    LiveBindingStamp runtime leaks next := by
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
          change LiveBindingStamp runtime leaks {execution with
            application := ((app).handle execution.application message).getD execution.application}
          cases accepted : (app).handle execution.application message with
          | none => exact valid
          | some state =>
              exact liveBindingStamp_handle runtime leaks execution state message valid record
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
        apply PhaseRuntimeState.normalize_bindingStamp _ _
          (PhaseRuntimeState.raw_environment_frontier runtime _ record.frontier _ native allowed
            nativeMoved) record.saved
          (record.active.step (completionStep_environmentStep runtime _ native command nativeMoved))
        exact valid.copy (environmentStep_tables runtime _ _ command nativeMoved).1
      · rw [PMF.mem_support_pure_iff] at changed
        subst state
        exact valid

/-- At every actual raw initialized history, every accepted binding in the live
phase is certified by an actual signed output in that exact attempt namespace. -/
theorem phaseLiveBindingStamp_history (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) : LiveBindingStamp runtime leaks control.execution := by
  have invariant : (app).ServiceInvariant scheduler (fun execution =>
      LiveBindingStamp runtime leaks execution ∧ execution.application.ExclusionRecord ∧
        execution.Provenance (app)) := {
    respond := fun execution who response valid =>
      ⟨liveBindingStamp_respond runtime leaks execution who response valid.1,
        (phaseApplication_exclusionRecord runtime leaks).respond execution who response valid.2.1,
        (app).respond_provenance execution who response valid.2.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨liveBindingStamp_environment runtime leaks execution next command valid.1 valid.2.1
          valid.2.2 reached,
        (phaseApplication_exclusionRecord runtime leaks).environmentStep execution next command
          valid.2.1 reached,
        (app).environment_provenance execution next command valid.2.2 reached⟩ }
  exact (invariant.history _ horizon (by
    intro state supported
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨?_, PhaseRuntimeState.initial_exclusionRecord plan draw,
      MessageNetwork.Satisfies.empty⟩
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
      cases impossible) trace).1

end Vegas.EventGraphRuntime
