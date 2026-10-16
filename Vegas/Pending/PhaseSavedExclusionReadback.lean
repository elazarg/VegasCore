/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseArchivedExclusions

/-! # Saved exclusions read from archived and current public failure records -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace State

/-- All earlier completed events retain their exact public failure verdict. -/
structure PublicFailureExtension (before after : State graph) : Prop where
  completed : before.config.cut.completed ⊆ after.config.cut.completed
  failures : ∀ event ∈ before.config.cut.completed,
    after.PublicFailure event ↔ before.PublicFailure event

theorem PublicFailureExtension.refl (state : State graph) :
    state.PublicFailureExtension state := ⟨fun _ member => member, fun _ _ => Iff.rfl⟩

theorem PublicFailureExtension.trans {first middle last : State graph}
    (before : first.PublicFailureExtension middle) (after : middle.PublicFailureExtension last) :
    first.PublicFailureExtension last :=
  ⟨before.completed.trans after.completed, fun event member =>
    (after.failures event (before.completed member)).trans (before.failures event member)⟩

theorem PublicFailureExtension.of_copy {before after : State graph}
    (config : after.config = before.config) (accepted : after.accepted = before.accepted) :
    before.PublicFailureExtension after := by
  refine ⟨fun event member => by simpa only [config] using member, fun event _ => ?_⟩
  exact PublicFailure.congr event (by rw [config]) (by rw [config]) (by rw [accepted])

end State

theorem CompletionStep.publicFailureExtension {before after : State graph}
    (step : CompletionStep before after) : before.PublicFailureExtension after := by
  rcases step with ⟨config, accepted, _⟩ |
    ⟨event, ready, action, supported, _activated, acceptedOnly⟩
  · exact State.PublicFailureExtension.of_copy config accepted
  · refine ⟨?_, ?_⟩
    · intro query completed
      rw [before.config.step_cut event ready action after.config supported,
        EventOrder.Cut.mem_complete]
      exact Or.inr completed
    · intro query completed
      apply State.PublicFailure.of_step_of_ne supported (fun field changed =>
        (acceptedOnly field changed).2)
      intro same
      exact ready.1 (same ▸ completed)

namespace RuntimePhase

variable [DecidableEq Player]

theorem drainFuel_publicFailureExtension (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) :
    state.native.PublicFailureExtension (phase.drainFuel fuel state).native := by
  induction fuel generalizing state with
  | zero => exact State.PublicFailureExtension.refl _
  | succ fuel ih =>
    unfold drainFuel
    split
    · rename_i pending
      let event := Classical.choose pending
      have eligible := (Classical.choose_spec pending).2
      obtain ⟨owner, acting, _excluded⟩ := eligible.owned
      have step : CompletionStep state.native (state.completeAutomatic event eligible).native :=
        SuffixExclusionRecord.failureCompletionStep state.native event eligible.1 acting
      exact step.publicFailureExtension.trans (ih _)
    · exact State.PublicFailureExtension.refl _

theorem drain_publicFailureExtension (phase : RuntimePhase graph) (state : RecoveryState graph) :
    state.native.PublicFailureExtension (phase.drain state).native :=
  phase.drainFuel_publicFailureExtension _ _

end RuntimePhase

variable [DecidableEq Player]

namespace PhaseRuntimeState

/-- The live native state retains the saved prefix's public failure verdicts. -/
def PublicFailureCheckpoint (state : PhaseRuntimeState graph) : Prop :=
  state.entry.native.PublicFailureExtension state.current.native

theorem settle_publicFailureCheckpoint (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (valid : entry.native.PublicFailureExtension current.native) :
    (settle phases generation entry current retired).PublicFailureCheckpoint := by
  induction phases generalizing generation entry current retired with
  | nil => exact valid
  | cons phase remaining ih =>
    have drained := valid.trans (phase.drain_publicFailureExtension current)
    simp only [settle]
    split
    · split
      · split
        · exact phase.drain_publicFailureExtension _
        · exact ih _ _ _ _ (State.PublicFailureExtension.refl _)
      · exact ih _ _ _ _ (State.PublicFailureExtension.refl _)
    · exact drained

theorem initial_publicFailureCheckpoint (plan : RuntimePhasePlan graph)
    (inputs : graph.Inputs) : (initial plan inputs).PublicFailureCheckpoint :=
  settle_publicFailureCheckpoint _ _ _ _ _ (State.PublicFailureExtension.refl _)

end PhaseRuntimeState

theorem phaseApplication_publicFailureCheckpoint (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.PublicFailureCheckpoint where
  submit state who material valid := by
    have same := (submitStep_publicView (material.call.register state.current.native who) who
      material.call.packet).trans (material.call.register_facts who state.current.native).2
    have config : (state.current.submit who material).native.config =
        state.current.native.config := by
      rw [RecoveryState.submit, submitStep_config, (material.call.register_facts who _).1]
    exact valid.trans (State.PublicFailureExtension.of_copy config
      (congrArg PublicView.accepted same))
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_publicFailureCheckpoint
      exact valid.trans (completionStep_handle runtime _ native _ handled).publicFailureExtension
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_publicFailureCheckpoint
      exact valid.trans
        (completionStep_environmentStep runtime _ native command supported).publicFailureExtension
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

theorem phasePublicFailureCheckpoint_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.PublicFailureCheckpoint :=
  (phaseApplication_publicFailureCheckpoint runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_publicFailureCheckpoint plan draw) trace

namespace State

variable [Fintype Player]

/-- Owners of public failures strictly below a saved source frontier. -/
def failureOwnersBefore (state : State graph) (low : Nat) : Finset Player := by
  classical
  exact Finset.univ.filter fun owner => ∃ event : graph.EventId,
    event.val < low ∧ graph.actor? event = some owner ∧ state.PublicFailure event

theorem failureOwnersBefore_congr {first second : State graph}
    (same : first.publicView = second.publicView) (low : Nat) :
    first.failureOwnersBefore low = second.failureOwnersBefore low := by
  classical
  ext owner
  simp only [failureOwnersBefore, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun event => and_congr_right fun _ =>
    and_congr_right fun _ => PublicFailure.of_publicView_eq same event

end State

variable [Fintype Player]

namespace PhaseRuntimeState

/-- Equal public attempt archives have the same excluded-owner witnesses;
their hidden binding values do not enter the failure predicate. -/
theorem archivedFailureOwners_eq_of_publicViews_eq
    (first second : List (RetiredCommitAttempt graph))
    (same : first.map (fun record => (record.attempt, record.state.publicView)) =
      second.map (fun record => (record.attempt, record.state.publicView))) :
    archivedFailureOwners first = archivedFailureOwners second := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => rfl
    | cons record rest => cases same
  | cons record rest ih =>
    cases second with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at same
    | cons other more =>
      have pairs := List.cons.inj same
      have publicEq := congrArg Prod.snd pairs.1
      have failures : record.state.failureOwners = other.state.failureOwners := by
        classical
        ext owner
        simp only [State.failureOwners, Finset.mem_filter, Finset.mem_univ, true_and]
        exact exists_congr fun event => and_congr_right fun _ =>
          State.PublicFailure.of_publicView_eq publicEq event
      change record.state.failureOwners ∪ archivedFailureOwners rest =
        other.state.failureOwners ∪ archivedFailureOwners more
      rw [failures, ih more pairs.2]

/-- At an installed phase, saved exclusions are exactly archived failure
owners together with current public failures strictly before the phase. In
particular, a new expiry inside the phase cannot enter the saved source set. -/
theorem saved_excluded_eq_public_failures {state : PhaseRuntimeState graph}
    (archives : state.ArchivedExclusions) (checkpoint : state.PublicFailureCheckpoint)
    (frontier : state.Frontier) (phase : RuntimePhase graph)
    (remaining : List (RuntimePhase graph)) (installed : state.phases = phase :: remaining) :
    state.entry.excluded = archivedFailureOwners state.retired ∪
      state.current.native.failureOwnersBefore state.attempt.phase := by
  have saved := frontier.positioned
  rw [installed] at saved
  rw [archives.saved_eq]
  apply congrArg (archivedFailureOwners state.retired ∪ ·)
  classical
  ext owner
  simp only [State.failureOwners, State.failureOwnersBefore, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have low : state.attempt.phase = phase.low := by simp only [attempt, installed, List.head?_cons,
    Option.map_some, Option.getD_some]
  rw [low]
  constructor
  · rintro ⟨event, acting, failed⟩
    have completed := failed.completed
    exact ⟨event, (saved.1.2 event).mp completed, acting,
      (checkpoint.failures event completed).mpr failed⟩
  · rintro ⟨event, earlier, acting, failed⟩
    exact ⟨event, acting, (checkpoint.failures event ((saved.1.2 event).mpr earlier)).mp failed⟩

/-- The same public native view determines the saved source exclusion set at
an installed phase. Current in-phase failures cannot change that set. -/
theorem saved_excluded_eq_of_publicView_eq {first second : PhaseRuntimeState graph}
    (firstArchives : first.ArchivedExclusions) (secondArchives : second.ArchivedExclusions)
    (firstCheckpoint : first.PublicFailureCheckpoint)
    (secondCheckpoint : second.PublicFailureCheckpoint)
    (firstFrontier : first.Frontier) (secondFrontier : second.Frontier)
    (firstPhase secondPhase : RuntimePhase graph)
    (firstRest secondRest : List (RuntimePhase graph))
    (firstInstalled : first.phases = firstPhase :: firstRest)
    (secondInstalled : second.phases = secondPhase :: secondRest)
    (same : first.publicView = second.publicView) :
    first.entry.excluded = second.entry.excluded := by
  rw [saved_excluded_eq_public_failures firstArchives firstCheckpoint firstFrontier
    firstPhase firstRest firstInstalled,
    saved_excluded_eq_public_failures secondArchives secondCheckpoint secondFrontier
      secondPhase secondRest secondInstalled]
  have archives := archivedFailureOwners_eq_of_publicViews_eq first.retired second.retired
    (congrArg PhasePublicView.retired same)
  have low := congrArg (fun view : PhasePublicView graph => view.attempt.phase) same
  change first.attempt.phase = second.attempt.phase at low
  have native := congrArg PhasePublicView.native same
  have current : first.current.native.failureOwnersBefore first.attempt.phase =
      second.current.native.failureOwnersBefore second.attempt.phase := by
    rw [← low]
    exact State.failureOwnersBefore_congr native _
  exact congrArg₂ (fun left right : Finset Player => left ∪ right) archives current

end PhaseRuntimeState

omit [Fintype Player] in
/-- Actual initialized histories with the same public view and an installed
phase have the same saved source exclusion set, without a supplied decoder or
saved-exclusion equality premise. -/
theorem phase_saved_excluded_eq_of_publicView_eq [Finite Player]
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some second))
    (firstLive : first.execution.application.phases ≠ [])
    (secondLive : second.execution.application.phases ≠ [])
    (same : first.execution.application.publicView = second.execution.application.publicView) :
    first.execution.application.entry.excluded = second.execution.application.entry.excluded := by
  let := Fintype.ofFinite Player
  cases firstInstalled : first.execution.application.phases with
  | nil => exact (firstLive firstInstalled).elim
  | cons firstPhase firstRest =>
    cases secondInstalled : second.execution.application.phases with
    | nil => exact (secondLive secondInstalled).elim
    | cons secondPhase secondRest =>
      exact PhaseRuntimeState.saved_excluded_eq_of_publicView_eq
        (phaseArchivedExclusions_history runtime leaks plan inputs horizon scheduler firstTrace)
        (phaseArchivedExclusions_history runtime leaks plan inputs horizon scheduler secondTrace)
        (phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon scheduler
          firstTrace)
        (phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon scheduler
          secondTrace)
        (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
          firstTrace).frontier
        (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler
          secondTrace).frontier
        firstPhase secondPhase firstRest secondRest firstInstalled secondInstalled same

end Vegas.EventGraphRuntime
