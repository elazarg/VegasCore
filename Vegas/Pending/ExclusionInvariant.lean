/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionApplication
import Interaction.ReactiveInvariant

/-! # Lifetime invariants of the permanent-exclusion runtime -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace State

omit [DecidableEq Player] in
theorem completeFailure_activated (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    (state.completeFailure event ready).activatedAt =
      refreshActivated (state.completeFailure event ready).config state.clock
        state.activatedAt := by
  cases view : nodeView graph event with
  | bind _ _ _ _ => simp only [completeFailure, view, complete]
  | resolve _ _ _ _ _ _ => simp only [completeFailure, view, complete]
  | sample payload law outputEq codeEq =>
      have actorEq : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [actorEq] at acting
      cases acting

omit [DecidableEq Player] in
theorem completeFailure_invariant {state : State graph} {inputs : graph.Inputs}
    (valid : state.Invariant inputs) (event : graph.EventId)
    (ready : state.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    (state.completeFailure event ready).Invariant inputs := by
  obtain ⟨action, realized⟩ := state.completeFailure_step event ready acting
  have completed := valid.refreshStep event ready action _ realized
  apply completed.copy
  · rfl
  · exact (state.completeFailure_tables event ready).2.2
  · exact state.completeFailure_activated event ready acting

end State

namespace RecoveryState

theorem drainFuel_invariant (fuel : Nat) (state : RecoveryState graph) {inputs : graph.Inputs}
    (valid : state.native.Invariant inputs) :
    (drainFuel fuel state).native.Invariant inputs := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        obtain ⟨owner, acting, _⟩ := (Classical.choose_spec pending).owned
        exact ih _ (State.completeFailure_invariant valid _
          (Classical.choose_spec pending).1 acting)
      · exact valid

theorem drain_invariant (state : RecoveryState graph) {inputs : graph.Inputs}
    (valid : state.native.Invariant inputs) : state.drain.native.Invariant inputs :=
  drainFuel_invariant _ _ valid

/-- Every externally visible recovery state has coherent native metadata and
no ready event belonging to an excluded owner. -/
structure Invariant (inputs : graph.Inputs) (state : RecoveryState graph) : Prop where
  native : state.native.Invariant inputs
  quiescent : ∀ event, ¬ state.AutomaticReady event

namespace Invariant

variable {state : RecoveryState graph} {inputs : graph.Inputs}

theorem initial (inputs : graph.Inputs) :
    Invariant inputs (⟨State.initial inputs, ∅⟩ : RecoveryState graph) := by
  refine ⟨State.initial_invariant inputs, ?_⟩
  intro event eligible
  obtain ⟨owner, _, member⟩ := eligible.owned
  exact Finset.notMem_empty _ member

omit [DecidableEq Player] in
theorem excluded_not_ready (valid : state.Invariant inputs) {event : graph.EventId}
    {owner : Player} (excluded : owner ∈ state.excluded)
    (acting : graph.actor? event = some owner) : ¬ state.native.config.cut.Ready event := by
  intro ready
  apply valid.quiescent event
  exact ⟨ready, by simpa only [acting] using excluded⟩

theorem submit (valid : state.Invariant inputs) (who : Player)
    (submission : WitnessedSubmission graph) : (state.submit who submission).Invariant inputs := by
  refine ⟨?_, state.submit_quiescent who submission valid.quiescent⟩
  apply valid.native.copy
  · change (submitStep _ who _).config = _
    rw [submitStep_config, (submission.call.register_facts who state.native).1]
  · have same := (submitStep_publicView (submission.call.register state.native who) who
        submission.call.packet).trans (submission.call.register_facts who state.native).2
    exact congrArg PublicView.clock same
  · have same := (submitStep_publicView (submission.call.register state.native who) who
        submission.call.packet).trans (submission.call.register_facts who state.native).2
    exact congrArg PublicView.activatedAt same

theorem handle (valid : state.Invariant inputs) (runtime : EventGraphRuntime graph)
    (message : Message Player (WitnessedPacket graph)) (next : RecoveryState graph)
    (accepted : state.handle runtime message = some next) : next.Invariant inputs := by
  unfold RecoveryState.handle at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have first := handle_invariant runtime state.native native
        ⟨message.id, message.payload.call⟩ valid.native rawAccepted
      exact ⟨drain_invariant _ first, drain_quiescent _⟩
    · cases accepted

theorem environment (valid : state.Invariant inputs) (runtime : EventGraphRuntime graph)
    (command : EnvironmentCommand graph) (next : RecoveryState graph)
    (realized : next ∈ (state.environment runtime command).support) : next.Invariant inputs := by
  rw [RecoveryState.environment, PMF.support_map] at realized
  obtain ⟨native, reached, rfl⟩ := realized
  have first := environmentStep_invariant runtime state.native native command valid.native reached
  exact ⟨drain_invariant _ first, drain_quiescent _⟩

end Invariant
end RecoveryState

/-- Generic reactive history invariants apply to the concrete recovery handlers. -/
theorem recoveryApplication_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) :
    (recoveryApplication runtime leaks).Invariant (RecoveryState.Invariant inputs) where
  submit _ who material valid := valid.submit who material
  handle _ message next valid accepted := valid.handle runtime message next accepted
  environment _ command next valid realized := valid.environment runtime command next realized

/-- Permanent exclusions can only grow under actual recovery execution steps. -/
theorem recoveryApplication_exclusion_monotone (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (recoveryApplication runtime leaks).StepRelation
      (fun before after => before.excluded ⊆ after.excluded) where
  refl _ := fun _ member => member
  submit _ _ _ := fun _ member => member
  handle state message next accepted := state.handle_excluded_subset runtime next message accepted
  environment state command next realized :=
    state.environment_excluded_subset runtime next command realized

/-- Every actual history from a coherent native initial law automatically
suppresses all subsequent readiness of permanently excluded owners. -/
theorem recoveryApplication_history_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (State graph))
    (initialized : ∀ native ∈ initial.support, native.Invariant native.config.inputs)
    (horizon : Nat) (scheduler : (recoveryApplication runtime leaks).Scheduler)
    (control : (recoveryApplication runtime leaks).Control)
    (trace : ((recoveryApplication runtime leaks).protocol
      (initial.map fun native => (⟨native, ∅⟩ : RecoveryState graph)) horizon scheduler).Trace
        (some control)) :
    ∃ inputs, control.execution.application.Invariant inputs := by
  let app := recoveryApplication runtime leaks
  have preserved : app.Invariant (fun state => ∃ inputs, state.Invariant inputs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro state who material valid
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, valid.submit who material⟩
    · intro state message next valid accepted
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, valid.handle runtime message next accepted⟩
    · intro state command next valid realized
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, valid.environment runtime command next realized⟩
  apply preserved.history _ horizon scheduler ?_ trace
  intro state member
  rw [PMF.support_map] at member
  obtain ⟨native, member, rfl⟩ := member
  refine ⟨native.config.inputs, initialized native member, ?_⟩
  intro event eligible
  obtain ⟨owner, _, impossible⟩ := eligible.owned
  exact Finset.notMem_empty _ impossible

end Vegas.EventGraphRuntime
