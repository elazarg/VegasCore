/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalAccepted
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveServiceInvariant

/-! # Initialized true publication actions have actual submitted openings -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def ExecutionOpeningOrigins (execution : (app).Execution) : Prop :=
  OpeningOrigins execution.network.inputs execution.application.current.native ∧
    OpeningOrigins execution.network.inputs execution.application.entry.native

theorem openingOrigins_respond (execution : (app).Execution) (owner : Player)
    (response : (app).Action) (valid : ExecutionOpeningOrigins runtime leaks execution) :
    ExecutionOpeningOrigins runtime leaks (execution.respond (app) owner response) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact valid
  | some material =>
      let next := execution.application.submit owner material
      let packet := (app).packet next owner (execution.network.known owner) material
      let message : Message Player (app).Payload :=
        ⟨(owner, execution.network.nextSerial owner), packet⟩
      have contains : execution.network.inputs ⊆ execution.network.inputs ++ [message] :=
        List.subset_append_left _ _
      have configEq : next.current.native.config = execution.application.current.native.config := by
        change (submitStep (material.call.register execution.application.current.native owner)
          owner material.call.packet).config = _
        rw [submitStep_config, (material.call.register_facts owner _).1]
      change OpeningOrigins (execution.network.inputs ++ [message]) next.current.native ∧
        OpeningOrigins (execution.network.inputs ++ [message]) next.entry.native
      exact ⟨(valid.1.mono contains).copy (congrArg Config.history configEq),
        valid.2.mono contains⟩

private theorem openingOrigins_handle (execution : (app).Execution)
    (next : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (present : message ∈ execution.network.inputs)
    (valid : ExecutionOpeningOrigins runtime leaks execution)
    (handled : execution.application.handle runtime message = some next) :
    OpeningOrigins execution.network.inputs next.current.native ∧
      OpeningOrigins execution.network.inputs next.entry.native := by
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · obtain ⟨native, accepted, rfl⟩ := Option.map_eq_some_iff.mp handled
    exact settle_openingOrigins execution.network.inputs _ _ _ _ _ valid.2
      (valid.1.handle runtime message present native accepted)
  · cases handled

theorem openingOrigins_environment (execution next : (app).Execution)
    (command : (app).Command) (valid : ExecutionOpeningOrigins runtime leaks execution)
    (origins : execution.Provenance (app)) (recalled : execution.InputRecall (app))
    (reached : next ∈ (execution.environmentStep (app) command).support) :
    ExecutionOpeningOrigins runtime leaks next := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate owner =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact valid
      | some message =>
          have present := ((app).retained_envelopes_mem_inputs execution origins recalled).lookup
            id message found
          change ExecutionOpeningOrigins runtime leaks {execution with
            application := ((app).handle execution.application message).getD execution.application}
          cases accepted : (app).handle execution.application message with
          | none => exact valid
          | some state =>
              exact openingOrigins_handle runtime leaks execution state message present valid
                accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ (execution.application.environment runtime command).support at changed
      unfold PhaseRuntimeState.environment at changed
      split at changed
      · obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
        exact settle_openingOrigins execution.network.inputs _ _ _ _ _ valid.2
          (valid.1.environment runtime command native nativeMoved)
      · cases (PMF.mem_support_pure_iff _ _).mp changed
        exact valid

/-- A true completion is authenticated even when its guard failed and its
owner was permanently excluded in that same inclusion transition. -/
theorem openingOrigins_history (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some current)) :
    ExecutionOpeningOrigins runtime leaks current.execution := by
  have invariant : (app).ServiceInvariant scheduler (fun execution =>
      ExecutionOpeningOrigins runtime leaks execution ∧ execution.Provenance (app) ∧
        execution.InputRecall (app)) := {
    respond := fun execution owner action valid =>
      ⟨openingOrigins_respond runtime leaks execution owner action valid.1,
        (app).respond_provenance execution owner action valid.2.1,
        (app).respond_inputRecall execution owner action valid.2.2⟩
    environment := fun execution next command valid _ reached =>
      ⟨openingOrigins_environment runtime leaks execution next command valid.1 valid.2.1 valid.2.2
          reached,
        (app).environment_provenance execution next command valid.2.1 reached,
        (app).environment_inputRecall execution next command valid.2.2 reached⟩ }
  exact (invariant.history _ horizon (by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨?_, MessageNetwork.Satisfies.empty, (app).initial_inputRecall _⟩
    apply settle_openingOrigins
    all_goals intro completion recorded; cases recorded) trace).1

end Vegas.EventGraphRuntime.PhaseProposal
