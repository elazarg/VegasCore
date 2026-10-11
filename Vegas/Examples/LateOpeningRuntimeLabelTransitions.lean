/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLabelSymmetry

/-! # Authenticated raw operations under initial private-label replacement -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeLabelTransitions

open Vegas.EventGraphRuntime Interaction
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLabelSymmetry
open LateOpeningRuntimeReadout LateOpeningRuntimeBobService

theorem register_replace (submission : Submission nativeGraph)
    (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs) (who : Player) :
    replaceStateInputs (submission.register state who) inputs =
      submission.register (replaceStateInputs state inputs) who := by
  rcases submission with ⟨packet, opening⟩
  cases packet with
  | malformed raw | opening event handle raw => rfl
  | commitment event handle =>
      rcases handle with ⟨owner, slot⟩
      cases slot <;> cases opening <;> simp only [Submission.register]
      all_goals first | rfl | (split <;> rfl)

theorem emit_replace (submission : WitnessedSubmission nativeGraph)
    (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = state.config.inputs ⟨0, by decide⟩)
    (who : Player) (known : List (Message Player (WitnessedPacket nativeGraph))) :
    submission.emit (replaceStateInputs state inputs) who known =
      submission.emit state who known := by
  have publicEq := congrArg PlayerView.publicView (replaceStateInputs_bob_view state inputs bit)
  change (replaceStateInputs state inputs).publicView = state.publicView at publicEq
  unfold WitnessedSubmission.emit
  rw [publicEq]
  rfl

theorem submit_replace (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs)
    (who : Player) (submission : WitnessedSubmission nativeGraph) :
    replaceStateInputs (app.submit state who submission) inputs =
      app.submit (replaceStateInputs state inputs) who submission := by
  change replaceStateInputs (submitStep (submission.call.register state who)
    who submission.call.packet) inputs = _
  rw [replaceStateInputs_submitStep, register_replace]
  rfl

theorem reactive_handle_replace (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = state.config.inputs ⟨0, by decide⟩)
    (message : Message Player (WitnessedPacket nativeGraph)) :
    (app.handle state message).map (fun next => replaceStateInputs next inputs) =
      app.handle (replaceStateInputs state inputs) message := by
  simp only [reactiveApplication_handle]
  split
  · exact replaceStateInputs_handle state inputs bit ⟨message.id, message.payload.call⟩
  · rfl

theorem expire_replace (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs) (event : nativeGraph.EventId) :
    (environmentStep LateOpeningRuntimeService.runtime state (.expire event)).map
        (fun next => replaceStateInputs next inputs) =
      environmentStep LateOpeningRuntimeService.runtime
        (replaceStateInputs state inputs) (.expire event) := by
  by_cases ready : state.config.cut.Ready event
  · cases activated : state.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated _ state event ready activated,
          environmentStep_expire_of_not_activated _ (replaceStateInputs state inputs)
            event ready activated, PMF.pure_map]
    | some entered =>
        by_cases due : LateOpeningRuntimeService.runtime.deadline event ≤ state.clock - entered
        · change Fin 3 at event
          fin_cases event
          · rw [environmentStep_expire_resolve_eq _ state aliceEvent ready entered activated due
              alice .bool aliceBinding [] rfl rfl rfl,
              environmentStep_expire_resolve_eq _ (replaceStateInputs state inputs)
                aliceEvent ready entered activated due alice .bool aliceBinding [] rfl rfl rfl,
              PMF.pure_map, replaceStateInputs_complete]
          · rw [environmentStep_expire_bind_eq _ state bobBindEvent ready entered activated due
              bob (.range 0 5) rfl rfl rfl,
              environmentStep_expire_bind_eq _ (replaceStateInputs state inputs)
                bobBindEvent ready entered activated due bob (.range 0 5) rfl rfl rfl,
              PMF.pure_map, replaceStateInputs_complete]
          · rw [environmentStep_expire_resolve_eq _ state bobRevealEvent ready entered activated due
              bob (.range 0 5) bobBinding bobChecks rfl rfl rfl,
              environmentStep_expire_resolve_eq _ (replaceStateInputs state inputs)
                bobRevealEvent ready entered activated due
                bob (.range 0 5) bobBinding bobChecks rfl rfl rfl,
              PMF.pure_map, replaceStateInputs_complete]
        · rw [environmentStep_expire_of_not_due _ state event ready entered activated due,
            environmentStep_expire_of_not_due _ (replaceStateInputs state inputs)
              event ready entered activated due, PMF.pure_map]
  · rw [environmentStep_expire_of_not_ready _ state event ready,
      environmentStep_expire_of_not_ready _ (replaceStateInputs state inputs) event ready,
      PMF.pure_map]

private theorem sample_stutters (state : Vegas.EventGraphRuntime.State nativeGraph)
    (event : nativeGraph.EventId) :
    environmentStep LateOpeningRuntimeService.runtime state (.executeSample event) =
      PMF.pure state := by
  by_cases ready : state.config.cut.Ready event
  · apply environmentStep_executeSample_of_nonsample _ state event ready
    intro payload law outputEq codeEq
    change Fin 3 at event
    fin_cases event <;> cases outputEq
  · exact environmentStep_executeSample_of_not_ready _ state event ready

theorem environment_replace (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs) (command : EnvironmentCommand nativeGraph) :
    (environmentStep LateOpeningRuntimeService.runtime state command).map
        (fun next => replaceStateInputs next inputs) =
      environmentStep LateOpeningRuntimeService.runtime
        (replaceStateInputs state inputs) command := by
  cases command with
  | advanceClock =>
      rw [environmentStep, environmentStep, PMF.pure_map]
      rfl
  | executeSample event =>
      rw [sample_stutters, sample_stutters, PMF.pure_map]
  | expire event => exact expire_replace state inputs event

theorem rawMenu_actions_eq_of_packets (who : Player) (first second : List app.PlayerEntry)
    (view other : app.PlayerView) (outputs : app.outputs first = app.outputs second)
    (messages : view.messages = other.messages) :
    rawMenu.actions who first view = rawMenu.actions who second other := by
  simp only [LateOpeningRuntimeService.rawMenu, MessageBounds.rawMenu,
    ReactiveApplication.ResponseMenu.fromSubmissions,
    ReactiveApplication.ResponseMenu.knownPackets, outputs, messages]

end Vegas.Examples.LateOpeningRuntimeLabelTransitions
