/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLabelTransitions

/-! # Recalled native observations and actual transitions under label replacement

Input replacement changes only Alice's observed ordinary private label, including
her recorded before-observations. Raw actions, authored envelopes, network state,
receipts, candidate meanings and environment recall remain intact. Actual responses
and all environment commands commute with this replacement; the full raw response
menu is unchanged. The original independent input prior is label-permutation invariant.

A complete legal protocol-history bijection and its conditional reference-law
consequences require a further lifting of these transition laws.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeLabelHistories

open Vegas.EventGraph Vegas.EventGraphRuntime Interaction
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
open LateOpeningRuntimeLabelSymmetry LateOpeningRuntimeLabelTransitions

def replaceLocalView (view : Vegas.EventGraphRuntime.PlayerView nativeGraph)
    (inputs : nativeGraph.Inputs) : Vegas.EventGraphRuntime.PlayerView nativeGraph :=
  if view.who = alice then
    { view with
      observation := { view.observation with
        store := Function.update view.observation.store (.inl labelInput)
          (some (inputs labelInput)) } }
  else view

theorem alice_observe_replace (config : nativeGraph.Config) (inputs : nativeGraph.Inputs)
    (bit : inputs aliceInput = config.inputs aliceInput) :
    nativeGraph.playerObserve alice (replaceInputs config inputs) =
      { (nativeGraph.playerObserve alice config) with
        store :=
        Function.update (nativeGraph.playerObserve alice config).store
          (.inl labelInput) (some (inputs labelInput)) } := by
  apply PlayerObservation.ext
  · rfl
  · funext field
    dsimp only
    change nativeGraph.playerStore alice (replaceInputs config inputs).store field = _
    by_cases label : field = .inl labelInput
    · subst field
      simp only [Function.update_self]
      exact nativeGraph.playerStore_own_privateInput _ _ alice (.range 0 2) rfl
    · rw [Function.update_of_ne label]
      unfold playerStore
      rw [replaceInputs_store_eq config inputs bit field label]
      rfl
  · rfl

theorem local_observe_replace (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs) (bit : inputs aliceInput = state.config.inputs aliceInput)
    (who : Player) :
    (replaceStateInputs state inputs).playerView who =
      replaceLocalView (state.playerView who) inputs := by
  have publicEq := congrArg Vegas.EventGraphRuntime.PlayerView.publicView
    (replaceStateInputs_bob_view state inputs bit)
  change (replaceStateInputs state inputs).publicView = state.publicView at publicEq
  fin_cases who
  · change (replaceStateInputs state inputs).playerView alice =
      replaceLocalView (state.playerView alice) inputs
    unfold replaceLocalView
    rw [ite_eq_left (show (state.playerView alice).who = alice from rfl)]
    simp only [Vegas.EventGraphRuntime.State.playerView]
    rw [publicEq]
    change (⟨alice, state.publicView,
      nativeGraph.playerObserve alice (replaceInputs state.config inputs),
      fun slot => state.candidates.lookup (alice, slot)⟩ :
        Vegas.EventGraphRuntime.PlayerView nativeGraph) = _
    rw [alice_observe_replace state.config inputs bit]
  · change (replaceStateInputs state inputs).playerView bob =
      replaceLocalView (state.playerView bob) inputs
    rw [replaceStateInputs_bob_view state inputs bit]
    simp [replaceLocalView, Vegas.EventGraphRuntime.State.playerView]

def replaceView (view : app.PlayerView) (inputs : nativeGraph.Inputs) : app.PlayerView :=
  { view with application := replaceLocalView view.application inputs }

def replaceEntry (entry : app.PlayerEntry) (inputs : nativeGraph.Inputs) : app.PlayerEntry :=
  { entry with beforeView := replaceView entry.beforeView inputs }

def replaceExecution (execution : app.Execution) (inputs : nativeGraph.Inputs) : app.Execution :=
  { execution with
    application := replaceStateInputs execution.application inputs
    «recall» := fun who => (execution.recall who).map (fun entry => replaceEntry entry inputs) }

theorem observe_replace (execution : app.Execution) (inputs : nativeGraph.Inputs)
    (bit : inputs aliceInput = execution.application.config.inputs aliceInput) (who : Player) :
    (replaceExecution execution inputs).observe app who =
      replaceView (execution.observe app who) inputs := by
  change (⟨_, (replaceStateInputs execution.application inputs).playerView who, _⟩ :
    app.PlayerView) = _
  rw [local_observe_replace execution.application inputs bit who]
  rfl

theorem observeEnvironment_replace (execution : app.Execution) (inputs : nativeGraph.Inputs)
    (bit : inputs aliceInput = execution.application.config.inputs aliceInput) :
    (replaceExecution execution inputs).observeEnvironment app =
      execution.observeEnvironment app := by
  have same := congrArg Vegas.EventGraphRuntime.PlayerView.publicView
    (replaceStateInputs_bob_view execution.application inputs bit)
  change (replaceStateInputs execution.application inputs).publicView =
    execution.application.publicView at same
  change (⟨_, (replaceStateInputs execution.application inputs).publicView, _⟩ :
    app.EnvironmentView) = _
  rw [same]
  rfl

theorem respond_replace (execution : app.Execution) (inputs : nativeGraph.Inputs)
    (bit : inputs aliceInput = execution.application.config.inputs aliceInput)
    (who : Player) (action : app.Action) :
    replaceExecution (execution.respond app who action) inputs =
      (replaceExecution execution inputs).respond app who action := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [ReactiveApplication.Execution.respond, replaceExecution]
      congr 1
      funext observer
      by_cases same : observer = who
      · subst observer
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil, replaceEntry]
        rw [← observe_replace execution inputs bit who]
        rfl
      · simp only [ite_eq_right same]
  | some submission =>
      have packetEq : app.packet
          (app.submit (replaceStateInputs execution.application inputs) who submission)
          who (execution.network.known who) submission =
          app.packet (app.submit execution.application who submission)
            who (execution.network.known who) submission := by
        rw [← submit_replace execution.application inputs who submission]
        have nextBit : inputs aliceInput =
            (app.submit execution.application who submission).config.inputs aliceInput := by
          change inputs aliceInput = (submitStep (submission.call.register
            execution.application who) who submission.call.packet).config.inputs aliceInput
          rw [submitStep_config, (Submission.register_facts submission.call who
            execution.application).1]
          exact bit
        exact emit_replace submission (app.submit execution.application who submission)
          inputs nextBit who (execution.network.known who)
      simp only [ReactiveApplication.Execution.respond, replaceExecution]
      rw [packetEq, ← submit_replace execution.application inputs who submission]
      congr 1
      funext observer
      by_cases same : observer = who
      · subst observer
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil, replaceEntry]
        rw [← observe_replace execution inputs bit who]
        rfl
      · simp only [ite_eq_right same]

theorem includePending_replace (execution : app.Execution) (inputs : nativeGraph.Inputs)
    (bit : inputs aliceInput = execution.application.config.inputs aliceInput)
    (id : MessageId Player) :
    replaceExecution (execution.includePending app id) inputs =
      (replaceExecution execution inputs).includePending app id := by
  simp only [ReactiveApplication.Execution.includePending, replaceExecution]
  cases selected : execution.network.includePending id with
  | mk envelope network =>
      dsimp only
      cases envelope with
      | none => rfl
      | some message =>
          dsimp only
          rw [← reactive_handle_replace execution.application inputs bit message]
          cases handled : app.handle execution.application message <;> rfl

theorem environmentStep_replace (execution : app.Execution) (inputs : nativeGraph.Inputs)
    (bit : inputs aliceInput = execution.application.config.inputs aliceInput)
    (command : app.Command) :
    (execution.environmentStep app command).map (fun next => replaceExecution next inputs) =
      (replaceExecution execution inputs).environmentStep app command := by
  have publicEq := observeEnvironment_replace execution inputs bit
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
      rw [publicEq]
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
      rw [publicEq]
      change PMF.pure (replaceExecution
        { execution.includePending app id with environmentRecall := _ } inputs) = _
      rw [← includePending_replace execution inputs bit id]
      rfl
  | activate who =>
      simp only [ReactiveApplication.Execution.environmentStep]
      rw [publicEq]
      simp only [PMF.map_comp]
      change (app.observePending who execution.network.pending).map _ = _
      congr 1
  | application operation =>
      simp only [ReactiveApplication.Execution.environmentStep]
      rw [publicEq]
      simp only [PMF.map_comp]
      change (app.environment execution.application operation).map _ = _
      have lawEq : (app.environment execution.application operation).map
          (fun next => replaceStateInputs next inputs) =
          app.environment (replaceExecution execution inputs).application operation :=
        environment_replace execution.application inputs operation
      rw [← lawEq, PMF.map_comp]
      rfl

theorem initial_replace (original inputs : nativeGraph.Inputs)
    (bit : inputs aliceInput = original aliceInput) :
    replaceStateInputs (Vegas.EventGraphRuntime.State.initial original) inputs =
      Vegas.EventGraphRuntime.State.initial inputs := by
  have candidates := initial_candidates_eq original inputs bit.symm
  unfold Vegas.EventGraphRuntime.State.initial replaceStateInputs replaceInputs
  dsimp only
  congr 1

private theorem uniform_label_permutation (permutation : Equiv.Perm (Fin 3)) :
    (PMF.uniformOfFintype (Fin 3)).map permutation = PMF.uniformOfFintype (Fin 3) := by
  ext label
  have fiber (other : Fin 3) : label = permutation other ↔ permutation.symm label = other := by
    constructor
    · intro same
      simpa only [Equiv.symm_apply_apply] using congrArg permutation.symm same
    · intro same
      simpa only [Equiv.apply_symm_apply] using congrArg permutation same
  simp [PMF.map_apply, fiber, PMF.uniformOfFintype_apply]

theorem prior_label_permutation (permutation : Equiv.Perm (Fin 3)) :
    prior.map (fun parameter => (parameter.1, permutation parameter.2)) = prior := by
  unfold prior
  rw [PMF.map_bind]
  congr 1
  funext bit
  rw [PMF.map_comp]
  change (PMF.uniformOfFintype (Fin 3)).map
    ((fun label => (bit, label)) ∘ permutation) = _
  rw [← PMF.map_comp, uniform_label_permutation]

theorem outputs_replace (past : List app.PlayerEntry) (inputs : nativeGraph.Inputs) :
    app.outputs (past.map (fun entry => replaceEntry entry inputs)) = app.outputs past := by
  simp only [ReactiveApplication.outputs, List.filterMap_map, replaceEntry]
  rfl

theorem rawMenu_replace (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (inputs : nativeGraph.Inputs) :
    rawMenu.actions who (past.map (fun entry => replaceEntry entry inputs))
      (replaceView view inputs) = rawMenu.actions who past view :=
  rawMenu_actions_eq_of_packets who _ past _ view (outputs_replace past inputs) rfl

end Vegas.Examples.LateOpeningRuntimeLabelHistories
