/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeService
import Vegas.EventGraph.PrivateInputs
import Vegas.Examples.LateOpeningRuntimeReadout
import Vegas.Examples.LateOpeningRuntimeBobService

/-! # Native operational invariance under private-label changes

Changing only Alice's ordinary initial label preserves the compiled evaluator laws,
selected graph transitions, reachability and Bob's complete physical observation.
Actual private preparations, transmissions and raw packet handlers commute with
this input replacement. Supplied packet values, authenticated candidate meanings,
accepted handles, original completion actions and physical clocks remain intact.

These results do not yet lift the replacement to complete raw protocol histories
or construct an equilibrium assessment.
-/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeLabelSymmetry

open Vegas.EventGraph
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
open LateOpeningRuntimeBobService

theorem label_not_read (event : nativeGraph.EventId) :
    (.inl ⟨1, by decide⟩ : nativeGraph.Field) ∉
      (nativeGraph.nodes event).readFields := by
  change Fin 3 at event
  fin_cases event <;> decide

theorem evaluator_eq_of_label_change (event : nativeGraph.EventId)
    (action : (nativeGraph.nodes event).Action)
    (left right : Store nativeGraph.layout)
    (same : ∀ field, field ≠ .inl ⟨1, by decide⟩ → left field = right field) :
    (nativeGraph.nodes event).eval? action left =
      (nativeGraph.nodes event).eval? action right := by
  apply EventCode.eval?_congr
  intro field member
  apply same
  intro equality
  subst field
  exact label_not_read event member

theorem bob_label_hidden (store : Store nativeGraph.layout) :
    nativeGraph.playerStore bob store (.inl ⟨1, by decide⟩) = none := by
  apply nativeGraph.playerStore_foreign_privateInput store _ alice bob (.range 0 2)
  · rfl
  · decide

/-- Replace only the immutable input environment; all raw completion records remain intact. -/
def replaceInputs (config : nativeGraph.Config) (inputs : nativeGraph.Inputs) :
    nativeGraph.Config := { config with inputs }

theorem replaceInputs_store_eq (config : nativeGraph.Config) (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = config.inputs ⟨0, by decide⟩)
    (field : nativeGraph.Field) (different : field ≠ .inl ⟨1, by decide⟩) :
    (replaceInputs config inputs).store field = config.store field := by
  cases field with
  | inl input =>
      change Fin 2 at input
      fin_cases input
      · exact congrArg some bit
      · exact False.elim (different rfl)
  | inr event => rfl

theorem replaceInputs_evaluator (config : nativeGraph.Config) (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = config.inputs ⟨0, by decide⟩)
    (event : nativeGraph.EventId) (action : nativeGraph.Action event) :
    (nativeGraph.nodes event).eval? action (replaceInputs config inputs).store =
      (nativeGraph.nodes event).eval? action config.store :=
  evaluator_eq_of_label_change event action _ _ (replaceInputs_store_eq config inputs bit)

theorem replaceInputs_bob_observe (config : nativeGraph.Config) (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = config.inputs ⟨0, by decide⟩) :
    nativeGraph.playerObserve bob (replaceInputs config inputs) =
      nativeGraph.playerObserve bob config := by
  apply PlayerObservation.ext
  · rfl
  · change nativeGraph.playerStore bob (replaceInputs config inputs).store =
      nativeGraph.playerStore bob config.store
    funext field
    by_cases label : field = .inl ⟨1, by decide⟩
    · subst field
      rw [bob_label_hidden, bob_label_hidden]
    · unfold playerStore
      rw [replaceInputs_store_eq config inputs bit field label]
  · rfl

theorem replaceInputs_complete (config : nativeGraph.Config) (inputs : nativeGraph.Inputs)
    (event : nativeGraph.EventId) (ready : config.cut.Ready event)
    (action : nativeGraph.Action event) (value : (nativeGraph.outputLayout event).Value) :
    replaceInputs (config.complete event ready action value) inputs =
      (replaceInputs config inputs).complete event ready action value := rfl

theorem replaceInputs_step (config : nativeGraph.Config) (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = config.inputs ⟨0, by decide⟩)
    (event : nativeGraph.EventId) (ready : config.cut.Ready event)
    (action : nativeGraph.Action event) :
    (config.step event ready action).map (fun next => replaceInputs next inputs) =
      (replaceInputs config inputs).step event ready action := by
  have available := EventCode.eval?_isSome_of_reads (nativeGraph.nodes event) action
    config.store (fun _ read => config.read_available ready read)
  let law := ((nativeGraph.nodes event).eval? action config.store).get available
  have evaluates : (nativeGraph.nodes event).eval? action config.store = some law :=
    (Option.some_get available).symm
  have replaced : (nativeGraph.nodes event).eval? action
      (replaceInputs config inputs).store = some law :=
    (replaceInputs_evaluator config inputs bit event action).trans evaluates
  rw [Config.step_eq_map_of_eval config event ready action law evaluates,
    Config.step_eq_map_of_eval (replaceInputs config inputs) event ready action law replaced,
    PMF.map_comp]
  rfl

theorem replaceInputs_reachable {original : nativeGraph.Inputs}
    {config : nativeGraph.Config} (reachable : config.Reachable original)
    (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = original ⟨0, by decide⟩) :
    (replaceInputs config inputs).Reachable inputs := by
  induction reachable with
  | initial => exact Config.Reachable.initial
  | @step config reachable event ready action next supported ih =>
      apply Config.Reachable.step ih event ready action
      rw [← replaceInputs_step config inputs
        (bit.trans (congrFun reachable.inputs_eq ⟨0, by decide⟩).symm) event ready action]
      rw [PMF.support_map]
      exact ⟨next, supported, rfl⟩

theorem replaceInputs_public_observe (config : nativeGraph.Config)
    (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = config.inputs ⟨0, by decide⟩) :
    nativeGraph.publicObserve (replaceInputs config inputs) = nativeGraph.publicObserve config := by
  apply PublicObservation.ext
  · rfl
  · change nativeGraph.publicStore (replaceInputs config inputs).store =
      nativeGraph.publicStore config.store
    funext field
    by_cases label : field = .inl ⟨1, by decide⟩
    · subst field
      rw [nativeGraph.publicStore_privateInput _ _ alice (.range 0 2) rfl,
        nativeGraph.publicStore_privateInput _ _ alice (.range 0 2) rfl]
    · unfold publicStore
      rw [replaceInputs_store_eq config inputs bit field label]

/-- Retain every candidate meaning, accepted handle and physical clock while relabeling inputs. -/
def replaceStateInputs (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs) : Vegas.EventGraphRuntime.State nativeGraph :=
  { state with config := replaceInputs state.config inputs }

theorem replaceStateInputs_bob_view (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = state.config.inputs ⟨0, by decide⟩) :
    (replaceStateInputs state inputs).playerView bob = state.playerView bob := by
  unfold Vegas.EventGraphRuntime.State.playerView Vegas.EventGraphRuntime.State.publicView
  simp only [replaceStateInputs, replaceInputs_public_observe state.config inputs bit,
    replaceInputs_bob_observe state.config inputs bit]

theorem initial_candidates_eq (left right : nativeGraph.Inputs)
    (bit : left ⟨0, by decide⟩ = right ⟨0, by decide⟩) :
    (Vegas.EventGraphRuntime.State.initial left).candidates =
      (Vegas.EventGraphRuntime.State.initial right).candidates := by
  apply congrArg Interaction.CommitmentCandidates.mk
  funext owner slot
  change (Vegas.EventGraphRuntime.State.initial left).candidates.lookup (owner, slot) =
    (Vegas.EventGraphRuntime.State.initial right).candidates.lookup (owner, slot)
  rw [Vegas.EventGraphRuntime.State.initial_candidate,
    Vegas.EventGraphRuntime.State.initial_candidate]
  cases slot with
  | prepared serial => rfl
  | initial input =>
      change Fin 2 at input
      fin_cases input
      · change Vegas.EventGraphRuntime.State.candidateOfValue owner
          (nativeGraph.inputLayout ⟨0, by decide⟩) (left ⟨0, by decide⟩) = _
        exact congrArg (Vegas.EventGraphRuntime.State.candidateOfValue owner
          (nativeGraph.inputLayout ⟨0, by decide⟩)) bit
      · rfl

theorem replaceStateInputs_complete (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs) (event : nativeGraph.EventId)
    (ready : state.config.cut.Ready event) (action : nativeGraph.Action event)
    (value : (nativeGraph.outputLayout event).Value) :
    replaceStateInputs (state.complete event ready action value) inputs =
      (replaceStateInputs state inputs).complete event ready action value := rfl

theorem replaceStateInputs_privateStep (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs) (who : Player)
    (command : Vegas.EventGraphRuntime.PrivateCommand nativeGraph) :
    replaceStateInputs (Vegas.EventGraphRuntime.privateStep state who command) inputs =
      Vegas.EventGraphRuntime.privateStep (replaceStateInputs state inputs) who command := by
  cases command
  rfl

theorem replaceStateInputs_submitStep (state : Vegas.EventGraphRuntime.State nativeGraph)
    (inputs : nativeGraph.Inputs) (who : Player)
    (packet : Vegas.EventGraphRuntime.Payload nativeGraph) :
    replaceStateInputs (Vegas.EventGraphRuntime.submitStep state who packet) inputs =
      Vegas.EventGraphRuntime.submitStep (replaceStateInputs state inputs) who packet := by
  cases packet <;> simp only [Vegas.EventGraphRuntime.submitStep]
  all_goals rfl

theorem replaceStateInputs_handle_commitment
    (state : Vegas.EventGraphRuntime.State nativeGraph) (inputs : nativeGraph.Inputs)
    (id : Interaction.MessageId Player) (event : nativeGraph.EventId)
    (candidate : Vegas.EventGraphRuntime.Handle nativeGraph) :
    (Vegas.EventGraphRuntime.handle LateOpeningRuntimeService.runtime state
      ⟨id, .commitment event candidate⟩).map
        (fun next => replaceStateInputs next inputs) =
      Vegas.EventGraphRuntime.handle LateOpeningRuntimeService.runtime
        (replaceStateInputs state inputs)
        ⟨id, .commitment event candidate⟩ := by
  classical
  have aliceNode : Vegas.EventGraphRuntime.nodeView nativeGraph aliceEvent =
      .resolve alice .bool aliceBinding [] rfl rfl := rfl
  have bobNode : Vegas.EventGraphRuntime.nodeView nativeGraph bobBindEvent =
      .bind bob (.range 0 5) rfl rfl := rfl
  have revealNode : Vegas.EventGraphRuntime.nodeView nativeGraph bobRevealEvent =
      .resolve bob (.range 0 5) bobBinding bobChecks rfl rfl := rfl
  change Fin 3 at event
  fin_cases event
  · simp only [Vegas.EventGraphRuntime.handle, aliceNode]
    split <;> simp_all
  · simp only [Vegas.EventGraphRuntime.handle, bobNode]
    simp only [replaceStateInputs, replaceInputs,
      Vegas.EventGraphRuntime.State.WithinDeadline, Vegas.EventGraphRuntime.State.HandleUnused]
    split_ifs <;> rfl
  · simp only [Vegas.EventGraphRuntime.handle, revealNode]
    split <;> simp_all

theorem replaceStateInputs_handle_alice_opening
    (state : Vegas.EventGraphRuntime.State nativeGraph) (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = state.config.inputs ⟨0, by decide⟩)
    (id : Interaction.MessageId Player) (candidate : Vegas.EventGraphRuntime.Handle nativeGraph)
    (raw : Vegas.EventGraphRuntime.Raw simpleExpr) :
    (Vegas.EventGraphRuntime.handle LateOpeningRuntimeService.runtime state
      ⟨id, .opening aliceEvent candidate raw⟩).map
        (fun next => replaceStateInputs next inputs) =
      Vegas.EventGraphRuntime.handle LateOpeningRuntimeService.runtime
        (replaceStateInputs state inputs) ⟨id, .opening aliceEvent candidate raw⟩ := by
  classical
  have node : Vegas.EventGraphRuntime.nodeView nativeGraph aliceEvent =
      .resolve alice .bool aliceBinding [] rfl rfl := rfl
  simp only [Vegas.EventGraphRuntime.handle, node]
  simp only [replaceStateInputs, replaceInputs,
    Vegas.EventGraphRuntime.State.WithinDeadline]
  cases typed : raw.as? .bool
  · dsimp only
    split_ifs <;> rfl
  · rename_i value
    dsimp only
    have stored : aliceBinding.get? (replaceInputs state.config inputs).store =
        aliceBinding.get? state.config.store := by
      change some (inputs ⟨0, by decide⟩) = some (state.config.inputs ⟨0, by decide⟩)
      exact congrArg some bit
    simp only [replaceInputs] at stored
    rw [stored]
    split_ifs
    all_goals first
    | rfl
    | rename_i sourceStored
      change ((EventCode.resolveOutput? aliceBinding [] true state.config.store).map
        (fun result => replaceStateInputs
          (state.complete aliceEvent (by assumption) true result) inputs)) =
          (EventCode.resolveOutput? aliceBinding [] true
            (replaceInputs state.config inputs).store).map
              (fun result => (replaceStateInputs state inputs).complete
                aliceEvent (by assumption) true result)
      simp only [EventCode.resolveOutput?, sourceStored,
        show aliceBinding.get? (replaceInputs state.config inputs).store =
          some (.success value) from stored.trans sourceStored,
        GuardCheck.allAccepted?]
      rfl

theorem replaceStateInputs_handle_bob_opening
    (state : Vegas.EventGraphRuntime.State nativeGraph) (inputs : nativeGraph.Inputs)
    (id : Interaction.MessageId Player) (candidate : Vegas.EventGraphRuntime.Handle nativeGraph)
    (raw : Vegas.EventGraphRuntime.Raw simpleExpr) :
    (Vegas.EventGraphRuntime.handle LateOpeningRuntimeService.runtime state
      ⟨id, .opening bobRevealEvent candidate raw⟩).map
        (fun next => replaceStateInputs next inputs) =
      Vegas.EventGraphRuntime.handle LateOpeningRuntimeService.runtime
        (replaceStateInputs state inputs) ⟨id, .opening bobRevealEvent candidate raw⟩ := by
  classical
  have node : Vegas.EventGraphRuntime.nodeView nativeGraph bobRevealEvent =
      .resolve bob (.range 0 5) bobBinding bobChecks rfl rfl := rfl
  simp only [Vegas.EventGraphRuntime.handle, node]
  simp only [replaceStateInputs, replaceInputs,
    Vegas.EventGraphRuntime.State.WithinDeadline]
  cases typed : raw.as? (.range 0 5)
  · dsimp only
    split_ifs <;> rfl
  · rename_i value
    dsimp only
    have stored : bobBinding.get? (replaceInputs state.config inputs).store =
        bobBinding.get? state.config.store := by
      rfl
    simp only [replaceInputs] at stored
    rw [stored]
    split_ifs
    all_goals first
    | rfl
    | rename_i sourceStored
      change Option.map (fun next => replaceStateInputs next inputs)
        ((EventCode.resolveOutput? bobBinding bobChecks true state.config.store).bind
          (fun result => some (state.complete bobRevealEvent (by assumption) true result))) =
        (EventCode.resolveOutput? bobBinding bobChecks true
          (replaceInputs state.config inputs).store).bind
            (fun result => some ((replaceStateInputs state inputs).complete
              bobRevealEvent (by assumption) true result))
      simp only [EventCode.resolveOutput?, sourceStored,
        show bobBinding.get? (replaceInputs state.config inputs).store =
          some (.success value) from stored.trans sourceStored]
      rfl

theorem replaceStateInputs_handle
    (state : Vegas.EventGraphRuntime.State nativeGraph) (inputs : nativeGraph.Inputs)
    (bit : inputs ⟨0, by decide⟩ = state.config.inputs ⟨0, by decide⟩)
    (message : Interaction.Message Player (Vegas.EventGraphRuntime.Payload nativeGraph)) :
    (Vegas.EventGraphRuntime.handle LateOpeningRuntimeService.runtime state message).map
        (fun next => replaceStateInputs next inputs) =
      Vegas.EventGraphRuntime.handle LateOpeningRuntimeService.runtime
        (replaceStateInputs state inputs) message := by
  classical
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => rfl
  | commitment event candidate =>
      exact replaceStateInputs_handle_commitment state inputs id event candidate
  | opening event candidate raw =>
      change Fin 3 at event
      fin_cases event
      · exact replaceStateInputs_handle_alice_opening state inputs bit id candidate raw
      · have node : Vegas.EventGraphRuntime.nodeView nativeGraph bobBindEvent =
            .bind bob (.range 0 5) rfl rfl := rfl
        simp only [Vegas.EventGraphRuntime.handle, node]
        split <;> simp_all
      · exact replaceStateInputs_handle_bob_opening state inputs id candidate raw

end Vegas.Examples.LateOpeningRuntimeLabelSymmetry
