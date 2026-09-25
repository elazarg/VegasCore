/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedSymmetry

/-! # The hidden Alice binding in native application state

This transformation flips Alice's Boolean binding output and original binding
action. Public fields, completion order, and all other players' original
actions stay fixed. Together with the selected-candidate transformation, it
describes the application-state change needed before the first publication.
The lemmas are about the existing native application, not a replacement game.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.StoreFlip

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Math.Probability

def output (event : nativeGraph.EventId) (value : (nativeGraph.outputLayout event).Value) :
    (nativeGraph.outputLayout event).Value :=
  if same : event = aliceBinding then
    cast (congrArg (fun event => (nativeGraph.outputLayout event).Value) same.symm)
      (CandidateFlip.result
        (cast (congrArg (fun event => (nativeGraph.outputLayout event).Value) same) value))
  else value

def action (event : nativeGraph.EventId) (value : nativeGraph.Action event) :
    nativeGraph.Action event :=
  if same : event = aliceBinding then
    cast (congrArg (fun event => nativeGraph.Action event) same.symm)
      (CandidateFlip.result
        (cast (congrArg (fun event => nativeGraph.Action event) same) value))
  else value

@[simp] theorem output_alice (value : PublicationResult Bool) :
    output aliceBinding value = CandidateFlip.result value := by simp [output]

@[simp] theorem action_alice (value : PublicationResult Bool) :
    action aliceBinding value = CandidateFlip.result value := by simp [action]

theorem output_other (event : nativeGraph.EventId) (different : event ≠ aliceBinding)
    (value : (nativeGraph.outputLayout event).Value) : output event value = value := by
  rw [output, dite_eq_right different]

theorem action_other (event : nativeGraph.EventId) (different : event ≠ aliceBinding)
    (value : nativeGraph.Action event) : action event value = value := by
  rw [action, dite_eq_right different]

def completion (entry : nativeGraph.Completion) : nativeGraph.Completion :=
  ⟨entry.event, action entry.event entry.action⟩

@[simp] theorem completion_event (entry : nativeGraph.Completion) :
    (completion entry).event = entry.event := rfl

theorem completion_order (history : List nativeGraph.Completion) :
    (history.map completion).map EventGraph.Completion.event =
      history.map EventGraph.Completion.event := by
  rw [List.map_map]
  rfl

def config (before : nativeGraph.Config) : nativeGraph.Config where
  inputs := before.inputs
  cut := before.cut
  outputs event := (before.outputs event).map (output event)
  output_available event := by
    simpa only [Option.isSome_map] using before.output_available event
  history := before.history.map completion
  history_nodup := by simpa only [completion_order] using before.history_nodup
  history_exact event := by simpa only [completion_order] using before.history_exact event

@[simp] theorem config_cut (before : nativeGraph.Config) : (config before).cut = before.cut := rfl

private theorem config_ext (first second : nativeGraph.Config)
    (inputs : first.inputs = second.inputs) (cut : first.cut = second.cut)
    (outputs : first.outputs = second.outputs) (history : first.history = second.history) :
    first = second := by
  cases first
  cases second
  cases inputs
  cases cut
  cases outputs
  cases history
  rfl

theorem config_complete (before : nativeGraph.Config) (event : nativeGraph.EventId)
    (ready : before.cut.Ready event) (chosen : nativeGraph.Action event)
    (value : (nativeGraph.outputLayout event).Value) :
    config (before.complete event ready chosen value) =
      (config before).complete event ready (action event chosen) (output event value) := by
  apply config_ext
  · rfl
  · rfl
  · funext queried
    by_cases same : queried = event
    · subst queried
      simp [config, EventGraph.Config.complete, Function.update]
    · simp only [config, EventGraph.Config.complete, Function.update_of_ne same]
  · simp only [config, EventGraph.Config.complete, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem publicStore (before : nativeGraph.Config) :
    nativeGraph.publicStore (config before).store = nativeGraph.publicStore before.store := by
  apply nativeGraph.publicStore_congr
  intro field visible
  cases field with
  | inl input => rfl
  | inr event =>
      by_cases same : event = aliceBinding
      · subst event
        exact False.elim visible
      · change (before.outputs event).map (output event) = before.outputs event
        cases before.outputs event <;> simp [output_other event same]

theorem playerStore (before : nativeGraph.Config) (who : Player) (different : alice ≠ who) :
    nativeGraph.playerStore who (config before).store =
      nativeGraph.playerStore who before.store := by
  apply nativeGraph.playerStore_congr
  intro field visible
  cases field with
  | inl input => rfl
  | inr event =>
      by_cases same : event = aliceBinding
      · subst event
        exact (different visible).elim
      · change (before.outputs event).map (output event) = before.outputs event
        cases before.outputs event <;> simp [output_other event same]

theorem ownCompletions (history : List nativeGraph.Completion) (who : Player)
    (different : alice ≠ who) :
    nativeGraph.ownCompletions who (history.map completion) =
      nativeGraph.ownCompletions who history := by
  induction history with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨event, value⟩
      by_cases same : event = aliceBinding
      · subst event
        have notOwned : nativeGraph.actor? aliceBinding ≠ some who := by
          change some alice ≠ some who
          exact fun same => different (Option.some.inj same)
        simpa only [EventGraph.ownCompletions, List.map_cons, List.filter_cons,
          completion_event, EventGraph.Completion.event_mk, notOwned, decide_false,
          Bool.false_eq_true, ↓reduceIte] using ih
      · have fixed : completion ⟨event, value⟩ = ⟨event, value⟩ := by
          simp only [completion, action_other event same]
        simp only [List.map_cons, fixed, EventGraph.ownCompletions, List.filter_cons] at ih ⊢
        rw [ih]

theorem publicObserve (before : nativeGraph.Config) :
    nativeGraph.publicObserve (config before) = nativeGraph.publicObserve before := by
  apply EventGraph.PublicObservation.ext
  · exact completion_order before.history
  · exact publicStore before

theorem playerObserve (before : nativeGraph.Config) (who : Player) (different : alice ≠ who) :
    nativeGraph.playerObserve who (config before) = nativeGraph.playerObserve who before := by
  apply EventGraph.PlayerObservation.ext
  · exact completion_order before.history
  · exact playerStore before who different
  · exact ownCompletions before.history who different

def state (selected : Handle nativeGraph) (before : State nativeGraph) : State nativeGraph :=
  { before with
    config := config before.config
    candidates := CandidateFlip.catalogue selected before.candidates }

theorem state_complete (selected : Handle nativeGraph) (before : State nativeGraph)
    (event : nativeGraph.EventId) (ready : before.config.cut.Ready event)
    (chosen : nativeGraph.Action event) (value : (nativeGraph.outputLayout event).Value) :
    state selected (before.complete event ready chosen value) =
      (state selected before).complete event ready (action event chosen) (output event value) := by
  simp only [State.complete, state, config_complete]
  rfl

theorem bindingResult (selected : Handle nativeGraph) (before : State nativeGraph) :
    (state selected before).bindingResult selected .bool =
      CandidateFlip.result (before.bindingResult selected .bool) :=
  CandidateFlip.bindingResult selected before

theorem bindingResult_other (selected queried : Handle nativeGraph)
    (different : queried ≠ selected) (before : State nativeGraph) :
    (state selected before).bindingResult queried .bool = before.bindingResult queried .bool := by
  simp only [State.bindingResult, state]
  rw [CandidateFlip.catalogue_lookup, ite_eq_right different]

theorem handle_alice_commitment (selected : Handle nativeGraph) (before : State nativeGraph)
    (id : MessageId Player) (owner : selected.1 = alice)
    (ready : before.config.cut.Ready aliceBinding)
    (timely : before.WithinDeadline nativeRuntime aliceBinding) (sender : id.1 = alice)
    (vacant : before.accepted (.inr aliceBinding) = none) (unused : before.HandleUnused selected) :
    handle nativeRuntime (state selected before) ⟨id, .commitment aliceBinding selected⟩ =
      (handle nativeRuntime before ⟨id, .commitment aliceBinding selected⟩).map
        (state selected) := by
  rw [handle_commitment_eq nativeRuntime before id aliceBinding selected alice .bool rfl rfl rfl
    ready timely sender owner vacant unused]
  rw [handle_commitment_eq nativeRuntime (state selected before) id aliceBinding selected
    alice .bool rfl rfl rfl ready timely sender owner vacant unused]
  simp only [Option.map_some, Option.some.injEq, cast_eq, bindingResult]
  have completed := state_complete selected before aliceBinding ready
    (before.bindingResult selected .bool) (before.bindingResult selected .bool)
  simp only [action_alice, output_alice] at completed
  change _ = { state selected (before.complete aliceBinding ready
    (before.bindingResult selected .bool) (before.bindingResult selected .bool)) with
      accepted := Function.update before.accepted (.inr aliceBinding) (some selected)
      candidates := CandidateFlip.catalogue selected (before.candidates.freeze selected) }
  rw [completed, CandidateFlip.catalogue_freeze]
  rfl

/-- A successful other-player binding uses its unchanged candidate value.
This applies to the Carol and Bob binding nodes, before any publication. -/
theorem handle_other_commitment (selected candidate : Handle nativeGraph)
    (differentHandle : candidate ≠ selected) (before : State nativeGraph)
    (id : MessageId Player) (event : nativeGraph.EventId) (differentEvent : event ≠ aliceBinding)
    (who : Player) (outputEq : nativeGraph.outputLayout event = .binding who .bool)
    (codeEq : cast (congrArg (EventGraph.EventCode (L := simpleExpr) nativeGraph.layout) outputEq)
      (nativeGraph.nodes event) = EventGraph.EventCode.bind (L := simpleExpr)
        (layout := nativeGraph.layout) who BaseTy.bool)
    (view : nodeView nativeGraph event = .bind who .bool outputEq codeEq)
    (ready : before.config.cut.Ready event) (timely : before.WithinDeadline nativeRuntime event)
    (sender : id.1 = who) (owner : candidate.1 = who)
    (vacant : before.accepted (.inr event) = none) (unused : before.HandleUnused candidate) :
    handle nativeRuntime (state selected before) ⟨id, .commitment event candidate⟩ =
      (handle nativeRuntime before ⟨id, .commitment event candidate⟩).map (state selected) := by
  rw [handle_commitment_eq nativeRuntime before id event candidate who .bool outputEq codeEq view
    ready timely sender owner vacant unused]
  rw [handle_commitment_eq nativeRuntime (state selected before) id event candidate
    who .bool outputEq codeEq view ready timely sender owner vacant unused]
  rw [bindingResult_other selected candidate differentHandle before]
  simp only [Option.map_some, Option.some.injEq]
  let chosen : nativeGraph.Action event := cast
    (congrArg EventGraph.EventField.Action outputEq.symm) (before.bindingResult candidate .bool)
  let value : (nativeGraph.outputLayout event).Value := cast
    (congrArg EventGraph.EventField.Value outputEq.symm) (before.bindingResult candidate .bool)
  have completed := state_complete selected before event ready chosen value
  rw [action_other event differentEvent, output_other event differentEvent] at completed
  change _ = { state selected (before.complete event ready chosen value) with
    accepted := Function.update before.accepted (.inr event) (some candidate)
    candidates := CandidateFlip.catalogue selected (before.candidates.freeze candidate) }
  rw [completed, CandidateFlip.catalogue_freeze]
  rfl

/-- Rejection cannot test the flipped bit at a binding node. The application
checks event kind before any opening verification, and commitment rejection
uses only readiness, time, authentication and handle allocation. -/
theorem handle_other_binding (selected : Handle nativeGraph) (selectedOwner : selected.1 = alice)
    (before : State nativeGraph) (event : nativeGraph.EventId)
    (differentEvent : event ≠ aliceBinding) (who : Player) (differentOwner : who ≠ alice)
    (outputEq : nativeGraph.outputLayout event = .binding who .bool)
    (codeEq : cast (congrArg (EventGraph.EventCode (L := simpleExpr) nativeGraph.layout) outputEq)
      (nativeGraph.nodes event) = EventGraph.EventCode.bind (L := simpleExpr)
        (layout := nativeGraph.layout) who BaseTy.bool)
    (view : nodeView nativeGraph event = .bind who .bool outputEq codeEq)
    (sent : Message Player (Payload nativeGraph))
    (addressed : sent.payload.event? nativeGraph = some event) :
    handle nativeRuntime (state selected before) sent =
      (handle nativeRuntime before sent).map (state selected) := by
  rcases sent with ⟨id, packet⟩
  cases packet with
  | malformed value => cases addressed
  | opening addressedEvent candidate value =>
      cases Option.some.inj addressed
      simp only [handle, view, state, config, State.WithinDeadline]
      split_ifs <;> rfl
  | withhold addressedEvent =>
      cases Option.some.inj addressed
      simp only [handle, view, state, config, State.WithinDeadline]
      split_ifs <;> rfl
  | commitment addressedEvent candidate =>
      cases Option.some.inj addressed
      by_cases good : before.config.cut.Ready event ∧
          before.WithinDeadline nativeRuntime event ∧ id.1 = who ∧ candidate.1 = who ∧
          before.accepted (.inr event) = none ∧ before.HandleUnused candidate
      · obtain ⟨ready, timely, sender, owner, vacant, unused⟩ := good
        have differentHandle : candidate ≠ selected := by
          intro same
          exact differentOwner (owner.symm.trans ((congrArg Prod.fst same).trans selectedOwner))
        exact handle_other_commitment selected candidate differentHandle before id event
          differentEvent who outputEq codeEq view ready timely sender owner vacant unused
      · have rejected : handle nativeRuntime before ⟨id, .commitment event candidate⟩ = none := by
          simp only [handle, view, Message.sender]
          split_ifs <;> simp_all
        have rejectedFlip : handle nativeRuntime (state selected before)
            ⟨id, .commitment event candidate⟩ = none := by
          simp only [handle, view, Message.sender, state, config, State.WithinDeadline,
            State.HandleUnused] at *
          split_ifs <;> simp_all
        rw [rejectedFlip, rejected]
        rfl

theorem environment_grant (selected : Handle nativeGraph) (before : State nativeGraph)
    (event : nativeGraph.EventId) :
    environmentStep nativeRuntime (state selected before) (.grant event) =
      (environmentStep nativeRuntime before (.grant event)).map (state selected) := by
  simp only [environmentStep, FinDist.map_pure]
  rfl

theorem environment_tick (selected : Handle nativeGraph) (before : State nativeGraph) :
    environmentStep nativeRuntime (state selected before) .advanceClock =
      (environmentStep nativeRuntime before .advanceClock).map (state selected) := by
  simp only [environmentStep, FinDist.map_pure]
  rfl

/-- Binding expiry commutes with the hidden-value flip even on failed or
off-path runs. Deadline and activation tests are unchanged. -/
theorem environment_expire_binding (selected : Handle nativeGraph) (before : State nativeGraph)
    (event : nativeGraph.EventId) (who : Player)
    (outputEq : nativeGraph.outputLayout event = .binding who .bool)
    (codeEq : cast (congrArg (EventGraph.EventCode (L := simpleExpr) nativeGraph.layout) outputEq)
      (nativeGraph.nodes event) = EventGraph.EventCode.bind (L := simpleExpr)
        (layout := nativeGraph.layout) who BaseTy.bool)
    (view : nodeView nativeGraph event = .bind who .bool outputEq codeEq) :
    environmentStep nativeRuntime (state selected before) (.expire event) =
      (environmentStep nativeRuntime before (.expire event)).map (state selected) := by
  by_cases ready : before.config.cut.Ready event
  · cases activated : before.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated nativeRuntime before event ready activated,
          environmentStep_expire_of_not_activated nativeRuntime (state selected before)
            event ready activated, FinDist.map_pure]
    | some entered =>
        by_cases due : nativeRuntime.deadline event ≤ before.clock - entered
        · rw [environmentStep_expire_bind_eq nativeRuntime before event ready entered activated
            due who .bool outputEq codeEq view,
            environmentStep_expire_bind_eq nativeRuntime (state selected before) event
              ready entered activated due who .bool outputEq codeEq view, FinDist.map_pure]
          apply congrArg FinDist.pure
          have completed := state_complete selected before event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (PublicationResult.failure : PublicationResult Bool))
            (cast (congrArg EventGraph.EventField.Value outputEq.symm)
              (PublicationResult.failure : PublicationResult Bool))
          by_cases same : event = aliceBinding
          · subst event
            have owner : who = alice := by cases outputEq; rfl
            subst who
            simpa only [cast_eq, action_alice, output_alice, CandidateFlip.result]
              using completed.symm
          · simpa only [action_other event same, output_other event same] using completed.symm
        · rw [environmentStep_expire_of_not_due nativeRuntime before event ready entered
            activated due,
            environmentStep_expire_of_not_due nativeRuntime (state selected before) event
              ready entered activated due, FinDist.map_pure]
  · rw [environmentStep_expire_of_not_ready nativeRuntime before event ready,
      environmentStep_expire_of_not_ready nativeRuntime (state selected before) event ready,
      FinDist.map_pure]


theorem publicView (selected : Handle nativeGraph) (before : State nativeGraph) :
    (state selected before).publicView = before.publicView := by
  simp only [state, State.publicView, publicObserve]

theorem playerView (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (before : State nativeGraph) (who : Player) (different : alice ≠ who) :
    (state selected before).playerView who = before.playerView who := by
  have meanings : (fun slot => (CandidateFlip.catalogue selected before.candidates).lookup
      (who, slot)) = fun slot => before.candidates.lookup (who, slot) := by
    funext slot
    exact CandidateFlip.catalogue_lookup_other_owner selected before.candidates who
      (owner ▸ different) slot
  simp only [state, State.playerView, State.publicView, publicObserve,
    playerObserve before.config who different, meanings]

private theorem register_replaceConfig (submitted : Submission nativeGraph)
    (before : State nativeGraph) (who : Player) (replacement : nativeGraph.Config) :
    submitted.register { before with config := replacement } who =
      { submitted.register before who with config := replacement } := by
  rcases submitted with ⟨packet, opening⟩
  cases packet with
  | commitment event handle =>
      rcases handle with ⟨owner, slot⟩
      cases slot <;> cases opening <;> simp only [Submission.register]
      split <;> rfl
  | opening | withhold | malformed => rfl

theorem register (selected : Handle nativeGraph) (submitted : Submission nativeGraph)
    (before : State nativeGraph) (who : Player) :
    (CandidateFlip.call selected submitted).register (state selected before) who =
      state selected (submitted.register before who) := by
  calc
    _ = { (CandidateFlip.call selected submitted).register
        (CandidateFlip.state selected before) who with config := config before.config } :=
      register_replaceConfig (CandidateFlip.call selected submitted)
        (CandidateFlip.state selected before) who (config before.config)
    _ = { CandidateFlip.state selected (submitted.register before who) with
        config := config before.config } :=
      congrArg (fun current : State nativeGraph =>
        { current with config := config before.config })
          (CandidateFlip.register selected submitted before who)
    _ = _ := by
      simp only [state, CandidateFlip.state, (submitted.register_facts who before).1]

theorem register_other_owner (selected : Handle nativeGraph) (submitted : Submission nativeGraph)
    (before : State nativeGraph) (who : Player) (different : selected.1 ≠ who) :
    submitted.register (state selected before) who =
      state selected (submitted.register before who) := by
  rw [← CandidateFlip.call_register_other_owner selected submitted (state selected before)
    who different, register]

theorem submitStep_state (selected : Handle nativeGraph) (before : State nativeGraph)
    (who : Player) (sent : Payload nativeGraph) :
    submitStep (state selected before) who sent = state selected (submitStep before who sent) := by
  cases sent with
  | commitment event handle =>
      by_cases owned : handle.1 = who
      · simp only [submitStep, owned, ↓reduceIte, state]
        congr 1
        exact (CandidateFlip.catalogue_freeze selected handle before.candidates).symm
      · simp [submitStep, state, owned]
  | opening | withhold | malformed => rfl

theorem emit (selected : Handle nativeGraph) (submitted : WitnessedSubmission nativeGraph)
    (before : State nativeGraph) (who : Player)
    (known : List (Message Player (WitnessedPacket nativeGraph))) :
    (CandidateFlip.submission selected submitted).emit (state selected before) who
        (known.map (CandidateFlip.message selected)) =
      CandidateFlip.packet selected (submitted.emit before who known) := by
  calc
    _ = (CandidateFlip.submission selected submitted).emit (CandidateFlip.state selected before)
        who (known.map (CandidateFlip.message selected)) :=
      WitnessedSubmission.emit_local _ _ _ _ _ (fun _ => rfl)
    _ = _ := CandidateFlip.emit selected submitted before who known

end VegasTests.SelectiveAssociation.Restricted.StoreFlip
