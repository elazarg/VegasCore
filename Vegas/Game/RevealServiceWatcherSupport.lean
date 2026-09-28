/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceOwnerSupport
import Vegas.Game.RevealServiceActions
import Interaction.DeferredObservation

/-! # Silence at every retained watcher opportunity

Reserved inclusion precedes the watcher activation. Every ordinary owner
response is silence, a published replay, or a fresh opening for that reserved
event. Consequently the watcher has no unpublished evidence at any legal C
history. The statement covers all retained histories and arbitrary policies.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

omit [Fintype Player] in
private theorem opening_shape (owner : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (granted : view.application.publicView.serviceGrant = some event)
    (response : (application setup leaks).Action)
    (selected : opening? setup leaks owner past view = some response) :
    ∃ candidate raw evidence,
      response = ⟨some (.submit ⟨⟨.opening event candidate raw, none⟩, evidence⟩)⟩ := by
  unfold opening? at selected
  rw [granted] at selected
  simp only [bind, Option.bind_some] at selected
  split at selected
  · cases selected
  · cases node : nodeView (graph setup) event with
    | sample => simp only [node] at selected; cases selected
    | bind => simp only [node] at selected; cases selected
    | resolve who payload binding checks outputEq codeEq =>
        simp only [node] at selected
        cases resolved : EventGraph.EventCode.resolveOutput? binding checks true
            view.application.observation.store with
        | none => simp only [resolved] at selected; cases selected
        | some publication =>
            cases publication with
            | failure => simp only [resolved] at selected; cases selected
            | success value =>
                simp only [resolved] at selected
                obtain ⟨candidate, _accepted, selected⟩ := Option.bind_eq_some_iff.mp selected
                split at selected
                · cases selected
                · have same := Option.some.inj selected
                  obtain ⟨evidence, shape⟩ := (runtime setup).normalized_reveal_response leaks
                    owner past view event candidate ⟨payload, value⟩
                  exact ⟨candidate, ⟨payload, value⟩, evidence, same.symm.trans shape⟩

private theorem ordinary_inclusion_published (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy) (watcher owner : Player)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (granted : execution.application.serviceGrant = some event)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (leaked : execution.network.leaked = fun _ => [])
    (inputs : ∀ input ∈ execution.network.inputs,
      input.envelope.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (response : (application setup leaks).Action)
    (allowed : response ∈ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner))
    (next : (application setup leaks).Execution)
    (reached : next ∈ ((runtime setup).interactionStep leaks players
      ((runtime setup).reportNetwork leaks watcher) (.includeLatest event owner)
      (execution.respond (application setup leaks) owner response)).support) :
    (∀ message ∈ next.network.pending,
      message.id ∈ next.network.ledger.map Message.id) ∧
      next.network.leaked = (fun _ => []) ∧
      (∀ input ∈ next.network.inputs,
        input.envelope.id ∈ next.network.ledger.map Message.id) := by
  let app := application setup leaks
  rcases ordinary_response_cases setup leaks bounds owner _ _ response allowed with
    silent | opening | replay
  · subst response
    have quietPending : ∀ message ∈ (execution.respond app owner ⟨none⟩).network.pending,
        message.id ∈ (execution.respond app owner ⟨none⟩).network.ledger.map Message.id := pending
    rw [(runtime setup).interaction_includeLatest_of_pending_published leaks players
      ((runtime setup).reportNetwork leaks watcher) _ owner event quietPending] at reached
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.mem_support_pure] at reached
    subst next
    exact ⟨pending, leaked, inputs⟩
  · obtain ⟨candidate, raw, evidence, rfl⟩ := opening_shape setup leaks owner _ _ event
      granted response opening
    let submitted := execution.respond app owner
      ⟨some (.submit ⟨⟨.opening event candidate raw, none⟩, evidence⟩)⟩
    let id := (owner, execution.network.nextSerial owner)
    let packet := app.packet execution.application owner (execution.network.known owner)
      ⟨⟨.opening event candidate raw, none⟩, evidence⟩
    have found : submitted.network.lookup id = some ⟨id, packet⟩ :=
      serials.lookup_submit owner packet
    have oldOrNew : ∀ message ∈ submitted.network.pending,
        message.id ∈ submitted.network.ledger.map Message.id ∨ message.id = id := by
      intro message member
      change message ∈ execution.network.pending ++ [⟨id, packet⟩] at member
      rcases List.mem_append.mp member with old | fresh
      · exact Or.inl (pending message old)
      · obtain rfl := List.mem_singleton.mp fresh
        exact Or.inr rfl
    rw [(runtime setup).opening_inclusion leaks players
      ((runtime setup).reportNetwork leaks watcher) execution owner event candidate raw
      evidence (serials.next_unpublished owner)] at reached
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.mem_support_pure] at reached
    subst next
    change (∀ message ∈ (submitted.includePending app id).network.pending,
      message.id ∈ (submitted.includePending app id).network.ledger.map Message.id) ∧
      (submitted.includePending app id).network.leaked = (fun _ => []) ∧
      (∀ input ∈ (submitted.includePending app id).network.inputs,
        input.envelope.id ∈ (submitted.includePending app id).network.ledger.map Message.id)
    rw [app.includePending_network]
    refine ⟨submitted.network.include_pending_published_or_selected id _ found oldOrNew, ?_, ?_⟩
    · change (submitted.network.includePending id).2.leaked = fun _ => []
      rw [MessageNetwork.includePending, found]
      exact leaked
    · exact (execution.network.submit_include_published owner packet pending inputs serials).2.1
  · obtain ⟨message, published, rfl⟩ := replay
    have spent : message.id ∈ execution.network.ledger.map Message.id :=
      List.mem_map.mpr ⟨message, published, rfl⟩
    rw [(runtime setup).published_replay_inclusion leaks players
      ((runtime setup).reportNetwork leaks watcher) execution owner event message.id
      pending spent] at reached
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.mem_support_pure] at reached
    subst next
    refine ⟨execution.network.replay_pending_published owner message.id pending spent, ?_,
      execution.network.replay_inputs_published owner message.id inputs spent⟩
    change (execution.network.replay owner message.id).2.leaked = fun _ => []
    unfold MessageNetwork.replay
    split <;> exact leaked

omit [Fintype Player] in
private theorem include_control_step
    (players : Player → (application setup leaks).Policy) (watcher owner : Player)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (remaining cursor : Nat) (position : execution.environmentRecall.length = cursor)
    (located : (plan setup watcher)[cursor]? = some (.includeLatest event owner)) :
    (application setup leaks).controlStep (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) players (some ⟨remaining + 1, none, execution⟩) =
      ((runtime setup).interactionStep leaks players ((runtime setup).reportNetwork leaks watcher)
        (.includeLatest event owner) execution).map (fun next => some ⟨remaining, none, next⟩) := by
  let app := application setup leaks
  have scheduled : scheduler setup leaks watcher execution.environmentRecall
      (execution.observeEnvironment app) = (runtime setup).interactionInstruction leaks
        ((runtime setup).reportNetwork leaks watcher) execution.environmentRecall
        (execution.observeEnvironment app) (.includeLatest event owner) := by
    simp only [scheduler, position, located]
  change (scheduler setup leaks watcher execution.environmentRecall
    (execution.observeEnvironment app)).bind _ = _
  rw [scheduled, interactionStep, FinDist.map_bind]
  apply FinDist.bind_congr
  intro command supported
  have noActor := instruction_actor setup leaks watcher execution.environmentRecall
    (execution.observeEnvironment app) (.includeLatest event owner) command supported
  change command.actor? app = none at noActor
  dsimp only [app, application] at noActor ⊢
  simp only [ReactiveApplication.dispatch, noActor]
  change _ = ((execution.environmentStep (application setup leaks) command).bind
    FinDist.pure).map _
  rw [FinDist.bind_pure]

private theorem owner_to_watcher_clean (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy) (watcher owner : Player)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (remaining cursor : Nat) (position : execution.environmentRecall.length = cursor)
    (includeAt : (plan setup watcher)[cursor]? = some (.includeLatest event owner))
    (watcherAt : (plan setup watcher)[cursor + 1]? = some (.player watcher))
    (granted : execution.application.serviceGrant = some event)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (leaked : execution.network.leaked = fun _ => [])
    (inputs : ∀ input ∈ execution.network.inputs,
      input.envelope.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (ordinary : ∀ response ∈ (players owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)).support,
      response ∈ ordinaryActions setup leaks bounds owner (execution.recall owner)
        (execution.observe (application setup leaks) owner))
    (state : (application setup leaks).ProtocolState)
    (reached : state ∈ ((fun law => law.bind ((application setup leaks).controlStep
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher) players))^[3]
      (FinDist.pure (some ⟨remaining + 2, some owner, execution⟩))).support) :
    ∃ next, state = some ⟨remaining, some watcher, next⟩ ∧
      next.network.leaked = (fun _ => []) ∧
      (∀ message ∈ next.network.pending,
        message.id ∈ next.network.ledger.map Message.id) ∧
      (∀ input ∈ next.network.inputs,
        input.envelope.id ∈ next.network.ledger.map Message.id) := by
  let app := application setup leaks
  have first : app.controlStep (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) players (some ⟨remaining + 2, some owner, execution⟩) =
      (players owner (execution.recall owner) (execution.observe app owner)).map
        (fun response => some ⟨remaining + 2, none, execution.respond app owner response⟩) := by
    simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
      ReactiveApplication.transition, ↓reduceIte, Option.getD_some, FinDist.map_eq_bind]
    rfl
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    FinDist.pure_bind] at reached
  obtain ⟨afterInclude, firstTwo, activated⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨afterResponse, responded, middleReached⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ firstTwo)
  rw [first, FinDist.support_map] at responded
  obtain ⟨response, supported, rfl⟩ := responded
  have responsePosition : (execution.respond app owner response).environmentRecall.length =
      cursor := position
  rw [show remaining + 2 = (remaining + 1) + 1 by omega,
    include_control_step setup leaks players watcher owner event
      (execution.respond app owner response) (remaining + 1) cursor responsePosition includeAt,
    FinDist.support_map] at middleReached
  obtain ⟨next, included, rfl⟩ := middleReached
  obtain ⟨published, quiet, inputPublished⟩ :=
    ordinary_inclusion_published setup leaks bounds players
    watcher owner event execution granted pending leaked inputs serials response
      (ordinary response supported) next included
  have nextPosition : next.environmentRecall.length = cursor + 1 := by
    have count := (runtime setup).interactionStep_recall leaks players
      ((runtime setup).reportNetwork leaks watcher) (.includeLatest event owner)
      (execution.respond app owner response) next included
    simpa only [responsePosition] using count
  have scheduled : scheduler setup leaks watcher next.environmentRecall
      (next.observeEnvironment app) = FinDist.pure (.activate watcher) := by
    simp only [scheduler, nextPosition, watcherAt, interactionInstruction]
  change state ∈ ((scheduler setup leaks watcher next.environmentRecall
    (next.observeEnvironment app)).bind _).support at activated
  rw [scheduled, FinDist.pure_bind,
    next.activate_of_pending_published app watcher published,
    FinDist.map_pure, FinDist.mem_support_pure] at activated
  exact ⟨_, activated, quiet, published, inputPublished⟩

/-- At the watcher's exact service depth, every retained execution has no
unpublished leaked packet. This holds for every C behavioral profile. -/
theorem watcher_supported_clean (bounds : MessageBounds (graph setup))
    (watcher owner : Player) (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : Profile (information setup leaks bounds watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (history : (protocol setup leaks bounds watcher).History)
    (supported : history ∈ ((information setup leaks bounds watcher).runBehavioral profile
      (blockOffset event.val + 2 * event.val + 6)).support) :
    ∃ control : (application setup leaks).Control, history.state = some control ∧
      control.actor = some watcher ∧ control.execution.network.leaked = (fun _ => []) ∧
      (∀ message ∈ control.execution.network.pending,
        message.id ∈ control.execution.network.ledger.map Message.id) ∧
      (∀ input ∈ control.execution.network.inputs,
        input.envelope.id ∈ control.execution.network.ledger.map Message.id) := by
  let responses := menu setup leaks bounds watcher
  let model := information setup leaks bounds watcher
  let players := responses.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) profile
  let ownerDepth := blockOffset event.val + 2 * event.val + 3
  change history ∈ (model.runBehavioral profile (ownerDepth + 3)).support at supported
  rw [InformationModel.runBehavioral, InformationModel.runBehavioralFrom_add,
    FinDist.support_bind] at supported
  obtain ⟨before, beforeSupport, continued⟩ := Set.mem_iUnion₂.mp supported
  obtain ⟨boundary, boundarySupport, current, initial, _initialSupport, source,
      _boundaryCheckpoint, related, _decoded⟩ :=
    owner_supported setup leaks bounds watcher owner reveals observer openable profile
      event owned before beforeSupport
  let execution := ownerOpportunity setup leaks event owner boundary
  have pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id :=
    PrefixCheckpoint.runtime_fact (fun next => ∀ message ∈ next.network.pending,
      message.id ∈ next.network.ledger.map Message.id)
      (fun _ _ _ _ checkpoint => checkpoint.pending) _ _ _ _ _ _ _ _ related
  have leaked : execution.network.leaked = fun _ => [] :=
    PrefixCheckpoint.runtime_fact (fun next => next.network.leaked = fun _ => [])
      (fun _ _ _ _ checkpoint => checkpoint.leaked) _ _ _ _ _ _ _ _ related
  have inputs : ∀ input ∈ execution.network.inputs,
      input.envelope.id ∈ execution.network.ledger.map Message.id :=
    PrefixCheckpoint.runtime_fact (fun next => ∀ input ∈ next.network.inputs,
      input.envelope.id ∈ next.network.ledger.map Message.id)
      (fun _ _ _ _ checkpoint => checkpoint.inputs) _ _ _ _ _ _ _ _ related
  have serials : execution.network.SerialsBeforeNext :=
    PrefixCheckpoint.runtime_fact (fun next => next.network.SerialsBeforeNext)
      (fun _ _ _ _ checkpoint => checkpoint.serials) _ _ _ _ _ _ _ _ related
  have prefixLength := planPrefix_length setup watcher reveals event.val event.isLt.le
  obtain ⟨initialNative, _initialNativeSupport, prefixRun⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ boundarySupport)
  have position : execution.environmentRecall.length = blockOffset event.val + 2 := by
    have counted := (runtime setup).runInteractionPlan_recall leaks players
      ((runtime setup).reportNetwork leaks watcher) (planPrefix setup watcher event.val)
      (ReactiveApplication.Execution.initial (application setup leaks) initialNative)
      boundary prefixRun
    simp only [ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add,
      prefixLength] at counted
    simp only [execution, ownerOpportunity, List.length_append, List.length_singleton, counted]
  obtain ⟨rest, planEq⟩ := plan_split_at setup watcher event
  have includeAt : (plan setup watcher)[blockOffset event.val + 2]? =
      some (.includeLatest event owner) := by
    rw [planEq, List.append_assoc, List.getElem?_append_right (by omega), prefixLength,
      Nat.add_sub_cancel_left, block_of_owner setup watcher owner event owned]
    rfl
  have watcherAt : (plan setup watcher)[(blockOffset event.val + 2) + 1]? =
      some (.player watcher) := by
    rw [show (blockOffset event.val + 2) + 1 = blockOffset event.val + 3 by omega,
      planEq, List.append_assoc, List.getElem?_append_right (by omega), prefixLength,
      Nat.add_sub_cancel_left, block_of_owner setup watcher owner event owned]
    rfl
  have room : blockOffset event.val + 4 ≤ horizon setup watcher := by
    have lengths := congrArg List.length planEq
    rw [List.length_append, List.length_append, prefixLength,
      block_length setup watcher reveals] at lengths
    change blockOffset event.val + 4 ≤ (plan setup watcher).length
    omega
  have stateSupport : history.state ∈ ((model.runBehavioralFrom profile 3 before).map
      History.state).support := by
    rw [FinDist.support_map]
    exact ⟨history, continued, rfl⟩
  rw [menu_run_control_steps, current] at stateSupport
  have remaining : horizon setup watcher - blockOffset event.val - 2 =
      (horizon setup watcher - blockOffset event.val - 4) + 2 := by omega
  rw [remaining] at stateSupport
  have different : owner ≠ watcher := fun same => observer event (same ▸ owned)
  obtain ⟨next, stateEq, quiet, pendingPublished, inputPublished⟩ :=
    owner_to_watcher_clean setup leaks bounds players
    watcher owner event execution (horizon setup watcher - blockOffset event.val - 4)
    (blockOffset event.val + 2) position includeAt watcherAt rfl pending leaked inputs serials
    (menu_decode_ordinary setup leaks bounds watcher profile owner different _ _)
    history.state stateSupport
  exact ⟨_, stateEq, rfl, quiet, pendingPublished, inputPublished⟩

/-- Every actual watcher decision in the retained game executes silence.
The proof uses legal history support, not the selected equilibrium profile. -/
theorem watcher_history_clean (bounds : MessageBounds (graph setup))
    (watcher : Player) (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (history : (protocol setup leaks bounds watcher).History)
    (control : (application setup leaks).Control) (state : history.state = some control)
    (active : control.actor = some watcher) :
    control.execution.network.leaked = (fun _ => []) ∧
      (∀ message ∈ control.execution.network.pending,
        message.id ∈ control.execution.network.ledger.map Message.id) ∧
      (∀ input ∈ control.execution.network.inputs,
        input.envelope.id ∈ control.execution.network.ledger.map Message.id) := by
  let responses := menu setup leaks bounds watcher
  let reference := responses.uniformPolicy (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)
  have supported := (responses.uniform_fullyMixed (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)).history_supported history.trace
  obtain ⟨rawTrace, rawLength⟩ : ∃ rawTrace : ((application setup leaks).protocol
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).Trace
        (some control), rawTrace.length = history.trace.length := by
    rcases history with ⟨current, trace⟩
    cases state
    exact ⟨responses.toRawTrace (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) trace, responses.toRawTrace_length ..⟩
  obtain ⟨event, _granted, located⟩ := raw_decision_calendar setup leaks watcher watcher
    reveals control rawTrace active
  have position : control.execution.environmentRecall.length = blockOffset event.val + 4 := by
    rcases located with ⟨_position, owned⟩ | ⟨position, _same⟩
    · exact (observer event owned).elim
    · exact position
  obtain ⟨owner, owned⟩ := source_owner setup reveals event
  have depth := raw_watcher_decision_depth setup leaks watcher owner reveals event owned
    control rawTrace active position
  have actualDepth : history.trace.length = blockOffset event.val + 2 * event.val + 6 :=
    rawLength.symm.trans depth
  have atDepth : history ∈ ((information setup leaks bounds watcher).runBehavioral reference
      (blockOffset event.val + 2 * event.val + 6)).support := by
    simpa only [actualDepth, ReactiveApplication.ResponseMenu.uniformAssessment,
      InformationModel.BehavioralAssessment.ofStrategy] using supported
  obtain ⟨reachedControl, reachedState, _reachedActor, clean⟩ := watcher_supported_clean
    setup leaks bounds watcher owner reveals observer openable reference event owned history atDepth
  have same : reachedControl = control := Option.some.inj (reachedState.symm.trans state)
  subst reachedControl
  exact clean

/-- The prescribed watcher response is silent at every actual retained site. -/
theorem watcher_history_silent (bounds : MessageBounds (graph setup))
    (watcher : Player) (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (history : (protocol setup leaks bounds watcher).History)
    (control : (application setup leaks).Control) (state : history.state = some control)
    (active : control.actor = some watcher) :
    (application setup leaks).reportFirstUnpublished (control.execution.recall watcher)
      (control.execution.observe (application setup leaks) watcher) = FinDist.pure ⟨none⟩ := by
  have quiet := (watcher_history_clean setup leaks bounds watcher reveals observer openable
    history control state active).1
  apply (application setup leaks).reportFirstUnpublished_silent
  intro message seen
  change message ∈ control.execution.network.leaked watcher at seen
  rw [quiet] at seen
  exact (List.not_mem_nil seen).elim

end Vegas
