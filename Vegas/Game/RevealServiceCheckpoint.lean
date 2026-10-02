/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceBlock
import Vegas.Game.RevealServiceCalendarState
import Vegas.Pending.ReactiveServiceRecall
import Vegas.Game.RevealServiceTranscript
import Vegas.EventGraph.PrivateInputs
import Vegas.Pending.ReactiveResponseRecall
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventSequentialTiming
import Vegas.Source.RevealSequence
import Vegas.Source.SetupProtocol

/-! # Checkpoint invariants for the actual revelation service

The relation records facts about the existing source configuration and native
execution. In particular, native response recall and rebroadcast inputs remain
untouched. Only published envelopes may remain pending between source events.
No strategic correspondence or optimal assessment is a field of this relation.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Source/application correspondence and source-determined public metadata.
Pending copies, private leak lists and response recall are auxiliary execution
data; no condition here identifies or erases them. -/
structure PublicCheckpoint (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (initial : State L setup.context) {Γ : SourceCtx Player L}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (rank : Nat) (execution : (application setup leaks).Execution) : Prop where
  emptyRegistry : source.registry = []
  openable : source.state.BindingsOpenable
  agrees : refs.Agrees source.state execution.application.config.store
  history : decodeHistory setup.program
    (execution.application.config.history.map
      (setup.eventGraph.fromModeCompletion .sequential)) = source.history
  ordered : execution.application.config.cut.IsPrefix rank
  invariant : EventGraphRuntime.State.Invariant (graph := graph setup)
    (setup.eventInputs initial) execution.application
  binding : execution.application.BindingInvariant
  accepted : execution.application.accepted =
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
  candidates : execution.application.candidates =
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).candidates
  remembered : execution.application.remembered = fun _ => none
  timely : ∀ event, event.val = rank → ((graph setup).actor? event).isSome = true →
    execution.application.WithinDeadline (runtime setup) event
  reveals : setup.program.RevealOnly
  covered : refs.CoversPrefix setup.program rank
  ledger : execution.network.ledger = publicationLedger
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
    ((graph setup).publicObserve execution.application.config)
  receipts : execution.receipts = publicationReceipts
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
    ((graph setup).publicObserve execution.application.config)
  counters : execution.network.nextSerial = publicationSerial
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
    ((graph setup).publicObserve execution.application.config)
  clock : execution.application.clock = clockAt rank
  activated : execution.application.activatedAt = checkpointActivations setup
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
    ((graph setup).publicObserve execution.application.config) rank

/-- The fixed one-owner service additionally has empty private leak lists.
This specialization is useful for that calendar's exact observation theorem;
delayed-inclusion rosters instead retain their published private leak history. -/
structure Checkpoint (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (initial : State L setup.context) {Γ : SourceCtx Player L}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (rank : Nat) (execution : (application setup leaks).Execution) : Prop
    extends PublicCheckpoint setup leaks initial source refs rank execution where
  pending : ∀ message ∈ execution.network.pending,
    message.id ∈ execution.network.ledger.map Message.id
  leaked : execution.network.leaked = fun _ => []
  inputs : ∀ input ∈ execution.network.inputs,
    input.envelope.id ∈ execution.network.ledger.map Message.id
  serials : execution.network.SerialsBeforeNext
  recall : execution.InputRecall (application setup leaks)

/-- The induction starts at every supplied valid source state, without any
independence restriction on its private cells. -/
theorem checkpoint_initial (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (reveals : setup.program.RevealOnly)
    (initial : State L setup.context) (openable : initial.BindingsOpenable) :
    Checkpoint setup leaks initial (setup.initialConfig initial)
      (ContextRefs.initial setup.context (outputLayout setup.program)) 0
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial))) := by
  refine {
    emptyRegistry := rfl
    openable := openable
    agrees := initial_agrees setup initial
    history := initial_history setup initial
    ordered := ?_
    invariant := EventGraphRuntime.State.initial_invariant _
    binding := EventGraphRuntime.State.initial_bindingInvariant _
    accepted := rfl
    candidates := rfl
    remembered := rfl
    pending := ?_
    leaked := rfl
    inputs := ?_
    serials := MessageNetwork.SerialsBeforeNext.empty
    recall := (application setup leaks).initial_inputRecall _
    timely := ?_
    reveals := reveals
    covered := ContextRefs.initial_coversPrefix setup.program
    ledger := rfl
    receipts := rfl
    counters := rfl
    clock := rfl
    activated := ?_ }
  · exact EventOrder.Cut.empty_isPrefix _
  · intro event first strategic
    apply EventGraphRuntime.State.initial_withinDeadline _ (runtime setup) event _ strategic
      (runtime_deadline_pos setup event)
    have start := EventOrder.Cut.empty_isPrefix (graph setup).order
    have positive : 0 < (graph setup).order.eventCount := by omega
    have same : (⟨0, positive⟩ : (graph setup).EventId) = event := Fin.ext first.symm
    rw [← same]
    exact start.ready positive
  · exact (initial_calendar setup reveals (setup.eventInputs initial) _).2
  · simp only [ReactiveApplication.Execution.initial, MessageNetwork.empty,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · simp only [ReactiveApplication.Execution.initial, MessageNetwork.empty,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]

/-- Every known packet at a checkpoint is already public, including remembered
own transmissions and earlier rebroadcasts. -/
theorem Checkpoint.known_published {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : Checkpoint setup leaks initial source refs rank execution) (who : Player) :
    ∀ message ∈ execution.network.known who,
      message.id ∈ execution.network.ledger.map Message.id := by
  apply execution.network.known_published who checkpoint.inputs
  simp only [checkpoint.leaked, List.not_mem_nil, IsEmpty.forall_iff, implies_true]

/-- At a checkpoint of some rank, the event of that rank is ready. -/
theorem PublicCheckpoint.ready {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : PublicCheckpoint setup leaks initial source refs rank execution)
    (event : (graph setup).EventId) (eventRank : event.val = rank) :
    execution.application.config.cut.Ready event := by
  have inside : rank < (graph setup).order.eventCount := eventRank ▸ event.isLt
  have same : (⟨rank, inside⟩ : (graph setup).EventId) = event := Fin.ext eventRank.symm
  rw [← same]
  exact checkpoint.ordered.ready inside

/-- At matched source ranks, the actual public metadata formulas make the
native before-view a function of the source view. This permits different
initial private states and does not identify the players' replay recalls. -/
theorem PublicCheckpoint.observe_eq {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {leftInitial rightInitial : State L setup.context} {Γ : SourceCtx Player L}
    {left right : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {nativeLeft nativeRight : (application setup leaks).Execution}
    (leftCheckpoint : PublicCheckpoint setup leaks leftInitial left refs rank nativeLeft)
    (rightCheckpoint : PublicCheckpoint setup leaks rightInitial right refs rank nativeRight)
    (who : Player)
    (leaked : nativeLeft.network.leaked who = nativeRight.network.leaked who)
    (same : left.view who = right.view who) :
    nativeLeft.observe (application setup leaks) who =
      nativeRight.observe (application setup leaks) who := by
  have leftCandidates : nativeLeft.application.candidates =
      (EventGraphRuntime.State.initial (graph := graph setup)
        nativeLeft.application.config.inputs).candidates := by
    rw [leftCheckpoint.invariant.reachable.inputs_eq]
    exact leftCheckpoint.candidates
  have rightCandidates : nativeRight.application.candidates =
      (EventGraphRuntime.State.initial (graph := graph setup)
        nativeRight.application.config.inputs).candidates := by
    rw [rightCheckpoint.invariant.reachable.inputs_eq]
    exact rightCheckpoint.candidates
  exact source_checkpoint_observe_eq setup leaks refs rank leftCheckpoint.covered
    who left right nativeLeft
    nativeRight leftCheckpoint.invariant.reachable rightCheckpoint.invariant.reachable
    leftCheckpoint.ordered rightCheckpoint.ordered leftCheckpoint.agrees rightCheckpoint.agrees
    leftCheckpoint.history rightCheckpoint.history leftCandidates rightCandidates
    (EventGraphRuntime.State.initial (graph := graph setup)
      (setup.eventInputs leftInitial)).accepted
    leftCheckpoint.accepted rightCheckpoint.accepted leftCheckpoint.clock rightCheckpoint.clock
    leftCheckpoint.activated rightCheckpoint.activated leftCheckpoint.ledger rightCheckpoint.ledger
    leaked
    leftCheckpoint.receipts rightCheckpoint.receipts same

/-- Empty leakage discharges the auxiliary observation premise of the
shared public checkpoint theorem. -/
theorem Checkpoint.observe_eq {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {leftInitial rightInitial : State L setup.context} {Γ : SourceCtx Player L}
    {left right : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {nativeLeft nativeRight : (application setup leaks).Execution}
    (leftCheckpoint : Checkpoint setup leaks leftInitial left refs rank nativeLeft)
    (rightCheckpoint : Checkpoint setup leaks rightInitial right refs rank nativeRight)
    (who : Player)
    (same : left.view who = right.view who) :
    nativeLeft.observe (application setup leaks) who =
      nativeRight.observe (application setup leaks) who :=
  leftCheckpoint.toPublicCheckpoint.observe_eq rightCheckpoint.toPublicCheckpoint who
    (by rw [leftCheckpoint.leaked, rightCheckpoint.leaked]) same

/-- Matching source views and an already matching focal alias prefix also
reconstruct the next whole recall entry, including its emitted packet. -/
theorem Checkpoint.respond_recall_eq {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {leftInitial rightInitial : State L setup.context} {Γ : SourceCtx Player L}
    {left right : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {nativeLeft nativeRight : (application setup leaks).Execution}
    (leftCheckpoint : Checkpoint setup leaks leftInitial left refs rank nativeLeft)
    (rightCheckpoint : Checkpoint setup leaks rightInitial right refs rank nativeRight)
    (who : Player)
    (same : left.view who = right.view who)
    (past : nativeLeft.recall who = nativeRight.recall who)
    (response : (application setup leaks).Action) :
    (nativeLeft.respond (application setup leaks) who response).recall who =
      (nativeRight.respond (application setup leaks) who response).recall who := by
  have views := leftCheckpoint.observe_eq rightCheckpoint who same
  have publicViews := congrArg (fun view : (application setup leaks).PlayerView =>
    view.application.publicView.observation) views
  change (graph setup).publicObserve nativeLeft.application.config =
    (graph setup).publicObserve nativeRight.application.config at publicViews
  apply respond_recall_eq_of_input_eq (runtime setup) leaks nativeLeft nativeRight who response
    leftCheckpoint.recall rightCheckpoint.recall past views
    (leftCheckpoint.remembered.trans rightCheckpoint.remembered.symm)
  rw [leftCheckpoint.counters, rightCheckpoint.counters, publicViews]
  rfl

/-- Owner activation reaches the actual response opportunity. Passive sampling
is inert here because every pending identifier is already public. -/
theorem Checkpoint.owner_opportunity
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : Checkpoint setup leaks initial source refs rank execution)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (owner : Player) :
    ∃ opportunity, Checkpoint setup leaks initial source refs rank opportunity ∧
      opportunity.application = execution.application ∧
      (runtime setup).runInteractionPlan leaks players network [.player owner] execution =
        (players owner (opportunity.recall owner)
          (opportunity.observe (application setup leaks) owner)).map
            (opportunity.respond (application setup leaks) owner) ∧
      opportunity.recall = execution.recall := by
  let app := application setup leaks
  let activated : app.Execution := { execution with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate owner⟩] }
  refine ⟨activated, ?_, rfl, ?_, rfl⟩
  · exact { checkpoint with
      invariant := checkpoint.invariant.copy rfl rfl rfl
      binding := checkpoint.binding.copy rfl rfl rfl }
  · simp only [runInteractionPlan, PMF.bind_pure]
    exact (runtime setup).player_instruction_published leaks players network
      execution owner checkpoint.pending

private theorem ordinary_network_checkpoint [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (execution : (application setup leaks).Execution) (owner : Player)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (inputs : ∀ input ∈ execution.network.inputs,
      input.envelope.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)) :
    let submitted := execution.respond (application setup leaks) owner response
    let after := if sourceChoice setup leaks response then
      (submitted.network.includePending (owner, execution.network.nextSerial owner)).2
      else submitted.network
    (∀ message ∈ after.pending, message.id ∈ after.ledger.map Message.id) ∧
      (∀ input ∈ after.inputs, input.envelope.id ∈ after.ledger.map Message.id) ∧
      after.leaked = execution.network.leaked ∧ after.SerialsBeforeNext := by
  cases chosen : sourceChoice setup leaks response with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain refuses := (ordinary_false_iff setup leaks bounds owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) response member).mp chosen
      rcases refuses with rfl | ⟨message, published, rfl⟩
      · exact ⟨pending, inputs, rfl, serials⟩
      · have spent : message.id ∈ execution.network.ledger.map Message.id :=
          List.mem_map.mpr ⟨message, published, rfl⟩
        refine ⟨execution.network.replay_pending_published owner message.id pending spent,
          execution.network.replay_inputs_published owner message.id inputs spent, ?_,
          serials.replay owner message.id⟩
        funext observer
        exact congrArg MessageNetwork.PlayerView.leaked
          (execution.network.replay_observe owner observer message.id)
  | true =>
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => cases chosen
      | some transmission =>
          cases transmission with
          | replay id => cases chosen
          | submit submission =>
              exact execution.network.submit_include_published owner _ pending inputs serials

/-- Every ordinary response advances the full operational relation. Policies
after the response are unrestricted except for the fixed watcher, which is
silent at these published-only checkpoints. -/
theorem Checkpoint.reveal_response [Fintype Player]
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : Checkpoint setup leaks initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy) (watcher : Player)
    (policy : players watcher = (application setup leaks).silentPolicy)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (ownedEvent : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : ∀ disclose, decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal owner name disclose))
    (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)) :
    ∃ next, (runtime setup).runInteractionPlan leaks players
        ((runtime setup).idleNetwork leaks)
        ([.includeLatest event owner, .player watcher, .wire] ++
          List.replicate (event.val + 1) .tick ++ [.expire event])
        (execution.respond (application setup leaks) owner response) = PMF.pure next ∧
      Checkpoint setup leaks initial
        (revealSuccessor published selected source (sourceChoice setup leaks response))
        (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1) next ∧
      ∀ observer, observer ≠ watcher → next.recall observer =
        (execution.respond (application setup leaks) owner response).recall observer := by
  let app := application setup leaks
  let submitted := execution.respond app owner response
  let suffix : List (ServiceInstruction (graph setup)) :=
    [.includeLatest event owner, .player watcher, .wire] ++
      List.replicate (event.val + 1) .tick ++ [.expire event]
  have ready : execution.application.config.cut.Ready event :=
    checkpoint.ready event eventRank
  have strategic : ((graph setup).actor? event).isSome = true := by rw [ownedEvent]; rfl
  have timely := checkpoint.timely event eventRank strategic
  obtain ⟨entered, activated⟩ := checkpoint.invariant.activatedAt_eq_some_of_ready_actor
    event ready strategic
  have due := checkpoint.invariant.due_after_deadline (runtime setup) event entered activated
  obtain ⟨value, bound⟩ := checkpoint.openable selected
  obtain ⟨next, law, applicationEq, networkEq, receiptsEq, recallEq⟩ :=
    ordinary_response_settlement setup leaks bounds players watcher policy selected source.state
      refs execution checkpoint.agrees checkpoint.binding event ownedEvent outputEq codeEq node
      value bound ready timely entered (event.val + 1) activated due checkpoint.pending
      checkpoint.serials response member
  obtain ⟨sourceNext, sourceLaw, store, history⟩ :=
    ordinary_response_source_step setup leaks bounds players watcher policy published selected
      source checkpoint.emptyRegistry refs execution checkpoint.agrees checkpoint.history
      checkpoint.binding event ownedEvent outputEq codeEq node before decoded value bound
      ready timely entered (event.val + 1) activated due checkpoint.pending checkpoint.serials
      response member
  have sourceSame : sourceNext = next := (PMF.mem_support_pure_iff _ _).mp (by
    rw [← law, sourceLaw]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  subst sourceNext
  let action := cast (congrArg EventGraph.EventField.Action outputEq.symm)
    (sourceChoice setup leaks response)
  let result := cast (congrArg EventGraph.EventField.Value outputEq.symm)
    (if sourceChoice setup leaks response then PublicationResult.success value else .failure)
  have configEq : next.application.config =
      (execution.application.complete event ready action result).config := by
    dsimp only [action, result]
    rw [applicationEq]
    cases sourceChoice setup leaks response <;> rfl
  have tables : next.application.accepted = execution.application.accepted ∧
      next.application.candidates = execution.application.candidates ∧
      next.application.remembered = execution.application.remembered := by
    rw [applicationEq]
    cases sourceChoice setup leaks response <;> exact ⟨rfl, rfl, rfl⟩
  have supported : next ∈ ((runtime setup).runInteractionPlan leaks players
      ((runtime setup).idleNetwork leaks) suffix submitted).support := by
    rw [show (runtime setup).runInteractionPlan leaks players
        ((runtime setup).idleNetwork leaks) suffix submitted = PMF.pure next
      from law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have progressed := (runtime setup).runInteractionPlan_facts leaks
    (setup.eventInputs initial) players ((runtime setup).idleNetwork leaks)
    suffix submitted next
    ((runtime setup).reactiveStateInvariant leaks (setup.eventInputs initial) |>.respond
      execution owner response checkpoint.invariant) supported
  have boundAfter := checkpoint.binding.complete_nonbinding event ready action result (by
    intro other otherPayload bindingEq
    cases outputEq.symm.trans bindingEq)
  have networkClean := ordinary_network_checkpoint setup leaks bounds execution owner
    checkpoint.pending checkpoint.inputs checkpoint.serials response member
  dsimp only at networkClean
  rw [← networkEq] at networkClean
  have recallInvariant : app.PolicyInvariant players (fun state => state.InputRecall app) := {
    respond state who reply valid _ := app.respond_inputRecall state who reply valid
    environment state after command valid moved :=
      app.environment_inputRecall state after command valid moved }
  let initialAccepted :=
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
  have transcript := ordinary_response_transcript setup leaks bounds selected source.state refs
    execution next checkpoint.agrees checkpoint.binding checkpoint.recall checkpoint.serials
    initialAccepted checkpoint.accepted event ownedEvent outputEq codeEq node value bound
    ready response member checkpoint.ledger checkpoint.receipts checkpoint.counters configEq
    networkEq receiptsEq
  obtain ⟨candidate, associated, _owned, _verified, _opening⟩ :=
    opening_at_checkpoint setup leaks selected source.state refs execution checkpoint.agrees
      checkpoint.binding event ownedEvent outputEq codeEq node
      (ownTurn?_of_ready setup execution.application ready ownedEvent) value bound
  rw [checkpoint.accepted] at associated
  change initialAccepted (refs.get selected).field = some candidate at associated
  have packetPresence : (publicationPacket? initialAccepted
      (execution.application.config.complete event ready action result).store event).isSome =
      sourceChoice setup leaks response := by
    cases chosen : sourceChoice setup leaks response with
    | false =>
        simp only [result, chosen, Bool.false_eq_true, ↓reduceIte]
        rw [publicationPacket?_complete_resolve initialAccepted execution.application.config
          event ready owner payload (refs.get selected) [] outputEq codeEq node action .failure]
        rfl
    | true =>
        simp only [result, chosen, ↓reduceIte]
        rw [publicationPacket?_complete_resolve initialAccepted execution.application.config
          event ready owner payload (refs.get selected) [] outputEq codeEq node action
            (.success value)]
        change ((initialAccepted (refs.get selected).field).map _).isSome = true
        rw [associated]
        rfl
  have calendar := settlement_calendar setup checkpoint.reveals execution.application
    checkpoint.invariant event ready action result (sourceChoice setup leaks response)
    initialAccepted (eventRank.symm ▸ checkpoint.clock) packetPresence
  have actualCalendar : next.application.clock = clockAt (rank + 1) ∧
      next.application.activatedAt = checkpointActivations setup initialAccepted
        ((graph setup).publicObserve next.application.config) (rank + 1) := by
    rw [applicationEq]
    simpa only [eventRank] using calendar
  refine ⟨next, law, ?_, recallEq⟩
  refine {
    emptyRegistry := revealSuccessor_registry_empty published selected source
      checkpoint.emptyRegistry _
    openable := revealSuccessor_bindingsOpenable published selected source checkpoint.openable _
    agrees := @store
    history := history
    ordered := ?_
    invariant := progressed.invariant
    binding := ?_
    accepted := tables.1.trans checkpoint.accepted
    candidates := tables.2.1.trans checkpoint.candidates
    remembered := tables.2.2.trans checkpoint.remembered
    pending := networkClean.1
    leaked := networkClean.2.2.1.trans checkpoint.leaked
    inputs := networkClean.2.1
    serials := networkClean.2.2.2
    recall := ?_
    timely := ?_
    reveals := checkpoint.reveals
    covered := checkpoint.covered.cons setup.program (cell := .publication payload)
      ⟨.inr event, outputEq⟩ event rfl eventRank
    ledger := transcript.1
    receipts := transcript.2.1
    counters := transcript.2.2
    clock := actualCalendar.1
    activated := actualCalendar.2 }
  · rw [configEq]
    exact checkpoint.ordered.complete_at event ready eventRank
  · exact boundAfter.copy configEq tables.1 tables.2.1
  · intro successor nextRank actor
    rw [applicationEq]
    exact settlement_successor_timely setup execution.application checkpoint.invariant
      event successor ready (by omega) actor action result (sourceChoice setup leaks response)
  · exact (runtime setup).runInteractionPlan_preserves leaks players
      ((runtime setup).idleNetwork leaks)
      _ recallInvariant suffix submitted next
      (app.respond_inputRecall execution owner response checkpoint.recall) supported

end Vegas
