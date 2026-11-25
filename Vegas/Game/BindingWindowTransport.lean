module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.AsyncDeviationForeign
public import Interaction.ReactiveResponseAccounting
public import Interaction.ReactiveEnvironmentStep
public import Vegas.EventGraph.RevealRelaxation
public import Vegas.EventGraph.BindingSubmission

@[expose] public section

/-! # Native opacity through private-binding windows

Canonical submitting clients keep honest binding values out of public packet
traffic. The coupling retains the deviator's complete native traffic and each
owner's turn and submission counters, while allowing other owners' bindings
to complete. Private inputs and behavioral kernels may vary jointly.

These are local and stopped native traffic laws. They do not assert a source
continuation law or equilibrium preservation across publication boundaries.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

theorem round_ready_of_unfinished
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    {before after : (serviceApplication setup deps duration leaks).Execution}
    {event : (serviceGraph setup deps).EventId}
    (ready : before.application.config.cut.Ready event)
    (unfinished : event ∉ after.application.config.cut.completed)
    (moved : after ∈ ((serviceApplication setup deps duration leaks).round scheduler players
      before).support) : after.application.config.cut.Ready event :=
  Config.Step.path_ready_of_not_completed
    (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler players
      before after moved) ready unfinished

theorem binding_ready_handler_congr
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {event : (serviceGraph setup deps).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (left right : EventGraphRuntime.State (serviceGraph setup deps)) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (leftReady : left.config.cut.Ready event)
    (message : Message Player (Payload (serviceGraph setup deps))) :
    (handle (serviceTimeouts setup deps duration) left message).map
        (fun state => state.playerView focal) =
      (handle (serviceTimeouts setup deps duration) right message).map
        (fun state => state.playerView focal) := by
  classical
  have cuts := cut_eq_of_publicView_eq (congrArg PlayerView.publicView views)
  obtain ⟨id, packet⟩ := message
  cases packet with
  | malformed raw => simp [handle]
  | commitment named candidate =>
      exact handle_commitment_playerView_congr _ left right focal id named candidate views
  | opening named candidate raw =>
      by_cases namedReady : left.config.cut.Ready named
      · have notPublication : ¬ ((serviceGraph setup deps).outputLayout named).IsPublication := by
          by_cases same : event = named
          · subst named
            rw [outputEq]
            simp [EventField.IsPublication]
          · intro publication
            have both := relaxed.ready_public_pair_publications left.config.cut leftReady
              namedReady same (Or.inr publication.isPublic)
            rw [outputEq] at both
            simp [EventField.IsPublication] at both
        have rightReady : right.config.cut.Ready named := by
          rw [← cuts]
          exact namedReady
        cases namedNode : nodeView (serviceGraph setup deps) named with
        | bind who ty outputEq codeEq =>
            simp [handle, namedReady, rightReady, namedNode]
        | sample ty law outputEq codeEq =>
            simp [handle, namedReady, rightReady, namedNode]
        | resolve who ty binding checks outputEq codeEq =>
            exact (notPublication (by rw [outputEq]; trivial)).elim
      · have rightNot : ¬ right.config.cut.Ready named := by
          rw [← cuts]
          exact namedReady
        simp [handle, namedReady, rightNot]


theorem environmentStep_pure_of_readyBinding
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {event : (serviceGraph setup deps).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (command : (serviceApplication setup deps duration leaks).Command)
    (inactive : command.actor? (serviceApplication setup deps duration leaks) = none) :
    ∃ next, execution.environmentStep (serviceApplication setup deps duration leaks) command =
      PMF.pure next := by
  classical
  let app := serviceApplication setup deps duration leaks
  cases command with
  | activate actor => cases inactive
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
      exact ⟨_, rfl⟩
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
      exact ⟨_, rfl⟩
  | application op =>
    have pureNative : ∃ state, environmentStep (serviceTimeouts setup deps duration)
        execution.application op = PMF.pure state := by
      cases op with
      | advanceClock => exact ⟨_, rfl⟩
      | expire named => exact ⟨_, rfl⟩
      | executeSample named =>
          by_cases namedReady : execution.application.config.cut.Ready named
          · cases namedNode : nodeView (serviceGraph setup deps) named with
            | sample ty law namedOutput namedCode =>
                have different : event ≠ named := by
                  intro same
                  subst named
                  rw [outputEq] at namedOutput
                  cases namedOutput
                have both := relaxed.ready_public_pair_publications
                  execution.application.config.cut ready namedReady different
                  (Or.inr (by rw [namedOutput]; trivial))
                rw [outputEq] at both
                simp [EventField.IsPublication] at both
            | bind who ty namedOutput namedCode =>
                exact ⟨_, environmentStep_executeSample_of_nonsample _ _ _ namedReady
                  (by intros; simp_all)⟩
            | resolve who ty binding checks namedOutput namedCode =>
                exact ⟨_, environmentStep_executeSample_of_nonsample _ _ _ namedReady
                  (by intros; simp_all)⟩
          · exact ⟨_, environmentStep_executeSample_of_not_ready _ _ _ namedReady⟩
    obtain ⟨state, pureNative⟩ := pureNative
    refine ⟨{ execution with application := state.drain, environmentRecall :=
      execution.environmentRecall ++ [⟨execution.observeEnvironment app, .application op⟩] }, ?_⟩
    have servicePure : (serviceApplication setup deps duration leaks).environment
        execution.application op = PMF.pure state.drain := by
      change (environmentStep (serviceTimeouts setup deps duration) execution.application op).map
        State.drain = _
      rw [pureNative, PMF.pure_map]
    simp only [ReactiveApplication.Execution.environmentStep, servicePure, PMF.pure_map]
    rfl


theorem reference_first_turn_action_mixture
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (selected : execution.application.publicView.ownTurn? owner = some event)
    (active : owner ∉ execution.application.config.defaulted)
    (first : ownerTurns owner event execution = 0) :
    turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference owner (execution.logs owner)
          (execution.observe (serviceApplication setup deps duration leaks) owner) =
      (reference owner event owned
        ((serviceGraph setup deps).playerObserve owner execution.application.config) active).bind
          (fun action => decidedTurnPolicy setup leaks bound owner event action
            (execution.logs owner)
              (execution.observe (serviceApplication setup deps duration leaks) owner)) := by
  have turn : turnIndex (serviceTimeouts setup deps duration)
    leaks owner event (execution.logs owner)
      (execution.observe (serviceApplication setup deps duration leaks) owner) = some 0 := by
    rw [serviceTurn_of_turn execution selected, first]
  rw [sourceServiceTurnPolicy_firstTurn_reference owned turn]
  have decided (action : (serviceGraph setup deps).Action event) :=
    decidedTurnPolicy_open (bound := bound) action execution selected first
  simp_rw [decided]
  unfold EventGraphRuntime.referenceOpportunity
  by_cases recorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
      (execution.logs owner) event = true
  · simp only [recorded, ite_true, ReactiveApplication.silentPolicy_apply]
    simp only [fixedOpportunity, recorded, ite_true, ReactiveApplication.silentPolicy_apply,
      PMF.bind_const]
  · have unrecorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
        (execution.logs owner) event = false := Bool.eq_false_iff.mpr recorded
    simp only [unrecorded, Bool.false_eq_true, ite_false]
    by_cases fits : (execution.observe (serviceApplication setup deps duration leaks)
        owner).application.publicView.InclusionFitsDeadline
          (serviceTimeouts setup deps duration) bound event
    · simp only [fits, ite_true]
      rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks reference owner execution
        event selected owned, dite_eq_right active]
      simp only [PMF.bind_map, Function.comp_def, fixedOpportunity, unrecorded,
        Bool.false_eq_true, ite_false, fits, ite_true]
      rfl
    · simp only [fits, ite_false, ReactiveApplication.silentPolicy_apply]
      simp only [fixedOpportunity, unrecorded, Bool.false_eq_true, ite_false, fits,
        ReactiveApplication.silentPolicy_apply, PMF.bind_const]



/-- Native focal traffic and each owner's public counters during a private-binding window. -/
private def bindingWindowReadout (focal : Player)
    (execution : (serviceApplication setup deps duration leaks).Execution) :=
  ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal execution,
    fun owner : Player => fun event : (serviceGraph setup deps).EventId =>
      (ownerTurns owner event execution,
        (eventRecorded (serviceTimeouts setup deps duration)) leaks (execution.logs owner) event))

private theorem bindingWindowReadout_activation (focal actor : Player)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (same : bindingWindowReadout (leaks := leaks) focal left =
      bindingWindowReadout (leaks := leaks) focal right)
    (sample : Finset (MessageId Player)) :
    bindingWindowReadout (leaks := leaks) focal
        (left.sampledActivation (serviceApplication setup deps duration leaks) actor sample) =
      bindingWindowReadout (leaks := leaks) focal
        (right.sampledActivation (serviceApplication setup deps duration leaks) actor sample) :=
  by
    apply Prod.ext (bindingTraffic_activation _ leaks left right focal actor
      (congrArg Prod.fst same) sample)
    change (bindingWindowReadout (leaks := leaks) focal left).2 =
      (bindingWindowReadout (leaks := leaks) focal right).2
    exact congrArg Prod.snd same

private theorem bindingWindowReadout_response
    (focal actor : Player)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (same : bindingWindowReadout (leaks := leaks) focal left =
      bindingWindowReadout (leaks := leaks) focal right)
    (leftResponse rightResponse : (serviceApplication setup deps duration leaks).Action)
    (submitted : (submittedEvent? (serviceTimeouts setup deps duration)) leaks leftResponse =
      (submittedEvent? (serviceTimeouts setup deps duration)) leaks rightResponse)
    (traffic : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
        (left.respond (serviceApplication setup deps duration leaks) actor leftResponse) =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
        (right.respond (serviceApplication setup deps duration leaks) actor rightResponse)) :
    bindingWindowReadout (leaks := leaks) focal
        (left.respond (serviceApplication setup deps duration leaks) actor leftResponse) =
      bindingWindowReadout (leaks := leaks) focal
        (right.respond (serviceApplication setup deps duration leaks) actor rightResponse) := by
  let app := serviceApplication setup deps duration leaks
  refine Prod.ext traffic ?_
  funext owner event
  have counters : (ownerTurns owner event left,
      (eventRecorded (serviceTimeouts setup deps duration)) leaks (left.logs owner) event) =
    (ownerTurns owner event right,
      (eventRecorded (serviceTimeouts setup deps duration)) leaks (right.logs owner) event) :=
    congrFun (congrFun (congrArg Prod.snd same) owner) event
  by_cases isActor : owner = actor
  · subst owner
    obtain ⟨_, leftRecalled, _⟩ := respond_recall_self _ leaks left actor leftResponse
    obtain ⟨_, rightRecalled, _⟩ := respond_recall_self _ leaks right actor rightResponse
    apply Prod.ext
    · have sameTurns : ownerTurns actor event left = ownerTurns actor event right :=
        congrArg Prod.fst counters
      have publics : (left.observe app actor).application.publicView =
          (right.observe app actor).application.publicView :=
        congrArg (fun value => value.2.2.2.2.2) (congrArg Prod.fst same)
      change ownerTurns actor event (left.respond app actor leftResponse) =
        ownerTurns actor event (right.respond app actor rightResponse)
      unfold ownerTurns
      rw [leftRecalled, rightRecalled, List.countP_append, List.countP_append]
      change ownerTurns actor event left + _ = ownerTurns actor event right + _
      rw [sameTurns]
      congr 1
      simp only [List.countP_singleton]
      rw [publics]
    · have sameRecorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
          (left.logs actor) event =
        (eventRecorded (serviceTimeouts setup deps duration)) leaks (right.logs actor) event :=
        congrArg Prod.snd counters
      change (eventRecorded (serviceTimeouts setup deps duration)) leaks
          ((left.respond app actor leftResponse).logs actor) event =
        (eventRecorded (serviceTimeouts setup deps duration)) leaks
          ((right.respond app actor rightResponse).logs actor) event
      unfold EventGraphRuntime.eventRecorded
      rw [leftRecalled, rightRecalled, List.any_append, List.any_append]
      unfold EventGraphRuntime.eventRecorded at sameRecorded
      rw [sameRecorded]
      simp only [List.any_cons, List.any_nil, Bool.or_false, submitted]
  · change (ownerTurns owner event (left.respond app actor leftResponse),
        (eventRecorded (serviceTimeouts setup deps duration)) leaks
          ((left.respond app actor leftResponse).logs owner) event) =
      (ownerTurns owner event (right.respond app actor rightResponse),
        (eventRecorded (serviceTimeouts setup deps duration)) leaks
          ((right.respond app actor rightResponse).logs owner) event)
    unfold ownerTurns
    rw [app.respond_recall_other left actor owner isActor leftResponse,
      app.respond_recall_other right actor owner isActor rightResponse]
    exact counters


private theorem reference_binding_first_invoke_congr
    {horizon leftRemaining rightRemaining turns : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {bound : (serviceGraph setup deps).EventId → Nat}
    {event : (serviceGraph setup deps).EventId} {owner focal : Player} {payload : L.Ty}
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    (foreign : owner ≠ focal)
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
      ((serviceGraph setup deps).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup deps) event = .bind owner payload outputEq codeEq)
    (leftReference rightReference : (serviceGraph setup deps).BehavioralProfile)
    (leftSubmits : (serviceGraph setup deps).SubmitsBindings leftReference)
    (rightSubmits : (serviceGraph setup deps).SubmitsBindings rightReference)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (same : bindingWindowReadout (leaks := leaks) focal left =
      bindingWindowReadout (leaks := leaks) focal right)
    (leftTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (leftOwn : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks left owner)
    (leftSlots : CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks left owner)
    (rightOwn : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks right owner)
    (rightSlots : CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks right owner)
    (selected : (.activate owner : (serviceApplication setup deps duration leaks).Command) ∈
      (scheduler left.environmentRecall
        (left.observeEnvironment (serviceApplication setup deps duration leaks))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((serviceApplication setup deps duration leaks).observePending owner
      left.network.pending).support)
    (first : ownerTurns owner event left = 0) :
    let app := serviceApplication setup deps duration leaks
    let leftActive := left.sampledActivation app owner sample
    let rightActive := right.sampledActivation app owner sample
    let clients := fun reference => turnPolicy (serviceTimeouts setup deps duration) leaks bound
      turns (firstTurnTiming setup turns deps) reference
    ((clients leftReference owner (leftActive.logs owner) (leftActive.observe app owner)).map
        (leftActive.respond app owner)).map (bindingWindowReadout (leaks := leaks) focal) =
      ((clients rightReference owner (rightActive.logs owner) (rightActive.observe app owner)).map
        (rightActive.respond app owner)).map (bindingWindowReadout (leaks := leaks) focal) := by
  intro app leftActive rightActive clients
  have owned : (serviceGraph setup deps).actor? event = some owner :=
    nodeView_bind_actor outputEq codeEq
  have leftActiveOwner : owner ∉ left.application.config.defaulted :=
    left.application.active_of_ready_owned
      (legalFacts setup leaks horizon scheduler _ leftTrace).quiescent leftReady owned
  have rightActiveOwner : owner ∉ right.application.config.defaulted :=
    right.application.active_of_ready_owned
      (legalFacts setup leaks horizon scheduler _ rightTrace).quiescent rightReady owned
  have leftTurn : leftActive.application.publicView.ownTurn? owner = some event :=
    leftActive.application.ownTurn?_of_ready ownerSolitary leftReady owned
  have rightTurn : rightActive.application.publicView.ownTurn? owner = some event :=
    rightActive.application.ownTurn?_of_ready ownerSolitary rightReady owned
  have counters : (ownerTurns owner event left,
      (eventRecorded (serviceTimeouts setup deps duration)) leaks (left.logs owner) event) =
    (ownerTurns owner event right,
      (eventRecorded (serviceTimeouts setup deps duration)) leaks (right.logs owner) event) :=
    congrFun (congrFun (congrArg Prod.snd same) owner) event
  have sameTurns : ownerTurns owner event left = ownerTurns owner event right :=
    congrArg Prod.fst counters
  have rightFirst : ownerTurns owner event right = 0 := sameTurns.symm.trans first
  dsimp only [clients]
  rw [reference_first_turn_action_mixture bound turns leftReference owner event leftActive owned
    leftTurn leftActiveOwner first,
    reference_first_turn_action_mixture bound turns rightReference owner event rightActive owned
      rightTurn rightActiveOwner rightFirst]
  simp only [PMF.map_bind]
  let leftKernel : PMF ((serviceGraph setup deps).Action event) :=
    leftReference owner event owned
      ((serviceGraph setup deps).playerObserve owner left.application.config) leftActiveOwner
  let rightKernel : PMF ((serviceGraph setup deps).Action event) :=
    rightReference owner event owned
      ((serviceGraph setup deps).playerObserve owner right.application.config) rightActiveOwner
  apply bind_eq_of_map_eq leftKernel rightKernel (fun _ => ()) (fun _ => ())
    ((PMF.map_const leftKernel ()).trans (PMF.map_const rightKernel ()).symm) _ _
  intro leftAction leftSupported rightAction rightSupported _
  let leftChoice : Option (PublicationResult (L.Val payload)) :=
    cast (congrArg EventField.Action outputEq) leftAction
  let rightChoice : Option (PublicationResult (L.Val payload)) :=
    cast (congrArg EventField.Action outputEq) rightAction
  have leftSubmitted : leftChoice.isSome := EventField.submitted_cast outputEq leftAction
    (leftSubmits owner event owned
      ((serviceGraph setup deps).playerObserve owner left.application.config)
        leftActiveOwner leftAction leftSupported)
  have rightSubmitted : rightChoice.isSome := EventField.submitted_cast outputEq rightAction
    (rightSubmits owner event owned
      ((serviceGraph setup deps).playerObserve owner right.application.config)
        rightActiveOwner rightAction rightSupported)
  have focalReadout : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right := by
    have traffic : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal left =
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal right :=
      congrArg Prod.fst same
    exact Prod.ext traffic counters
  obtain ⟨leftResponse, rightResponse, leftPure, rightPure, submitted, traffic⟩ :=
    binding_response_matched (bound := bound) ownerSolitary foreign outputEq codeEq node
      leftChoice rightChoice (leftSubmitted.trans rightSubmitted.symm) focalReadout leftTrace
      rightTrace leftReady rightReady leftOwn leftSlots rightOwn rightSlots selected sample sampled
  simp only [leftChoice, rightChoice, cast_cast, cast_eq] at leftPure rightPure
  rw [leftPure, rightPure, PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map]
  exact congrArg PMF.pure (bindingWindowReadout_response focal owner
    (bindingWindowReadout_activation focal owner same sample) leftResponse rightResponse submitted
      traffic)




private theorem bindingWindowReadout_environment_readyBinding
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    (focal : Player) {event : (serviceGraph setup deps).EventId}
    {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (same : bindingWindowReadout (leaks := leaks) focal left =
      bindingWindowReadout (leaks := leaks) focal right)
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (command : (serviceApplication setup deps duration leaks).Command)
    (inactive : command.actor? (serviceApplication setup deps duration leaks) = none) :
    (left.environmentStep (serviceApplication setup deps duration leaks) command).map
        (bindingWindowReadout (leaks := leaks) focal) =
      (right.environmentStep (serviceApplication setup deps duration leaks) command).map
        (bindingWindowReadout (leaks := leaks) focal) := by
  let app := serviceApplication setup deps duration leaks
  obtain ⟨first, firstPure⟩ := environmentStep_pure_of_readyBinding relaxed outputEq left
    leftReady command inactive
  obtain ⟨second, secondPure⟩ := environmentStep_pure_of_readyBinding relaxed outputEq right
    rightReady command inactive
  have focalLaw : (left.environmentStep app command).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) =
      (right.environmentStep app command).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) := by
    cases command with
    | activate actor => cases inactive
    | «include» id =>
        have included : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
            (left.includePending app id) =
          (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
            (right.includePending app id) := by
          apply include_bindingTraffic_of_handled (congrArg Prod.fst same) id
          intro message _
          exact binding_ready_handler_congr relaxed outputEq left.application
            right.application focal
            (congrArg (fun value => value.2.2.2.2.1) (congrArg Prod.fst same)) leftReady
              ⟨message.id, message.payload.call⟩
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        apply congrArg PMF.pure
        have recalled : left.environmentRecall = right.environmentRecall :=
          congrArg (fun value => value.2.2.1) (congrArg Prod.fst same)
        rw [recalled, observeEnvironment_eq_of_bindingTraffic focal (congrArg Prod.fst same)]
        exact bindingTraffic_with_environmentRecall focal included _
    | application op =>
        exact application_environmentStep_traffic_congr (leaks := leaks)
          (congrArg Prod.fst same) op
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        exact congrArg PMF.pure (bindingTraffic_record (leaks := leaks) focal
          (congrArg Prod.fst same) .wait)
  have firstLogs := app.environmentStep_recall left first command
    (show first ∈ (left.environmentStep app command).support by rw [firstPure]; simp)
  have secondLogs := app.environmentStep_recall right second command
    (show second ∈ (right.environmentStep app command).support by rw [secondPure]; simp)
  rw [firstPure, secondPure, PMF.pure_map, PMF.pure_map] at focalLaw ⊢
  apply congrArg PMF.pure
  have traffic : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal first =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal second := by
    have member : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal first ∈
        (PMF.pure ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
          second)).support := focalLaw ▸ (by simp)
    simpa using member
  refine Prod.ext traffic ?_
  funext actor named
  change (ownerTurns actor named first,
      (eventRecorded (serviceTimeouts setup deps duration)) leaks (first.logs actor) named) =
    (ownerTurns actor named second,
      (eventRecorded (serviceTimeouts setup deps duration)) leaks (second.logs actor) named)
  unfold ownerTurns
  rw [firstLogs, secondLogs]
  exact congrFun (congrFun (congrArg Prod.snd same) actor) named

private theorem bindingWindowReadout_invoke_focal (focal : Player)
    (policy : (serviceApplication setup deps duration leaks).Policy)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (same : bindingWindowReadout (leaks := leaks) focal left =
      bindingWindowReadout (leaks := leaks) focal right) :
    ((policy (left.logs focal)
        (left.observe (serviceApplication setup deps duration leaks) focal)).map
      (left.respond (serviceApplication setup deps duration leaks) focal)).map
        (bindingWindowReadout (leaks := leaks) focal) =
    ((policy (right.logs focal)
        (right.observe (serviceApplication setup deps duration leaks) focal)).map
      (right.respond (serviceApplication setup deps duration leaks) focal)).map
        (bindingWindowReadout (leaks := leaks) focal) := by
  have traffic := congrArg Prod.fst same
  have recalled : left.logs focal = right.logs focal :=
    congrArg (fun value => value.2.2.2.1) traffic
  rw [recalled, observe_eq_of_bindingTraffic focal traffic, PMF.map_comp, PMF.map_comp]
  apply map_congr_on_support _
  intro response _
  exact bindingWindowReadout_response focal focal same response response rfl
    (bindingTraffic_owner_response _ leaks left right focal traffic response)

private theorem bindingWindowReadout_silent (focal actor : Player)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (same : bindingWindowReadout (leaks := leaks) focal left =
      bindingWindowReadout (leaks := leaks) focal right) :
    bindingWindowReadout (leaks := leaks) focal
        (left.respond (serviceApplication setup deps duration leaks) actor ⟨none⟩) =
      bindingWindowReadout (leaks := leaks) focal
        (right.respond (serviceApplication setup deps duration leaks) actor ⟨none⟩) :=
  bindingWindowReadout_response focal actor same ⟨none⟩ ⟨none⟩ rfl
    (bindingTraffic_silent _ leaks left right focal actor (congrArg Prod.fst same) ⟨none⟩ rfl)


theorem reference_client_no_turn
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile) (who : Player)
    (past : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (view : (serviceApplication setup deps duration leaks).PlayerView)
    (serving : view.application.publicView.ownTurn? who = none) :
    turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference who past view = PMF.pure ⟨none⟩ := by
  simp only [EventGraphRuntime.turnPolicy, serving, ReactiveApplication.silentPolicy_apply]
theorem ready_not_public_of_binding_ready
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {event named : (serviceGraph setup deps).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (cut : (serviceGraph setup deps).order.Cut)
    (ready : cut.Ready event) (namedReady : cut.Ready named) :
    ¬ ((serviceGraph setup deps).outputLayout named).IsPublic := by
  by_cases same : event = named
  · subst named
    rw [outputEq]
    simp [EventField.IsPublic]
  · intro isPublic
    have both := relaxed.ready_public_pair_publications cut ready namedReady same (Or.inr isPublic)
    rw [outputEq] at both
    simp [EventField.IsPublication] at both

/-- A private-binding window cannot convey the honest players' binding values through traffic. -/
private theorem bindingWindow_round_readout
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {horizon leftRemaining rightRemaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {event : (serviceGraph setup deps).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (leftReference rightReference : (serviceGraph setup deps).BehavioralProfile)
    (leftSubmits : (serviceGraph setup deps).SubmitsBindings leftReference)
    (rightSubmits : (serviceGraph setup deps).SubmitsBindings rightReference)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (same : bindingWindowReadout (leaks := leaks) focal left =
      bindingWindowReadout (leaks := leaks) focal right)
    (leftTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (leftCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn
        (serviceTimeouts setup deps duration) leaks left actor ∧
          CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks left actor)
    (rightCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn
        (serviceTimeouts setup deps duration) leaks right actor ∧
          CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks right actor) :
    let app := serviceApplication setup deps duration leaks
    let players := fun reference => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) focal deviation
    (app.round scheduler (players leftReference) left).map
        (bindingWindowReadout (leaks := leaks) focal) =
      (app.round scheduler (players rightReference) right).map
        (bindingWindowReadout (leaks := leaks) focal) := by
  intro app players
  have traffic := congrArg Prod.fst same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) traffic
  have observed := observeEnvironment_eq_of_bindingTraffic focal traffic
  have networks : left.network = right.network := congrArg Prod.fst traffic
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) traffic
  apply app.round_map_congr scheduler (players leftReference) (players rightReference) left right
    (bindingWindowReadout (leaks := leaks) focal) environments observed networks
  · intro actor selected sample sampled
    let leftActive := left.sampledActivation app actor sample
    let rightActive := right.sampledActivation app actor sample
    have activated := bindingWindowReadout_activation focal actor same sample
    by_cases isFocal : actor = focal
    · subst actor
      simp only [players, Function.update_self]
      exact bindingWindowReadout_invoke_focal focal deviation activated
    · simp only [players, Function.update_of_ne isFocal]
      have activePublics : leftActive.application.publicView =
          rightActive.application.publicView := publics
      cases serving : left.application.publicView.ownTurn? actor with
      | none =>
          have leftServing : (leftActive.observe app actor).application.publicView.ownTurn?
              actor = none := serving
          have rightServing : (rightActive.observe app actor).application.publicView.ownTurn?
              actor = none := by
            change rightActive.application.publicView.ownTurn? actor = none
            rw [← activePublics]
            exact serving
          rw [reference_client_no_turn bound turns leftReference actor _ _ leftServing,
            reference_client_no_turn bound turns rightReference actor _ _ rightServing]
          simp only [PMF.pure_map]
          exact congrArg PMF.pure (bindingWindowReadout_silent focal actor activated)
      | some named =>
          have facts := left.application.publicView.ownTurn?_spec actor named serving
          have namedReady : left.application.config.cut.Ready named :=
            (left.application.publicView_eventReady named).mp facts.1
          have owned : (serviceGraph setup deps).actor? named = some actor := facts.2
          have rightNamedReady : right.application.config.cut.Ready named := by
            rw [← cut_eq_of_publicView_eq publics]
            exact namedReady
          have notPublic := ready_not_public_of_binding_ready relaxed outputEq
            left.application.config.cut leftReady namedReady
          have leftServing : leftActive.application.publicView.ownTurn? actor = some named :=
            serving
          have rightServing : rightActive.application.publicView.ownTurn? actor = some named :=
            (congrArg (fun view => view.ownTurn? actor) activePublics).symm.trans leftServing
          cases namedNode : nodeView (serviceGraph setup deps) named with
          | sample ty law namedOutput namedCode =>
              exact (notPublic (by rw [namedOutput]; trivial)).elim
          | resolve who ty binding checks namedOutput namedCode =>
              exact (notPublic (by rw [namedOutput]; trivial)).elim
          | bind who ty namedOutput namedCode =>
              have whoEq : who = actor :=
                Option.some.inj ((nodeView_bind_actor namedOutput namedCode).symm.trans owned)
              subst who
              by_cases first : ownerTurns actor named left = 0
              · exact reference_binding_first_invoke_congr (turns := turns) (bound := bound)
                  (relaxed.actorSerial named) isFocal namedOutput namedCode namedNode
                  leftReference rightReference leftSubmits rightSubmits same leftTrace rightTrace
                  namedReady rightNamedReady (leftCanonical actor isFocal).1
                  (leftCanonical actor isFocal).2 (rightCanonical actor isFocal).1
                  (rightCanonical actor isFocal).2 (by
                    rw [environments, observed]
                    exact selected) sample (by rw [networks]; exact sampled) first
              · have counters := congrFun (congrFun (congrArg Prod.snd same) actor) named
                have sameTurns : ownerTurns actor named left = ownerTurns actor named right :=
                  congrArg Prod.fst counters
                have rightNotFirst : ownerTurns actor named right ≠ 0 := by
                  rw [← sameTurns]
                  exact first
                have leftLater : turnIndex (serviceTimeouts setup deps duration) leaks actor named
                    (leftActive.logs actor) (leftActive.observe app actor) ≠ some 0 := by
                  rw [serviceTurn_of_turn leftActive leftServing]
                  exact fun equal => first (Option.some.inj equal)
                have rightLater : turnIndex (serviceTimeouts setup deps duration) leaks actor named
                    (rightActive.logs actor) (rightActive.observe app actor) ≠ some 0 := by
                  rw [serviceTurn_of_turn rightActive rightServing]
                  exact fun equal => rightNotFirst (Option.some.inj equal)
                rw [sourceServiceTurnPolicy_laterTurn_reference owned leftServing leftLater,
                  sourceServiceTurnPolicy_laterTurn_reference owned rightServing rightLater]
                simp only [PMF.pure_map]
                exact congrArg PMF.pure (bindingWindowReadout_silent focal actor activated)
  · intro command _ inactive
    exact bindingWindowReadout_environment_readyBinding relaxed focal outputEq same
      leftReady rightReady command inactive


/-- Joint focal traffic through binding completion ignores the honest hidden values. -/
private theorem bindingWindow_stopped_readout
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {horizon count leftRemaining rightRemaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {event : (serviceGraph setup deps).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (leftReference rightReference : (serviceGraph setup deps).BehavioralProfile)
    (leftSubmits : (serviceGraph setup deps).SubmitsBindings leftReference)
    (rightSubmits : (serviceGraph setup deps).SubmitsBindings rightReference)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (leftStart rightStart : (serviceApplication setup deps duration leaks).Execution)
    (same : bindingWindowReadout (leaks := leaks) focal leftStart =
      bindingWindowReadout (leaks := leaks) focal rightStart)
    (leftTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (leftCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks leftStart actor ∧
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks leftStart actor)
    (rightCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks rightStart actor ∧
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks rightStart actor) :
    let app := serviceApplication setup deps duration leaks
    let players := fun reference => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) focal deviation
    (app.runUntil scheduler (players leftReference)
        (fun final => event ∈ final.application.config.cut.completed) count leftStart).map
        (bindingWindowReadout (leaks := leaks) focal) =
      (app.runUntil scheduler (players rightReference)
        (fun final => event ∈ final.application.config.cut.completed) count rightStart).map
        (bindingWindowReadout (leaks := leaks) focal) := by
  intro app players
  let invariant := fun (n : Nat) (current : app.Execution) =>
    (∃ remaining, Nonempty ((app.protocol (serviceInitialDistribution setup deps) horizon
      scheduler).Trace
      (some ⟨remaining + n, none, current⟩))) ∧
    (event ∉ current.application.config.cut.completed →
      current.application.config.cut.Ready event) ∧
    ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn
        (serviceTimeouts setup deps duration) leaks current actor ∧
          CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks current actor
  have advance (reference : (serviceGraph setup deps).BehavioralProfile) (n : Nat)
      (current : app.Execution) (valid : invariant (n + 1) current)
      (running : event ∉ current.application.config.cut.completed)
      (next : app.Execution)
      (reached : next ∈ (app.round scheduler (players reference) current).support) :
      invariant n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, pendingReady, canonical⟩ := valid
    have before : (app.protocol (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := app.raw_trace_round (serviceInitialDistribution setup deps) horizon
      scheduler
      (players reference) (remaining + n) current next before reached
    refine ⟨⟨remaining, ⟨nextTrace⟩⟩,
      fun unfinished => round_ready_of_unfinished scheduler (players reference)
        (pendingReady running) unfinished reached, ?_⟩
    intro actor foreign
    obtain ⟨own, slots⟩ := canonical actor foreign
    exact canonicalSlots_round relaxed.actorSerial (by
      simpa only [players, Function.update_of_ne foreign] using
        (turnPolicy_submitsCanonically (serviceTimeouts setup deps duration) leaks bound turns
          (firstTurnTiming setup turns deps) reference actor)) (by
      simpa only [players, Function.update_of_ne foreign] using
        (sourceServiceTurnPolicy_submitsAtTurn_reference setup leaks bound turns
          (firstTurnTiming setup turns deps) reference actor)) before own slots reached
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler (players leftReference)
    (players rightReference) (fun final => event ∈ final.application.config.cut.completed)
    (bindingWindowReadout (leaks := leaks) focal) invariant invariant
  · intro n left right _leftValid _rightValid equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) (congrArg Prod.fst equal)
    rw [cut_eq_of_publicView_eq publics]
  · intro n left right leftValid rightValid equal running
    obtain ⟨⟨leftRest, ⟨leftCurrentTrace⟩⟩, currentLeftReady, currentLeftCanonical⟩ := leftValid
    obtain ⟨⟨rightRest, ⟨rightCurrentTrace⟩⟩, currentRightReady, currentRightCanonical⟩ :=
      rightValid
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) (congrArg Prod.fst equal)
    have rightRunning : event ∉ right.application.config.cut.completed := by
      rw [← cut_eq_of_publicView_eq publics]
      exact running
    have leftBefore : (app.protocol (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨(leftRest + n) + 1, none, left⟩) := by
      simpa only [Nat.add_assoc] using leftCurrentTrace
    have rightBefore : (app.protocol (serviceInitialDistribution setup deps) horizon
      scheduler).Trace
        (some ⟨(rightRest + n) + 1, none, right⟩) := by
      simpa only [Nat.add_assoc] using rightCurrentTrace
    exact bindingWindow_round_readout relaxed scheduler bound outputEq leftReference
      rightReference leftSubmits rightSubmits focal deviation equal leftBefore rightBefore
      (currentLeftReady running) (currentRightReady rightRunning) currentLeftCanonical
      currentRightCanonical
  · exact advance leftReference
  · exact advance rightReference
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, fun _ => leftReady, leftCanonical⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, fun _ => rightReady, rightCanonical⟩
  · exact same

end Vegas

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem submittedEvent_eq_recalled_emission
    (initial : PMF ((reactiveApplication timeouts) leaks).State) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    {control : ((reactiveApplication timeouts) leaks).Control}
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control)) (owner : Player)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry)
    (member : entry ∈ control.execution.logs owner) :
    (submittedEvent? timeouts) leaks entry.action =
      entry.emitted.bind (fun message => message.payload.call.event? graph) := by
  let app := (reactiveApplication timeouts) leaks
  let property := fun execution : app.Execution => ∀ who, ∀ found ∈ execution.logs who,
    (submittedEvent? timeouts) leaks found.action =
      found.emitted.bind (fun message => message.payload.call.event? graph)
  have invariant : app.ServiceInvariant scheduler property := {
    respond := by
      intro execution actor action valid observer found recorded
      rw [respond_recall] at recorded
      split at recorded
      · rename_i same
        subst observer
        rcases List.mem_append.mp recorded with old | new
        · exact valid actor found old
        · obtain rfl := List.mem_singleton.mp new
          rcases action with ⟨_ | material⟩ <;> rfl
      · exact valid observer found recorded
    environment := by
      intro execution next command valid _ moved observer found recorded
      rw [app.environmentStep_recall execution next command moved] at recorded
      exact valid observer found recorded }
  exact invariant.history initial horizon (by intro state _ observer found recorded; cases recorded)
    trace owner entry member

private theorem eventRecorded_eq_inputs
    (initial : PMF ((reactiveApplication timeouts) leaks).State) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    {control : ((reactiveApplication timeouts) leaks).Control}
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control)) (owner : Player) (event : graph.EventId) :
    (eventRecorded timeouts) leaks (control.execution.logs owner) event =
      (control.execution.network.inputs.filter (fun message => message.sender = owner)).any
        (fun message => decide (message.payload.call.event? graph = some event)) := by
  classical
  let app := (reactiveApplication timeouts) leaks
  have recalled := app.history_inputRecall initial horizon scheduler trace
  change control.execution.InputRecall app at recalled
  rw [recalled owner]
  apply Bool.eq_iff_iff.mpr
  simp only [eventRecorded, List.any_eq_true, decide_eq_true_eq, ReactiveApplication.outputs,
    List.mem_filterMap]
  constructor
  · rintro ⟨entry, member, submitted⟩
    have emitted := (submittedEvent_eq_recalled_emission timeouts leaks initial horizon scheduler
      trace owner entry member).symm.trans submitted
    obtain ⟨message, present, named⟩ := Option.bind_eq_some_iff.mp emitted
    exact ⟨message, ⟨entry, member, present⟩, named⟩
  · rintro ⟨message, ⟨entry, member, present⟩, named⟩
    refine ⟨entry, member, ?_⟩
    rw [submittedEvent_eq_recalled_emission timeouts leaks initial horizon scheduler trace
      owner entry member, present, Option.bind_some]
    exact named

end Vegas.EventGraphRuntime

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

private theorem public_response_count_eq_activations
    (localPublic : app.LocalObservation → app.PublicObservation)
    (agrees : ∀ state who, localPublic (app.observePlayer state who) = app.observePublic state)
    (test : app.PublicObservation → Bool) (owner : Principal)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {control : app.Control}
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (boundary : control.actor = none) :
    (control.execution.logs owner).countP
        (fun entry => test (localPublic entry.beforeView.application)) =
      control.execution.environmentRecall.countP (fun entry => match entry.command with
        | .activate actor => if actor = owner then test entry.beforeView.application else false
        | _ => false) := by
  let responses := fun execution : app.Execution => (execution.logs owner).countP
    (fun entry => test (localPublic entry.beforeView.application))
  let activations := fun execution : app.Execution => execution.environmentRecall.countP
    (fun entry => match entry.command with
      | .activate actor => if actor = owner then test entry.beforeView.application else false
      | _ => false)
  let pending := fun current : app.Control => if current.actor = some owner then
    if test (app.observePublic current.execution.application) then 1 else 0 else 0
  let property := fun state : app.ProtocolState => state.elim True
    (fun current => responses current.execution + pending current = activations current.execution)
  have responseCount (execution : app.Execution) (actor : Principal) (response : app.Action) :
      responses (execution.respond app actor response) = responses execution +
        if actor = owner then (if test (app.observePublic execution.application) then 1 else 0)
          else 0 := by
    by_cases same : actor = owner
    · subst actor
      rcases response with ⟨_ | material⟩ <;>
        simp only [responses, Execution.respond, ite_true, List.countP_append,
          List.countP_singleton, agrees, Execution.observe]
    · have other : owner ≠ actor := Ne.symm same
      simp only [responses, app.respond_recall_other execution actor owner other response,
        same, ite_false, Nat.add_zero]
  have accounting : ∀ {state} (_history : (app.protocol initial horizon scheduler).Trace state),
      property state := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈ (app.transition initial horizon scheduler source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
            simp only [property, Option.elim_some, responses, activations, pending,
              Execution.initial, List.countP_nil, reduceCtorEq, ite_false, Nat.add_zero]
        | some current =>
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some actor =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                change responses (execution.respond app actor ((joint actor).getD ⟨none⟩)) + _ = _
                rw [responseCount]
                simpa only [property, Option.elim_some, pending, app.respond_environmentRecall,
                  activations, Option.some.injEq, reduceCtorEq, ite_false, Nat.add_zero] using ih
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    have counted : responses execution = activations execution := by
                      simpa only [property, Option.elim_some, pending, reduceCtorEq, ite_false,
                        Nat.add_zero] using ih
                    change responses next + pending ⟨remaining, command.actor? app, next⟩ =
                      activations next
                    apply app.environmentStep_cases execution next command supported
                    · simpa only [responses, activations, pending, Command.actor?, reduceCtorEq,
                        ite_false, Nat.add_zero, List.countP_append, List.countP_singleton,
                        Bool.false_eq_true] using counted
                    · intro actor sample _
                      by_cases same : actor = owner
                      · simpa only [responses, activations, pending, Command.actor?,
                          Option.some.injEq, same, ite_true, List.countP_append,
                          List.countP_singleton, Execution.observeEnvironment] using congrArg
                            (fun value => value +
                              if test (app.observePublic execution.application) then 1 else 0)
                            counted
                      · simpa only [responses, activations, pending, Command.actor?,
                          Option.some.injEq, same, ite_false, List.countP_append,
                          List.countP_singleton, Bool.false_eq_true, Nat.add_zero] using counted
                    · intro id
                      have kept : (execution.includePending app id).logs = execution.logs := by
                        cases found : (execution.network.includePending id).1 <;>
                          simp only [Execution.includePending, found]
                      simpa only [responses, activations, pending, Command.actor?, reduceCtorEq,
                        ite_false, Nat.add_zero, List.countP_append, List.countP_singleton,
                        Bool.false_eq_true, kept] using counted
                    · intro command native _
                      simpa only [responses, activations, pending, Command.actor?, reduceCtorEq,
                        ite_false, Nat.add_zero, List.countP_append, List.countP_singleton,
                        Bool.false_eq_true] using counted
  change responses control.execution = activations control.execution
  have final : responses control.execution + pending control = activations control.execution :=
    accounting trace
  have pendingZero : pending control = 0 := by
    simp only [pending, boundary, reduceCtorEq, ite_false]
  simpa only [pendingZero, Nat.add_zero] using final

end Interaction.ReactiveApplication



namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

private theorem bindingWindowReadout_congr_of_traffic
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    (focal : Player)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (leftTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨leftRemaining, none, left⟩))
    (rightTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨rightRemaining, none, right⟩))
    (same : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal left =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal right) :
    bindingWindowReadout (leaks := leaks) focal left =
      bindingWindowReadout (leaks := leaks) focal right := by
  let app := serviceApplication setup deps duration leaks
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have networks : left.network = right.network := congrArg Prod.fst same
  refine Prod.ext same ?_
  funext owner event
  apply Prod.ext
  · change ownerTurns owner event left = ownerTurns owner event right
    let query : app.PublicObservation → Bool := fun view =>
      decide (PublicView.ownTurn? (graph := serviceGraph setup deps) view owner = some event)
    have leftTurns : ownerTurns owner event left = _ :=
      app.public_response_count_eq_activations
        (fun view : EventGraphRuntime.PlayerView (serviceGraph setup deps) => view.publicView)
        (by intro state who; rfl) query owner
        (serviceInitialDistribution setup deps) horizon scheduler leftTrace rfl
    have rightTurns : ownerTurns owner event right = _ :=
      app.public_response_count_eq_activations
        (fun view : EventGraphRuntime.PlayerView (serviceGraph setup deps) => view.publicView)
        (by intro state who; rfl) query owner
        (serviceInitialDistribution setup deps) horizon scheduler rightTrace rfl
    rw [leftTurns, rightTurns, environments]
  · change (eventRecorded (serviceTimeouts setup deps duration)) leaks (left.logs owner) event =
      (eventRecorded (serviceTimeouts setup deps duration)) leaks (right.logs owner) event
    rw [eventRecorded_eq_inputs (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler leftTrace owner event,
      eventRecorded_eq_inputs (serviceTimeouts setup deps duration) leaks
        (serviceInitialDistribution setup deps) horizon scheduler rightTrace owner event, networks]

end Vegas




namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

theorem bindingWindow_round_opacity
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {horizon leftRemaining rightRemaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {event : (serviceGraph setup deps).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (leftReference rightReference : (serviceGraph setup deps).BehavioralProfile)
    (leftSubmits : (serviceGraph setup deps).SubmitsBindings leftReference)
    (rightSubmits : (serviceGraph setup deps).SubmitsBindings rightReference)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (same : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal left =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal right)
    (leftTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (leftCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn
        (serviceTimeouts setup deps duration) leaks left actor ∧
          CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks left actor)
    (rightCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn
        (serviceTimeouts setup deps duration) leaks right actor ∧
          CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks right actor) :
    let app := serviceApplication setup deps duration leaks
    let players := fun reference => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) focal deviation
    (app.round scheduler (players leftReference) left).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) =
      (app.round scheduler (players rightReference) right).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) := by
  intro app players
  have recovered := bindingWindowReadout_congr_of_traffic focal leftTrace rightTrace same
  have law := bindingWindow_round_readout (turns := turns) relaxed scheduler bound outputEq
    leftReference rightReference leftSubmits rightSubmits focal deviation recovered leftTrace
    rightTrace leftReady rightReady leftCanonical rightCanonical
  have projected := congrArg (PMF.map Prod.fst) law
  simpa only [PMF.map_comp, Function.comp_def, bindingWindowReadout] using projected

theorem bindingWindow_stopped_opacity
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {horizon count leftRemaining rightRemaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {event : (serviceGraph setup deps).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (leftReference rightReference : (serviceGraph setup deps).BehavioralProfile)
    (leftSubmits : (serviceGraph setup deps).SubmitsBindings leftReference)
    (rightSubmits : (serviceGraph setup deps).SubmitsBindings rightReference)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (leftStart rightStart : (serviceApplication setup deps duration leaks).Execution)
    (same : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal leftStart =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal rightStart)
    (leftTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (leftCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks leftStart actor ∧
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks leftStart actor)
    (rightCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks rightStart actor ∧
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks rightStart actor) :
    let app := serviceApplication setup deps duration leaks
    let players := fun reference => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) focal deviation
    (app.runUntil scheduler (players leftReference)
        (fun final => event ∈ final.application.config.cut.completed) count leftStart).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) =
      (app.runUntil scheduler (players rightReference)
        (fun final => event ∈ final.application.config.cut.completed) count rightStart).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) := by
  intro app players
  have recovered := bindingWindowReadout_congr_of_traffic focal leftTrace rightTrace same
  have law := bindingWindow_stopped_readout (count := count) (turns := turns) relaxed scheduler
    bound outputEq leftReference rightReference leftSubmits rightSubmits focal deviation leftStart
    rightStart recovered leftTrace rightTrace leftReady rightReady leftCanonical rightCanonical
  have projected := congrArg (PMF.map Prod.fst) law
  simpa only [PMF.map_comp, Function.comp_def, bindingWindowReadout] using projected

end Vegas
