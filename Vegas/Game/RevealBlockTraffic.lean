/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ReferenceForeignTraffic
import Vegas.Pending.CanonicalKeyPublication
import Vegas.Pending.EffectiveOpening

/-! # Deviator traffic across a block of concurrent reveals

In a block of concurrently ready reveals, several honest owners open while the
deviator acts. The deviator's view after including any packet depends only on
its view before and on the stored bindings of the ready reveals: an opening is
accepted only for a stored successful binding, and then it reveals exactly the
stored value.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Handle

variable {graph : Vegas.EventGraph Player L}

/-- An opening of a reveal whose binding stores no successful value is rejected. -/
theorem handle_opening_eq_none_of_not_success (runtime : EventGraphRuntime graph)
    (state : EventGraphRuntime.State graph) (id : MessageId Player) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks}
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (failed : ∀ value, binding.get? state.config.store ≠ some (.success value)) :
    handle runtime state ⟨id, .opening event candidate raw⟩ = none := by
  simp only [handle, node, failed, dite_false]
  split_ifs <;> first | rfl | (split <;> rfl)

/-- An opening of a reveal that is not ready is rejected. -/
theorem handle_opening_eq_none_of_not_ready (runtime : EventGraphRuntime graph)
    (state : EventGraphRuntime.State graph) (id : MessageId Player) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (pending : ¬ state.config.cut.Ready event) :
    handle runtime state ⟨id, .opening event candidate raw⟩ = none := by
  simp [handle, pending]

end Handle

variable {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}

/-- **Inclusion in a block.** Two states with equal deviator views and equal
stored bindings at every ready reveal give the deviator equal views after
handling any packet. -/
theorem block_handle_playerView_congr
    (left right : EventGraphRuntime.State (serviceGraph setup mode)) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (leftInvariant : left.BindingInvariant) (rightInvariant : right.BindingInvariant)
    (bindings : ∀ (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      left.config.cut.Ready event →
        binding.get? left.config.store = binding.get? right.config.store)
    (message : Message Player (Payload (serviceGraph setup mode))) :
    (handle (serviceRuntime setup mode deadline) left message).map
        (fun state => state.playerView focal) =
      (handle (serviceRuntime setup mode deadline) right message).map
        (fun state => state.playerView focal) := by
  classical
  obtain ⟨id, packet⟩ := message
  have cuts := cut_eq_of_publicView_eq (congrArg PlayerView.publicView views)
  cases packet with
  | malformed raw => simp [handle]
  | commitment named candidate =>
      exact handle_commitment_playerView_congr _ left right focal id named candidate views
  | opening named candidate raw =>
      by_cases namedReady : left.config.cut.Ready named
      · have rightReady : right.config.cut.Ready named := by rw [← cuts]; exact namedReady
        cases node : nodeView (serviceGraph setup mode) named with
        | resolve owner payload binding checks outputEq codeEq =>
            have same := bindings named owner payload binding checks outputEq codeEq node
              namedReady
            by_cases successful : ∃ value, binding.get? left.config.store = some (.success value)
            · obtain ⟨value, leftStored⟩ := successful
              exact handle_opening_playerView_congr node left right focal views namedReady
                rightReady leftInvariant rightInvariant value leftStored (same ▸ leftStored) id
                candidate raw
            · push Not at successful
              rw [handle_opening_eq_none_of_not_success _ left id named candidate raw node
                  successful,
                handle_opening_eq_none_of_not_success _ right id named candidate raw node
                  (fun value stored => successful value (same.trans stored))]
        | bind owner payload outputEq codeEq => simp [handle, node]
        | sample payload law outputEq codeEq => simp [handle, node]
      · have rightNot : ¬ right.config.cut.Ready named := by rw [← cuts]; exact namedReady
        rw [handle_opening_eq_none_of_not_ready _ left id named candidate raw namedReady,
          handle_opening_eq_none_of_not_ready _ right id named candidate raw rightNot]

variable {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Every owner's turns at every event and whether it has submitted for it. -/
def blockCounters (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Player → (serviceGraph setup mode).EventId → Nat × Bool :=
  fun owner event => (ownerTurns owner event execution,
    (serviceRuntime setup mode deadline).eventRecorded leaks (execution.logs owner) event)

/-- The readout compared across a block: the deviator's traffic and every
owner's counters. -/
def blockReadout (who : Player)
    (execution : (serviceApplication setup mode deadline leaks).Execution) :=
  ((serviceRuntime setup mode deadline).bindingTraffic leaks who execution,
    blockCounters execution)

/-- Responding alike from executions with equal counters, with equal public
views of the responder and equal submitted events, keeps the counters equal. -/
theorem blockCounters_respond_congr
    {left right : (serviceApplication setup mode deadline leaks).Execution} (actor : Player)
    (leftResponse rightResponse : (serviceApplication setup mode deadline leaks).Action)
    (same : blockCounters left = blockCounters right)
    (publics : (left.observe (serviceApplication setup mode deadline leaks)
        actor).application.publicView =
      (right.observe (serviceApplication setup mode deadline leaks) actor).application.publicView)
    (submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks leftResponse =
      (serviceRuntime setup mode deadline).submittedEvent? leaks rightResponse) :
    blockCounters (left.respond (serviceApplication setup mode deadline leaks) actor
        leftResponse) =
      blockCounters (right.respond (serviceApplication setup mode deadline leaks) actor
        rightResponse) := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨_, leftRecalled, _⟩ := respond_recall_self setup leaks left actor leftResponse
  obtain ⟨_, rightRecalled, _⟩ := respond_recall_self setup leaks right actor rightResponse
  funext owner event
  have base := congrFun (congrFun same owner) event
  by_cases owned : owner = actor
  · subst owner
    simp only [blockCounters, ownerTurns, EventGraphRuntime.eventRecorded, Prod.mk.injEq]
      at base ⊢
    rw [leftRecalled, rightRecalled, List.countP_append, List.countP_append, List.any_append,
      List.any_append, base.1, base.2]
    simp only [List.countP_singleton, List.any_cons, List.any_nil, publics, submitted]
    exact ⟨trivial, trivial⟩
  · simp only [blockCounters, ownerTurns] at base ⊢
    rw [app.respond_recall_other left actor owner owned leftResponse,
      app.respond_recall_other right actor owner owned
        rightResponse]
    exact base

/-- The counters are read from the logs. -/
theorem blockCounters_of_logs
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : left.logs = right.logs) : blockCounters left = blockCounters right := by
  unfold blockCounters ownerTurns
  rw [same]

/-- A law on which every player's recall stays that of `execution` has the
compared readout of its traffic. -/
theorem map_blockReadout_of_recall (who : Player)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (law : PMF (serviceApplication setup mode deadline leaks).Execution)
    (kept : ∀ next ∈ law.support, next.logs = execution.logs) :
    law.map (blockReadout (leaks := leaks) who) =
      (law.map ((serviceRuntime setup mode deadline).bindingTraffic leaks who)).map fun traffic =>
        (traffic, blockCounters execution) := by
  rw [PMF.map_comp]
  apply map_congr_on_support _
  intro next member
  simp only [Function.comp_apply, blockReadout, blockCounters_of_logs (kept next member)]

/-- **One round of a block.** From executions with equal deviator traffic and
counters, if every other player's response at every activation is a point mass
leaving equal deviator traffic and submitting alike, and every packet is
handled alike for the deviator, one round gives equal laws of the compared
readout. -/
theorem blockRound_readout_congr
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (who : Player) (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : blockReadout who left = blockReadout who right)
    (matched : ∀ actor, actor ≠ who →
      (.activate actor : (serviceApplication setup mode deadline leaks).Command) ∈
        (scheduler left.environmentRecall
          (left.observeEnvironment (serviceApplication setup mode deadline leaks))).support →
      ∀ sample ∈ ((serviceApplication setup mode deadline leaks).observePending
          actor left.network.pending).support,
      let leftActive := left.sampledActivation
          (serviceApplication setup mode deadline leaks) actor sample
      let rightActive := right.sampledActivation
          (serviceApplication setup mode deadline leaks) actor sample
      ∃ leftResponse rightResponse,
        players actor (leftActive.logs actor)
            (leftActive.observe
                (serviceApplication setup mode deadline leaks) actor) = PMF.pure leftResponse ∧
        players actor (rightActive.logs actor)
            (rightActive.observe
                (serviceApplication setup mode deadline leaks) actor) = PMF.pure rightResponse ∧
        (serviceRuntime setup mode deadline).submittedEvent? leaks leftResponse =
          (serviceRuntime setup mode deadline).submittedEvent? leaks rightResponse ∧
        (serviceRuntime setup mode deadline).bindingTraffic leaks who
            (leftActive.respond (serviceApplication setup mode deadline leaks) actor
              leftResponse) =
          (serviceRuntime setup mode deadline).bindingTraffic leaks who
            (rightActive.respond
                (serviceApplication setup mode deadline leaks) actor rightResponse))
    (included : ∀ id message, left.network.lookup id = some message →
      Option.map (fun state => state.playerView who)
          (handle (serviceRuntime setup mode deadline) left.application ⟨message.id,
              message.payload.call⟩) =
        Option.map (fun state => state.playerView who)
          (handle (serviceRuntime setup mode deadline) right.application ⟨message.id,
              message.payload.call⟩)) :
    ((serviceApplication setup mode deadline leaks).round scheduler players left).map
        (blockReadout who) =
      ((serviceApplication setup mode deadline leaks).round scheduler players right).map
        (blockReadout who) := by
  let app := serviceApplication setup mode deadline leaks
  have sameTraffic : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right := congrArg Prod.fst same
  have sameCounters : blockCounters left = blockCounters right := congrArg Prod.snd same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) sameTraffic
  have observed := observeEnvironment_eq_of_bindingTraffic who sameTraffic
  have networks : left.network = right.network := congrArg Prod.fst sameTraffic
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) sameTraffic
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) sameTraffic
  have includeTraffic (id : MessageId Player) :
      (serviceRuntime setup mode deadline).bindingTraffic leaks who (left.includePending app id) =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who
            (right.includePending app id) :=
    include_bindingTraffic_of_handled sameTraffic id fun message found =>
      included id message found
  refine app.round_map_congr scheduler _ _ left right _ environments observed networks ?_ ?_
  · intro actor selected sample sampled
    let leftActive := left.sampledActivation app actor sample
    let rightActive := right.sampledActivation app actor sample
    have activated : (serviceRuntime setup mode deadline).bindingTraffic leaks who leftActive =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who rightActive :=
      bindingTraffic_activation
          (serviceRuntime setup mode deadline) leaks left right who actor sameTraffic sample
    have leftCounters : blockCounters leftActive = blockCounters left := rfl
    have rightCounters : blockCounters rightActive = blockCounters right := rfl
    have activePublics : (leftActive.observe app actor).application.publicView =
        (rightActive.observe app actor).application.publicView := publics
    change ((players actor (leftActive.logs actor)
        (leftActive.observe app actor)).map (leftActive.respond app actor)).map _ =
      ((players actor (rightActive.logs actor)
        (rightActive.observe app actor)).map (rightActive.respond app actor)).map _
    by_cases isWho : actor = who
    · subst actor
      have recalled : leftActive.logs who = rightActive.logs who :=
        congrArg (fun value => value.2.2.2.1) activated
      rw [recalled, observe_eq_of_bindingTraffic who activated, PMF.map_comp, PMF.map_comp]
      apply map_congr_on_support _
      intro response _
      refine Prod.ext (bindingTraffic_owner_response
          (serviceRuntime setup mode deadline) leaks leftActive rightActive who activated
          response) ?_
      exact blockCounters_respond_congr who response response
        (leftCounters.trans (sameCounters.trans rightCounters.symm)) activePublics rfl
    · obtain ⟨leftResponse, rightResponse, leftPure, rightPure, submitted, traffic⟩ :=
        matched actor isWho (by rw [environments, observed]; exact selected) sample
          (by rw [networks]; exact sampled)
      rw [leftPure, rightPure, PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map]
      apply congrArg PMF.pure
      refine Prod.ext traffic ?_
      exact blockCounters_respond_congr actor leftResponse rightResponse
        (leftCounters.trans (sameCounters.trans rightCounters.symm)) activePublics submitted
  · intro command selected inactive
    cases command with
    | activate actor => cases inactive
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        apply congrArg PMF.pure
        have includedTraffic := includeTraffic id
        have leftKeeps := ReactiveApplication.Execution.includePending_recall app left id
        have rightKeeps := ReactiveApplication.Execution.includePending_recall app right id
        refine Prod.ext ?_ ?_
        · change (serviceRuntime setup mode deadline).bindingTraffic leaks who
              { left.includePending app id with environmentRecall := _ } =
            (serviceRuntime setup mode deadline).bindingTraffic leaks who
              { right.includePending app id with environmentRecall := _ }
          rw [environments, observed]
          exact bindingTraffic_with_environmentRecall who includedTraffic _
        · change blockCounters { left.includePending app id with environmentRecall := _ } =
            blockCounters { right.includePending app id with environmentRecall := _ }
          exact (blockCounters_of_logs leftKeeps).trans
            (sameCounters.trans (blockCounters_of_logs rightKeeps).symm)
    | application command =>
        rw [map_blockReadout_of_recall who left _ (fun next reached => by
            rw [app.environmentStep_recall left next _ reached]),
          map_blockReadout_of_recall who right _ (fun next reached => by
            rw [app.environmentStep_recall right next _ reached]),
          application_environmentStep_traffic_congr sameTraffic command, sameCounters]
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        apply congrArg PMF.pure
        refine Prod.ext (bindingTraffic_record (leaks := leaks) who sameTraffic .wait) ?_
        change blockCounters left = blockCounters right
        exact sameCounters

/-- A first-turn reference client at its own event, where the reference's
kernel is a point mass, is the decided client of that action there. -/
theorem referenceTurnPolicy_eq_decided_of_kernel
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup mode).BehavioralProfile) (owner : Player)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (turn : execution.application.publicView.ownTurn? owner = some event)
    (active : owner ∉ execution.application.config.defaulted)
    (action : (serviceGraph setup mode).Action event)
    (opens : reference owner event owned
        ((serviceGraph setup mode).playerObserve owner execution.application.config) active =
      PMF.pure action) :
    serviceReferenceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) reference owner (execution.logs owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      decidedTurnPolicy setup leaks bound owner event action
        (execution.logs owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) := by
  let app := serviceApplication setup mode deadline leaks
  let family := serviceReferenceTurnFamily setup mode deadline leaks bound reference owner event
    turns
  have pin : (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).posterior
      (execution.logs owner) = PMF.pure 0 := by
    simpa only [List.nil_append] using app.policyMixture_posterior_pure_append
      (PMF.pure (0 : Fin (turns + 1))) family [] (execution.logs owner) 0 rfl
  rw [sourceServiceTurnPolicy_turn_reference setup leaks bound turns _ reference owner _ _
    event owned turn]
  change (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).policy _ _ = _
  rw [app.policyMixture_policy, pin, PMF.pure_bind]
  change app.turnScheduledPolicy (serviceTurn setup mode deadline leaks owner event)
    (some (0 : Fin (turns + 1)))
    (serviceReferenceOpportunity setup mode deadline leaks bound reference owner event)
    app.silentPolicy _ _ = _
  unfold decidedTurnPolicy
  by_cases selected : serviceTurn setup mode deadline leaks owner event (execution.logs owner)
      (execution.observe app owner) = some 0
  · rw [app.turnScheduledPolicy_selected _ (0 : Fin (turns + 1)) _ _ _ _ selected,
      app.turnScheduledPolicy_selected _ (0 : Fin 1) _ _ _ _ selected]
    unfold serviceReferenceOpportunity decidedOpportunity
    rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks reference owner execution
      event turn owned, dite_eq_right active]
    have opened : reference owner event owned
        (id ((serviceGraph setup mode).playerObserve owner execution.application.config))
        active = PMF.pure action := opens
    rw [opened, PMF.pure_map, PMF.pure_bind]
  · have unselected : ∀ (slot : Fin (turns + 1)), some (0 : Fin (turns + 1)) = some slot →
        serviceTurn setup mode deadline leaks owner event (execution.logs owner)
          (execution.observe app owner) ≠ some slot.val := by
      intro slot same
      cases same
      exact selected
    have unselectedOne : ∀ (slot : Fin 1), some (0 : Fin 1) = some slot →
        serviceTurn setup mode deadline leaks owner event (execution.logs owner)
          (execution.observe app owner) ≠ some slot.val := by
      intro slot same
      cases same
      exact selected
    rw [app.turnScheduledPolicy_unselected _ _ _ _ _ _ unselected,
      app.turnScheduledPolicy_unselected _ _ _ _ _ _ unselectedOne]

/-- Acceptance of an opening agrees on stores with the same binding and public
fields. -/
theorem openingAccepted_congr_public {event : (serviceGraph setup mode).EventId}
    {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    {left right : EventGraph.Store (serviceGraph setup mode).layout}
    (bound : binding.get? left = binding.get? right)
    (publicStores : (serviceGraph setup mode).publicStore left =
      (serviceGraph setup mode).publicStore right) :
    openingAccepted event left = openingAccepted event right := by
  have checked (proposal : PublicationResult (L.Val payload)) :
      GuardCheck.allAccepted? checks left proposal =
        GuardCheck.allAccepted? checks right proposal := by
    rw [← GuardCheck.allAccepted?_publicStore checks left, publicStores,
      GuardCheck.allAccepted?_publicStore]
  unfold openingAccepted
  rw [node]
  simp only [EventCode.resolveOutput?, bound, checked]

/-- A decided client that withholds at its own ready reveal is silent. -/
theorem decidedTurnPolicy_withhold_silent (bound : (serviceGraph setup mode).EventId → Nat)
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner) {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq) :
    decidedTurnPolicy setup leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) false) (execution.logs owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      PMF.pure ⟨none⟩ := by
  by_cases first : ownerTurns owner event execution = 0
  · rw [decidedTurnPolicy_open _ execution ready owned first]
    unfold decidedOpportunity
    rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_resolution_false leaks
      owner _ _ event owner payload binding checks outputEq codeEq node]
    split_ifs <;> rfl
  · apply decidedTurnPolicy_closed _ execution ready owned
    exact fun opened => first opened.1

/-- **An honest client in a block.** Among concurrently ready reveals, a
reference client that opens a publication exactly when the opening would be
accepted answers an activation with a point mass, alike from executions with
equal compared readouts and equal stored bindings at ready reveals: the opening
of its stored value, or silence. -/
theorem honest_block_matched {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store))) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : blockReadout who left = blockReadout who right)
    (leftTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (publications : ∀ event, left.application.config.cut.Ready event →
      ((serviceGraph setup mode).outputLayout event).IsPublication)
    (bindings : ∀ (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      left.application.config.cut.Ready event →
        binding.get? left.application.config.store = binding.get? right.application.config.store)
    (actor : Player) (other : actor ≠ who)
    (selected : (.activate actor : (serviceApplication setup mode deadline leaks).Command) ∈
      (scheduler left.environmentRecall
        (left.observeEnvironment (serviceApplication setup mode deadline leaks))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((serviceApplication setup mode deadline leaks).observePending actor
      left.network.pending).support) :
    let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
      turns (firstTurnTiming setup turns mode) reference) who deviation
    let leftActive := left.sampledActivation (serviceApplication setup mode deadline leaks)
      actor sample
    let rightActive := right.sampledActivation (serviceApplication setup mode deadline leaks)
      actor sample
    ∃ leftResponse rightResponse,
      players actor (leftActive.logs actor) (leftActive.observe
          (serviceApplication setup mode deadline leaks) actor) = PMF.pure leftResponse ∧
      players actor (rightActive.logs actor) (rightActive.observe
          (serviceApplication setup mode deadline leaks) actor) = PMF.pure rightResponse ∧
      (serviceRuntime setup mode deadline).submittedEvent? leaks leftResponse =
        (serviceRuntime setup mode deadline).submittedEvent? leaks rightResponse ∧
      (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (leftActive.respond (serviceApplication setup mode deadline leaks) actor leftResponse) =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (rightActive.respond (serviceApplication setup mode deadline leaks) actor
          rightResponse) := by
  intro players leftActive rightActive
  let app := serviceApplication setup mode deadline leaks
  let runtime := serviceRuntime setup mode deadline
  have sameTraffic : runtime.bindingTraffic leaks who left =
      runtime.bindingTraffic leaks who right := congrArg Prod.fst same
  have sameCounters : blockCounters left = blockCounters right := congrArg Prod.snd same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) sameTraffic
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) sameTraffic
  have networks : left.network = right.network := congrArg Prod.fst sameTraffic
  have activated := bindingTraffic_activation runtime leaks left right who actor
    sameTraffic sample
  have follows : players actor = serviceReferenceTurnPolicy setup mode deadline leaks bound
      turns (firstTurnTiming setup turns mode) reference actor := Function.update_of_ne other _ _
  simp only [follows]
  have leftMoved : leftActive ∈ (left.environmentStep app (.activate actor)).support := by
    rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
    exact ⟨sample, sampled, rfl⟩
  have rightMoved : rightActive ∈ (right.environmentStep app (.activate actor)).support := by
    rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
    exact ⟨sample, by rw [← networks]; exact sampled, rfl⟩
  obtain ⟨leftActiveTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
    scheduler leftRemaining left leftActive (.activate actor) leftTrace selected leftMoved
  obtain ⟨rightActiveTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
    scheduler rightRemaining right rightActive (.activate actor) rightTrace (by
      rw [← environments, ← observeEnvironment_eq_of_bindingTraffic who sameTraffic]
      exact selected) rightMoved
  have leftFacts := legalFacts setup leaks horizon scheduler _ leftActiveTrace
  have rightFacts := legalFacts setup leaks horizon scheduler _ rightActiveTrace
  have silentTraffic : runtime.bindingTraffic leaks who
      (leftActive.respond app actor ⟨none⟩) =
      runtime.bindingTraffic leaks who (rightActive.respond app actor ⟨none⟩) :=
    bindingTraffic_respond_other other.symm activated _ _ (Or.inl ⟨rfl, rfl⟩)
  cases turnEq : left.application.publicView.ownTurn? actor with
  | none =>
      have rightTurn : right.application.publicView.ownTurn? actor = none := publics ▸ turnEq
      have leftSilent : serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) reference actor (leftActive.logs actor)
          (leftActive.observe app actor) = PMF.pure ⟨none⟩ := by
        unfold serviceReferenceTurnPolicy
        change (match left.application.publicView.ownTurn? actor with
          | none => _ | some _ => _) = _
        rw [turnEq]
        rfl
      have rightSilent : serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) reference actor (rightActive.logs actor)
          (rightActive.observe app actor) = PMF.pure ⟨none⟩ := by
        unfold serviceReferenceTurnPolicy
        change (match right.application.publicView.ownTurn? actor with
          | none => _ | some _ => _) = _
        rw [rightTurn]
        rfl
      exact ⟨⟨none⟩, ⟨none⟩, leftSilent, rightSilent, rfl, silentTraffic⟩
  | some event =>
      have rightTurn : right.application.publicView.ownTurn? actor = some event :=
        publics ▸ turnEq
      obtain ⟨readyView, owned⟩ := left.application.publicView.ownTurn?_spec actor event turnEq
      have ready := (left.application.publicView_eventReady event).mp readyView
      have cuts := cut_eq_of_publicView_eq publics
      have rightReady : right.application.config.cut.Ready event := by rw [← cuts]; exact ready
      have publication := publications event ready
      have leftActiveOwner : actor ∉ leftActive.application.config.defaulted :=
        leftActive.application.active_of_ready_owned leftFacts.quiescent ready owned
      have rightActiveOwner : actor ∉ rightActive.application.config.defaulted :=
        rightActive.application.active_of_ready_owned rightFacts.quiescent rightReady owned
      have counted := congrFun (congrFun sameCounters actor) event
      have sameTurns : ownerTurns actor event left = ownerTurns actor event right :=
        congrArg Prod.fst counted
      have sameRecorded : runtime.eventRecorded leaks (left.logs actor) event =
          runtime.eventRecorded leaks (right.logs actor) event := congrArg Prod.snd counted
      cases node : nodeView (serviceGraph setup mode) event with
      | bind owner payload outputEq codeEq =>
          have impossible := publication
          rw [outputEq] at impossible
          exact impossible.elim
      | sample payload law outputEq codeEq =>
          have impossible := publication
          rw [outputEq] at impossible
          exact impossible.elim
      | resolve owner payload binding checks outputEq codeEq =>
          have sameOwner : owner = actor :=
            Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
          subst owner
          have storedEq := bindings event actor payload binding checks outputEq codeEq node ready
          have publicStores : (serviceGraph setup mode).publicStore left.application.config.store =
              (serviceGraph setup mode).publicStore right.application.config.store :=
            congrArg (fun view : PublicView (serviceGraph setup mode) =>
              view.observation.store) publics
          have acceptedSame : openingAccepted event left.application.config.store =
              openingAccepted event right.application.config.store :=
            openingAccepted_congr_public node storedEq publicStores
          have leftKernel := decides left.application.config event actor payload binding checks
            outputEq codeEq node owned leftActiveOwner
          have rightKernel := decides right.application.config event actor payload binding checks
            outputEq codeEq node owned rightActiveOwner
          rw [referenceTurnPolicy_eq_decided_of_kernel bound turns reference actor event owned
              leftActive turnEq leftActiveOwner _ leftKernel,
            referenceTurnPolicy_eq_decided_of_kernel bound turns reference actor event owned
              rightActive rightTurn rightActiveOwner _ rightKernel, ← acceptedSame]
          cases acceptedEq : openingAccepted event left.application.config.store
          · exact ⟨⟨none⟩, ⟨none⟩, decidedTurnPolicy_withhold_silent bound leftActive ready owned
              node, decidedTurnPolicy_withhold_silent bound rightActive rightReady owned node, rfl,
              silentTraffic⟩
          let action := cast (congrArg EventField.Action outputEq.symm) true
          by_cases opened : ownerTurns actor event left = 0 ∧
              runtime.eventRecorded leaks (left.logs actor) event = false ∧
              left.application.publicView.InclusionFitsDeadline runtime bound event
          · obtain ⟨first, unrecorded, fits⟩ := opened
            have rightFirst : ownerTurns actor event right = 0 := sameTurns ▸ first
            have rightUnrecorded : runtime.eventRecorded leaks (right.logs actor) event = false :=
              sameRecorded ▸ unrecorded
            have rightFits : right.application.publicView.InclusionFitsDeadline runtime bound
                event := publics ▸ fits
            rw [decidedTurnPolicy_open action leftActive ready owned first,
              decidedTurnPolicy_open action rightActive rightReady owned rightFirst]
            by_cases success : ∃ value, binding.get? left.application.config.store =
                some (.success value)
            · obtain ⟨value, leftStored⟩ := success
              have rightStored : binding.get? right.application.config.store =
                  some (.success value) := storedEq ▸ leftStored
              obtain ⟨candidate, leftAccepted, candidateOwner, leftFixed⟩ :=
                leftFacts.binding.success_provenance binding value leftStored
              have rightAccepted : rightActive.application.accepted binding.field =
                  some candidate := by
                change right.application.accepted binding.field = _
                exact (congrFun (congrArg PublicView.accepted publics) binding.field).symm.trans
                  leftAccepted
              obtain ⟨rightCandidate, acceptedOther, _, rightFixed⟩ :=
                rightFacts.binding.success_provenance binding value rightStored
              have candidateEq : rightCandidate = candidate :=
                Option.some.inj (acceptedOther.symm.trans rightAccepted)
              subst rightCandidate
              let leftMaterial :=
                (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
                actor (app.observePlayer leftActive.application actor)
                (leftActive.network.known actor)
              let rightMaterial :=
                (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
                actor (app.observePlayer rightActive.application actor)
                (rightActive.network.known actor)
              have leftDecision : runtime.canonicalServiceDecision leaks actor
                  (leftActive.logs actor) (leftActive.observe app actor) event action =
                    ⟨some leftMaterial⟩ :=
                canonical_opening_exact outputEq codeEq node leftActive leftFacts.inputs candidate
                  value leftAccepted candidateOwner leftFixed leftActiveOwner leftStored
              have rightDecision : runtime.canonicalServiceDecision leaks actor
                  (rightActive.logs actor) (rightActive.observe app actor) event action =
                    ⟨some rightMaterial⟩ :=
                canonical_opening_exact outputEq codeEq node rightActive rightFacts.inputs
                  candidate value rightAccepted candidateOwner rightFixed rightActiveOwner
                  rightStored
              refine ⟨⟨some leftMaterial⟩, ⟨some rightMaterial⟩,
                decidedOpportunity_transmits action leftActive unrecorded fits _ leftDecision,
                decidedOpportunity_transmits action rightActive rightUnrecorded rightFits _
                  rightDecision, rfl, ?_⟩
              apply bindingTraffic_respond_other other.symm activated
              refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
              rw [opening_normal_packet leftActive actor event candidate ⟨payload, value⟩
                candidateOwner leftFixed, opening_normal_packet rightActive actor event candidate
                ⟨payload, value⟩ candidateOwner rightFixed]
              have activePublics : leftActive.application.publicView =
                  rightActive.application.publicView := publics
              rw [activePublics]
            · push Not at success
              have unavailable (current : app.Execution)
                  (failed : ∀ value, binding.get? current.application.config.store ≠
                    some (.success value)) :
                  runtime.canonicalServiceDecision leaks actor (current.logs actor)
                    (current.observe app actor) event action = ⟨none⟩ :=
                runtime.canonicalServiceDecision_resolution_unavailable leaks actor
                  (current.logs actor) (current.observe app actor) event actor payload binding
                  checks outputEq codeEq node (fun value _ observed _ _ => by
                    apply failed value
                    have visible : binding.get? ((serviceGraph setup mode).playerStore actor
                        current.application.config.store) =
                        binding.get? current.application.config.store :=
                      binding.get?_playerStore actor _ rfl
                    rw [← visible]
                    exact observed)
              have silentAt (current : app.Execution)
                  (failed : ∀ value, binding.get? current.application.config.store ≠
                    some (.success value)) :
                  decidedOpportunity setup leaks bound actor event action (current.logs actor)
                    (current.observe app actor) = PMF.pure ⟨none⟩ := by
                unfold decidedOpportunity
                rw [unavailable current failed]
                split_ifs <;> rfl
              refine ⟨⟨none⟩, ⟨none⟩, silentAt leftActive success,
                silentAt rightActive (fun value stored => success value (storedEq.trans stored)),
                rfl, silentTraffic⟩
          · have rightClosed : ¬ (ownerTurns actor event right = 0 ∧
                runtime.eventRecorded leaks (right.logs actor) event = false ∧
                right.application.publicView.InclusionFitsDeadline runtime bound event) := by
              rw [← sameTurns, ← sameRecorded, ← publics]
              exact opened
            exact ⟨⟨none⟩, ⟨none⟩, decidedTurnPolicy_closed action leftActive ready owned opened,
              decidedTurnPolicy_closed action rightActive rightReady owned rightClosed, rfl,
              silentTraffic⟩

section Block

variable {graph : Vegas.EventGraph Player L}

/-- A configuration inside the block of ranks `[start, finish)`: every earlier
event has completed and no event from `finish` on has. -/
def InBlock (start finish : Nat) (config : graph.Config) : Prop :=
  (∀ event : graph.EventId, event.val < start → event ∈ config.cut.completed) ∧
    ∀ event : graph.EventId, finish ≤ event.val → event ∉ config.cut.completed

/-- Every event of rank before `finish` has completed. -/
def BlockDone (finish : Nat) (config : graph.Config) : Prop :=
  ∀ event : graph.EventId, event.val < finish → event ∈ config.cut.completed

instance (finish : Nat) (config : graph.Config) : Decidable (BlockDone finish config) := by
  unfold BlockDone
  infer_instance

/-- The block's shape: inside an unfinished block, only block events are ready. -/
def BlockShaped (start finish : Nat) : Prop :=
  ∀ config : graph.Config, InBlock start finish config → ¬ BlockDone finish config →
    ∀ event, config.cut.Ready event → start ≤ event.val ∧ event.val < finish

/-- Completion is monotone along graph paths, so a finished block stays finished. -/
theorem BlockDone.path {finish : Nat} {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after)
    (done : BlockDone finish before) : BlockDone finish after :=
  fun event smaller => Config.Step.path_completed_mono path (done event smaller)

/-- Graph steps keep a configuration inside an unfinished block. -/
theorem InBlock.path {start finish : Nat} (shaped : BlockShaped (graph := graph) start finish)
    {before after : graph.Config} (path : Relation.ReflTransGen Config.Step before after)
    (inside : InBlock start finish before) (unfinished : ¬ BlockDone finish after) :
    InBlock start finish after := by
  induction path with
  | refl => exact inside
  | @tail middle last _ moved previous =>
      have middleUnfinished : ¬ BlockDone finish middle := fun done =>
        unfinished (BlockDone.path (Relation.ReflTransGen.single moved) done)
      have middleInside := previous middleUnfinished
      obtain ⟨event, ready, action, member⟩ := moved
      have bounded := shaped middle middleInside middleUnfinished event ready
      refine ⟨fun other smaller => Config.Step.path_completed_mono
        (Relation.ReflTransGen.single ⟨event, ready, action, member⟩)
        (middleInside.1 other smaller), fun other late completed => ?_⟩
      rw [middle.step_cut event ready action last member, EventOrder.Cut.mem_complete]
        at completed
      rcases completed with same | earlier
      · subst same
        omega
      · exact middleInside.2 other late earlier

end Block

/-- Two configurations agree on the stored binding of every reveal of ranks in
`[start, finish)`. -/
def BindingsAgree (start finish : Nat)
    (left right : (serviceGraph setup mode).Config) : Prop :=
  ∀ (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
    nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq →
    start ≤ event.val → event.val < finish →
      left.store binding.field = right.store binding.field ∧
        (left.store binding.field).isSome

theorem BindingsAgree.trans {start finish : Nat} {first second third :
    (serviceGraph setup mode).Config}
    (left : BindingsAgree start finish first second)
    (right : BindingsAgree start finish second third) :
    BindingsAgree start finish first third := fun event owner payload binding checks outputEq
      codeEq node early late =>
  ⟨(left event owner payload binding checks outputEq codeEq node early late).1.trans
      (right event owner payload binding checks outputEq codeEq node early late).1,
    (left event owner payload binding checks outputEq codeEq node early late).2⟩

theorem BindingsAgree.symm {start finish : Nat} {first second :
    (serviceGraph setup mode).Config}
    (agree : BindingsAgree start finish first second)
    (available : BindingsAgree start finish second second) :
    BindingsAgree start finish second first := fun event owner payload binding checks outputEq
      codeEq node early late =>
  ⟨(agree event owner payload binding checks outputEq codeEq node early late).1.symm,
    (available event owner payload binding checks outputEq codeEq node early late).2⟩

/-- Agreement includes the availability of the left bindings. -/
theorem BindingsAgree.self {start finish : Nat} {left right : (serviceGraph setup mode).Config}
    (agree : BindingsAgree start finish left right) : BindingsAgree start finish left left :=
  fun event owner payload binding checks outputEq codeEq node early late =>
    ⟨rfl, (agree event owner payload binding checks outputEq codeEq node early late).2⟩

/-- Stored bindings persist along graph paths. -/
theorem BindingsAgree.path {start finish : Nat} {before after : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step before after)
    (available : BindingsAgree start finish before before) :
    BindingsAgree start finish after before := by
  intro event owner payload binding checks outputEq codeEq node early late
  obtain ⟨_, present⟩ := available event owner payload binding checks outputEq codeEq node early
    late
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
  have kept := Config.Step.path_store_of_some path binding.field value stored
  rw [kept, stored]
  exact ⟨rfl, rfl⟩

/-- Agreeing stored binding fields give agreeing typed bindings. -/
theorem BindingsAgree.get? {start finish : Nat} {left right : (serviceGraph setup mode).Config}
    (agree : BindingsAgree start finish left right) (event : (serviceGraph setup mode).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (early : start ≤ event.val) (late : event.val < finish) :
    binding.get? left.store = binding.get? right.store := by
  unfold FieldRef.get?
  rw [(agree event owner payload binding checks outputEq codeEq node early late).1]

/-- **The block's stopped readout.** From executions inside an unfinished
block with equal compared readouts and agreeing stored bindings of the block's
reveals, reference clients that open a publication exactly when the opening would be
accepted, against any deviation, give equal laws of the readout when the block
finishes. -/
theorem block_stopped_readout_congr {horizon : Nat}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store))) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication) :
    ∀ (count leftRemaining rightRemaining : Nat)
      (left right : (serviceApplication setup mode deadline leaks).Execution),
      ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨leftRemaining + count, none, left⟩) →
      ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨rightRemaining + count, none, right⟩) →
      (¬ BlockDone finish left.application.config →
        InBlock start finish left.application.config) →
      (¬ BlockDone finish right.application.config →
        InBlock start finish right.application.config) →
      BindingsAgree start finish left.application.config right.application.config →
      BindingsAgree start finish right.application.config right.application.config →
      blockReadout who left = blockReadout who right →
      ((serviceApplication setup mode deadline leaks).runUntil scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) reference) who deviation)
        (fun final => BlockDone finish final.application.config) count left).map
          (blockReadout who) =
      ((serviceApplication setup mode deadline leaks).runUntil scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) reference) who deviation)
        (fun final => BlockDone finish final.application.config) count right).map
          (blockReadout who) := by
  intro count leftRemaining rightRemaining left right leftTrace rightTrace leftInside
    rightInside agree rightAvailable same
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) reference) who deviation
  let invariant := fun (origin : app.Execution) (count : Nat) (current : app.Execution) =>
    (∃ remaining, Nonempty ((app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + count, none, current⟩))) ∧
    (¬ BlockDone finish current.application.config →
      InBlock start finish current.application.config) ∧
    BindingsAgree start finish current.application.config origin.application.config
  have advance (origin : app.Execution) (n : Nat) (current : app.Execution)
      (valid : invariant origin (n + 1) current)
      (running : ¬ BlockDone finish current.application.config)
      (next : app.Execution) (reached : next ∈ (app.round scheduler players current).support) :
      invariant origin n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, inside, kept⟩ := valid
    have before : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon scheduler
      players (remaining + n) current next before reached
    have path := reactive_round_graph_steps (serviceRuntime setup mode deadline) leaks scheduler
      players current next reached
    exact ⟨⟨remaining, ⟨nextTrace⟩⟩, fun unfinished => (inside running).path shaped path
      unfinished, (BindingsAgree.path path kept.self).trans kept⟩
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler players players
    (fun final => BlockDone finish final.application.config) (blockReadout who)
    (invariant left) (invariant right)
  · intro n current other _ _ equal
    have publics : current.application.publicView = other.application.publicView :=
      congrArg (fun value => value.1.2.2.2.2.2) equal
    have cuts := cut_eq_of_publicView_eq publics
    simp only [BlockDone, cuts]
  · intro n current other currentValid otherValid equal running
    obtain ⟨⟨currentRest, ⟨currentTrace⟩⟩, currentInside, currentKept⟩ := currentValid
    obtain ⟨⟨otherRest, ⟨otherTrace⟩⟩, _, otherKept⟩ := otherValid
    have currentBefore : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(currentRest + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using currentTrace
    have otherBefore : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(otherRest + n) + 1, none, other⟩) := by
      simpa only [Nat.add_assoc] using otherTrace
    have inside := currentInside running
    have agreeNow : BindingsAgree start finish current.application.config
        other.application.config :=
      currentKept.trans (agree.trans (otherKept.symm rightAvailable))
    have currentFacts := legalFacts setup leaks horizon scheduler _ currentBefore
    have otherFacts := legalFacts setup leaks horizon scheduler _ otherBefore
    have views : current.application.playerView who = other.application.playerView who :=
      congrArg (fun value => value.1.2.2.2.2.1) equal
    have bindings : ∀ (event : (serviceGraph setup mode).EventId) (owner : Player)
        (payload : L.Ty)
        (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
        (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
        (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
        (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
          ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
        nodeView (serviceGraph setup mode) event =
          .resolve owner payload binding checks outputEq codeEq →
        current.application.config.cut.Ready event →
          binding.get? current.application.config.store =
            binding.get? other.application.config.store := by
      intro event owner payload binding checks outputEq codeEq node ready
      have bounded := shaped _ inside running event ready
      exact agreeNow.get? event owner payload binding checks outputEq codeEq node bounded.1
        bounded.2
    apply blockRound_readout_congr scheduler who players equal
    · intro actor other' selected sample sampled
      exact honest_block_matched bound turns reference decides who deviation equal currentBefore
        otherBefore (fun event ready => publications event (shaped _ inside running event
          ready).1 (shaped _ inside running event ready).2) bindings actor other' selected
        sample sampled
    · intro id message _
      exact block_handle_playerView_congr current.application other.application who views
        currentFacts.binding otherFacts.binding bindings ⟨message.id, message.payload.call⟩
  · exact advance left
  · exact advance right
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, leftInside, agree.self⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, rightInside, rightAvailable⟩
  · exact same

/-- A decided client either stays silent or sends its canonical decision. -/
theorem decidedTurnPolicy_support (bound : (serviceGraph setup mode).EventId → Nat)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈
      (decidedTurnPolicy setup leaks bound owner event action past view).support) :
    response = ⟨none⟩ ∨
      response = (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner past
        view event action := by
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy at chosen
  dsimp only at chosen
  split at chosen
  · unfold decidedOpportunity at chosen
    split_ifs at chosen <;>
      first
      | exact Or.inl ((PMF.mem_support_pure_iff _ _).mp chosen)
      | exact Or.inr ((PMF.mem_support_pure_iff _ _).mp chosen)
  · exact Or.inl ((PMF.mem_support_pure_iff _ _).mp chosen)

/-- **An honest client in a block submits only accepted reveals.** Among
concurrently ready reveals, a first-turn effective-opening client answers an
activation with a response that submits an event only when that event is its
own ready reveal and its opening is accepted. -/
theorem honest_block_submits_accepted (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (execution : (serviceApplication setup mode deadline leaks).Execution) (owner : Player)
    (quiescent : ∀ query, ¬ execution.application.AutomaticReady query)
    (publications : ∀ event, execution.application.config.cut.Ready event →
      ((serviceGraph setup mode).outputLayout event).IsPublication)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈ (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) reference owner (execution.logs owner)
      (execution.observe (serviceApplication setup mode deadline leaks) owner)).support)
    (event : (serviceGraph setup mode).EventId)
    (submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks response =
      some event) :
    execution.application.config.cut.Ready event ∧
      (serviceGraph setup mode).actor? event = some owner ∧
      openingAccepted event execution.application.config.store = true := by
  let app := serviceApplication setup mode deadline leaks
  cases turnEq : execution.application.publicView.ownTurn? owner with
  | none =>
      have silent : serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) reference owner (execution.logs owner)
          (execution.observe app owner) = PMF.pure ⟨none⟩ := by
        unfold serviceReferenceTurnPolicy
        change (match execution.application.publicView.ownTurn? owner with
          | none => _ | some _ => _) = _
        rw [turnEq]
        rfl
      rw [silent, PMF.mem_support_pure_iff] at chosen
      subst chosen
      cases submitted
  | some current =>
      obtain ⟨readyView, owned⟩ :=
        execution.application.publicView.ownTurn?_spec owner current turnEq
      have ready := (execution.application.publicView_eventReady current).mp readyView
      have active : owner ∉ execution.application.config.defaulted :=
        execution.application.active_of_ready_owned quiescent ready owned
      obtain ⟨actorName, payload, binding, checks, outputEq, codeEq, node⟩ :=
        exists_resolve_of_publication (publications current ready)
      have actorSame : actorName = owner :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actorName
      have kernel := decides execution.application.config current owner payload binding checks
        outputEq codeEq node owned active
      rw [referenceTurnPolicy_eq_decided_of_kernel bound turns reference owner current owned
        execution turnEq active _ kernel] at chosen
      cases acceptedEq : openingAccepted current execution.application.config.store
      · rw [acceptedEq, decidedTurnPolicy_withhold_silent bound execution ready owned node,
          PMF.mem_support_pure_iff] at chosen
        subst chosen
        cases submitted
      · rw [acceptedEq] at chosen
        rcases decidedTurnPolicy_support bound owner current _ _ _ response chosen with
          silent | decided
        · subst silent
          cases submitted
        · rcases (serviceRuntime setup mode deadline).canonicalServiceDecision_submittedEvent
              leaks owner (execution.logs owner) (execution.observe app owner) current _ with
            none | named
          · rw [← decided, submitted] at none
            cases none
          · rw [← decided, submitted] at named
            cases named
            exact ⟨ready, owned, acceptedEq⟩

end Vegas
