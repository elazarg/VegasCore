/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTurnSubmissions
import Vegas.Pending.ReactiveBindingResources

/-! # A fixed first-turn decision completes its event with that action

From a completion boundary of the turn-counted policy, suppose the owner of
the current event decides a fixed action at its first turn there and every
other response is silent. Under the asynchronous contract with
`delay + bound < deadline`, every stopped point has completed the event with
exactly that action (`Vegas.decided_completion`).

* The first turn comes before any expiry: an expiry needs the deadline to have
  passed, and by then the scheduler has activated the owner.
* A binding decision submits a fresh, acceptable commitment to a fresh
  candidate prepared with the decided value; a disclosure of `true` that the
  source makes effective submits an acceptable certified opening. By the
  timeliness lemma that packet is accepted, and the event completes only
  through it, with the decided action.
* A disclosure of `false` is silence; no packet addresses the event, so only
  expiry completes it, with `false`.

The invariants are properties of play on the support of the turn-counted
policy, trembles included, up to the boundary, and of the decided policy
after it. They are not claims about arbitrary deviations.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

section Actions

variable {setup}

/-- The action with which expiry completes an event: failure for a binding,
`false` for a disclosure. -/
def ExpiryAction (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) : Prop :=
  match nodeView (serviceGraph setup mode) event with
  | .bind _ payload outputEq _ =>
      (cast (congrArg EventGraph.EventField.Action outputEq) action :
        PublicationResult (L.Val payload)) = .failure
  | .resolve _ _ _ _ outputEq _ =>
      (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = false
  | .sample .. => False

/-- A packet emitted by `entry` realizes `action`: accepted at a state with the
configuration `config` and the candidate meanings of `state`, the handler
completes the event with `action`. -/
def RealizesAt (config : (serviceGraph setup mode).Config)
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  match nodeView (serviceGraph setup mode) event with
  | .bind _ payload outputEq _ =>
      ∃ handle, message.payload.call = .commitment event handle ∧
        state.candidates.lookup handle ≠ .fresh ∧
        state.bindingResult handle payload =
          cast (congrArg EventGraph.EventField.Action outputEq) action
  | .resolve owner payload binding checks outputEq _ =>
      (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true ∧
      ∃ handle value, message.payload.call = .opening event handle ⟨payload, value⟩ ∧
        handle.1 = owner ∧
        entry.beforeView.application.publicView.accepted binding.field = some handle ∧
        state.candidates.lookup handle = .openable ⟨payload, value⟩ ∧
        binding.get? config.store = some (.success value) ∧
        ∃ result, EventGraph.EventCode.resolveOutput? binding checks true config.store =
          some result
  | .sample .. => False

end Actions

section Completion

variable {setup leaks}

/-- Realization survives every round before completion: only candidate
meanings are read from the current state, and fixed meanings never change. -/
theorem RealizesAt.round {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {config : (serviceGraph setup mode).Config}
    {execution next : (serviceApplication setup mode deadline leaks).Execution}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    {entry : (serviceApplication setup mode deadline leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (realized : RealizesAt leaks config execution.application event action entry message)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    RealizesAt leaks config next.application event action entry message := by
  revert realized
  unfold RealizesAt
  cases nodeView (serviceGraph setup mode) event with
  | bind owner payload outputEq codeEq =>
      rintro ⟨handle, call, fixed, result⟩
      have same := round_candidate_fixed setup leaks reached handle fixed
      refine ⟨handle, call, same ▸ fixed, ?_⟩
      simp only [State.bindingResult, same] at result ⊢
      exact result
  | resolve owner payload binding checks outputEq codeEq =>
      rintro ⟨isTrue, handle, value, call, owner', associated, fixed, rest⟩
      have same := round_candidate_fixed setup leaks reached handle (by rw [fixed]; simp)
      exact ⟨isTrue, handle, value, call, owner', associated, same.trans fixed, rest⟩
  | sample => exact id

/-- The conditions under which the handler accepts a commitment. -/
private theorem commitment_accepted_conditions
    (state next : EventGraphRuntime.State (serviceGraph setup mode)) (id : MessageId Player)
    (event : (serviceGraph setup mode).EventId) (handle : Handle (serviceGraph setup mode))
    (owner : Player) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (accepted : EventGraphRuntime.handle (serviceRuntime setup mode deadline) state
        ⟨id, .commitment event handle⟩ = some next) : state.config.cut.Ready event ∧
    state.WithinDeadline (serviceRuntime setup mode deadline) event ∧ id.1 = owner ∧ handle.1 =
    owner ∧ state.accepted (.inr event) = none ∧
      state.HandleUnused handle := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline (serviceRuntime setup mode deadline) event
    · simp only [EventGraphRuntime.handle, dite_eq_left ready, dite_eq_left timely, node]
        at accepted
      split at accepted
      · rename_i sender
        split at accepted
        · rename_i handleOwner
          split at accepted
          · rename_i vacant
            split at accepted
            · rename_i unused
              exact ⟨ready, timely, sender, handleOwner, vacant, unused⟩
            · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted
    · simp [EventGraphRuntime.handle, ready, timely] at accepted
  · simp [EventGraphRuntime.handle, ready] at accepted

/-- An opening is accepted only before the deadline. -/
private theorem opening_accepted_timely
    (state next : EventGraphRuntime.State (serviceGraph setup mode)) (id : MessageId Player)
    (event : (serviceGraph setup mode).EventId) (handle : Handle (serviceGraph setup mode))
    (raw : Raw L) (ready : state.config.cut.Ready event)
    (accepted : EventGraphRuntime.handle (serviceRuntime setup mode deadline) state
        ⟨id, .opening event handle raw⟩ = some next) :
    state.WithinDeadline (serviceRuntime setup mode deadline) event := by
  by_contra late
  simp [EventGraphRuntime.handle, ready, late] at accepted

/-- **Completion through a realizing packet.** If the handler accepts a packet
that realizes `action`, the event completes with `action`. -/
theorem include_realized (execution : (serviceApplication setup mode deadline leaks).Execution)
    (eventStable : EntryEventStable (serviceRuntime setup mode deadline) leaks execution)
    (config : (serviceGraph setup mode).Config) (same : execution.application.config = config)
    (event : (serviceGraph setup mode).EventId) (ready : config.cut.Ready event)
    (owner : Player) (owned : (serviceGraph setup mode).actor? event = some owner)
    (action : (serviceGraph setup mode).Action event)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (member : entry ∈ execution.recall owner)
    (seen : entry.beforeView.application.publicView.EventReady event)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (authored : message.sender = owner)
    (realized : RealizesAt leaks config execution.application event action entry message)
    (next : EventGraphRuntime.State (serviceGraph setup mode))
    (accepted : EventGraphRuntime.handle (serviceRuntime setup mode deadline) execution.application
      ⟨message.id, message.payload.call⟩ = some next) :
    next.config ∈ (config.step event ready action).support := by
  subst same
  revert realized
  unfold RealizesAt
  cases node : nodeView (serviceGraph setup mode) event with
  | bind actor payload outputEq codeEq =>
      rintro ⟨handle, call, _, result⟩
      rw [call] at accepted
      obtain ⟨_, timely, sender, handleOwner, vacant, unused⟩ :=
        commitment_accepted_conditions _ _ _ _ _ actor payload outputEq codeEq node accepted
      rw [handle_commitment_eq (serviceRuntime setup mode deadline) _ _ event handle actor payload
              outputEq codeEq node ready timely sender handleOwner vacant unused, Option.some.injEq]
          at accepted
      subst accepted
      have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (execution.application.bindingResult handle payload) := by
        rw [result, cast_cast, cast_eq]
      rw [actionEq, Vegas.commit_step _ _ ready outputEq codeEq]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | resolve actor payload binding checks outputEq codeEq =>
      rintro ⟨isTrue, handle, value, call, handleOwner, associatedThen, verified, stored, result,
        resolved⟩
      have actorEq : actor = owner := by
        have actorOf := nodeView_resolve_actor outputEq codeEq
        exact Option.some.inj (actorOf.symm.trans owned)
      subst actorEq
      rw [call] at accepted
      have timely := opening_accepted_timely _ _ _ _ _ _ ready accepted
      have associated : execution.application.accepted binding.field = some handle := by
        by_contra changed
        obtain ⟨_, _, _, _, acceptedChanged⟩ := eventStable actor entry member event seen
          (fun completed => ready.1 completed)
        have vacant := (acceptedChanged binding.field
          (fun same => changed (same.trans associatedThen))).1
        rw [associatedThen] at vacant
        cases vacant
      rw [handle_opening_eq (serviceRuntime setup mode deadline) _ _ event handle actor payload
              binding checks outputEq codeEq node ready timely authored handleOwner associated value
              verified stored result resolved, Option.some.injEq] at accepted
      subst accepted
      have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm) true := by
        rw [← isTrue, cast_cast, cast_eq]
      rw [actionEq, execution.application.config.step_eq_map_of_code event ready outputEq _ codeEq
        true (PMF.pure result) (by rw [EventGraph.EventCode.resolve_eval?, resolved]; rfl),
        PMF.pure_map]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | sample => exact False.elim

/-- **Completion by expiry.** An expiry that changes the configuration is due,
and completes the event with the expiry action. -/
theorem expire_completion (state next : EventGraphRuntime.State (serviceGraph setup mode))
    (event : (serviceGraph setup mode).EventId) (ready : state.config.cut.Ready event)
    (moved : next ∈
        (environmentStep (serviceRuntime setup mode deadline) state (.expire event)).support)
    (changed : next.config ≠ state.config) :
    (∃ entered, state.activatedAt event = some entered ∧
      (serviceRuntime setup mode deadline).deadline event ≤ state.clock - entered) ∧
    ∀ action, ExpiryAction event action →
      next.config ∈ (state.config.step event ready action).support := by
  have due : ∃ entered, state.activatedAt event = some entered ∧
      (serviceRuntime setup mode deadline).deadline event ≤ state.clock - entered := by
    cases activated : state.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated _ _ event ready activated,
          PMF.mem_support_pure_iff] at moved
        exact (changed (by rw [moved])).elim
    | some entered =>
        by_cases late : (serviceRuntime setup mode deadline).deadline event ≤ state.clock - entered
        · exact ⟨entered, rfl, late⟩
        · rw [environmentStep_expire_of_not_due _ _ event ready entered activated late,
            PMF.mem_support_pure_iff] at moved
          exact (changed (by rw [moved])).elim
  refine ⟨due, ?_⟩
  obtain ⟨entered, activated, late⟩ := due
  intro action expiring
  revert expiring
  unfold ExpiryAction
  cases node : nodeView (serviceGraph setup mode) event with
  | bind actor payload outputEq codeEq =>
      intro failed
      rw [environmentStep_expire_bind_eq _ _ event ready entered activated late actor payload
        outputEq codeEq node, PMF.mem_support_pure_iff] at moved
      subst moved
      have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)) := by
        rw [← failed, cast_cast, cast_eq]
      rw [actionEq, Vegas.commit_step _ _ ready outputEq codeEq]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | resolve actor payload binding checks outputEq codeEq =>
      intro withheld
      rcases environmentStep_expire_config_eq_or_mem_step _ _ next event moved with
        stutter | ⟨ready', recorded, stepped⟩
      · exact (changed stutter).elim
      · rw [environmentStep_expire_resolve_eq _ _ event ready entered activated late actor payload
          binding checks outputEq codeEq node, PMF.mem_support_pure_iff] at moved
        have actionEq : action = recorded := by
          have history := state.config.step_history event ready' recorded next.config stepped
          rw [moved] at history
          change state.config.history ++ [⟨event, cast (congrArg EventGraph.EventField.Action
            outputEq.symm) false⟩] = _ at history
          have last := List.append_cancel_left history
          simp only [List.cons.injEq, and_true] at last
          injection last with _ recordedEq
          rw [← recordedEq, ← withheld, cast_cast, cast_eq]
        rw [actionEq]
        exact stepped
  | sample => exact False.elim

end Completion

section FirstTurn

variable {setup leaks}

/-- The initial law is the image of initial inputs. -/
theorem serviceInitialLaw_eq_inputs :
    serviceInitialLaw setup mode =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)) := by
  rw [PMF.map_comp]
  rfl

/-- The initial law of the default runtime is the image of initial inputs. -/
theorem initialLaw_eq_inputs {setup : Setup (Player := Player) (L := L)} :
    initialLaw setup =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := graph setup)) :=
  serviceInitialLaw_eq_inputs

/-- The entry a fresh submission appends to its author's recall. -/
theorem respond_submit_recall (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) (material : (serviceApplication setup mode deadline leaks).Submission) :
    (execution.respond (serviceApplication setup mode deadline leaks) who ⟨some material⟩).recall
    who = execution.recall who ++
    [⟨execution.observe (serviceApplication setup mode deadline leaks) who, ⟨some material⟩, some
        ⟨(who, execution.network.nextSerial who),
        (serviceApplication setup mode deadline leaks).packet
        ((serviceApplication setup mode deadline leaks).submit execution.application who
        material) who
          (execution.network.known who) material⟩⟩] := by
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
  rfl

/-- **The compiled decision submits.** At a legal history where the owner of
the ready `event` is active, the compiled decision for an effective, non-silent
action transmits a call that realizes the action; when a packet included within
the inclusion bound still meets the deadline, the call is fresh and acceptable
on the owner's view. -/
theorem canonicalServiceDecision_submits {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    {remaining : Nat} {owner : Player}
    {middle : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, some owner, middle⟩))
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : middle.application.config.cut.Ready event)
    (entered : Nat) (activated : middle.application.activatedAt event = some entered)
    (action : (serviceGraph setup mode).Action event)
    (effective : EffectiveAction middle.application.config event action)
    (loud : ¬ SilentAction event action) :
    let app := serviceApplication setup mode deadline leaks
    let response := (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
        (middle.recall owner) (middle.observe app owner) event action
    ∃ material, response = ⟨some material⟩ ∧
      let entry : app.PlayerEntry := ⟨middle.observe app owner, response,
        some ⟨(owner, middle.network.nextSerial owner), app.packet
          (app.submit middle.application owner material) owner
          (middle.network.known owner) material⟩⟩
      let message : Message Player (WitnessedPacket (serviceGraph setup mode)) :=
        ⟨(owner, middle.network.nextSerial owner), app.packet
          (app.submit middle.application owner material) owner
          (middle.network.known owner) material⟩
      (middle.application.clock - entered + bound event <
          (serviceRuntime setup mode deadline).deadline event → FreshCall setup leaks owner event
          bound entry message) ∧ RealizesAt leaks middle.application.config
          (middle.respond app owner response).application event action entry message := by
  intro app response
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have deadlineOf (fits : middle.application.clock - entered + bound event <
      (serviceRuntime setup mode deadline).deadline event) :
      middle.application.clock - entered < (serviceRuntime setup mode deadline).deadline event := by
    omega
  have fitsViewOf (fits : middle.application.clock - entered + bound event <
      (serviceRuntime setup mode deadline).deadline event) :
      (middle.observe app owner).application.publicView.InclusionFitsDeadline
        (serviceRuntime setup mode deadline) bound event := by
    unfold PublicView.InclusionFitsDeadline
    change (match middle.application.activatedAt event with
      | none => False
      | some entered => middle.application.clock - entered + bound event <
          (serviceRuntime setup mode deadline).deadline event)
    rw [activated]
    exact fits
  have readyView : (middle.observe app owner).application.publicView.EventReady event :=
    (middle.application.publicView_eventReady event).mpr ready
  revert effective loud
  unfold EffectiveAction SilentAction
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | bind actor payload outputEq codeEq =>
      intro _ _
      have actorEq : actor = owner :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      have rawTrace := trace
      rw [serviceInitialLaw_eq_inputs] at rawTrace
      obtain ⟨least, _, leastSelected, _, _, vacant, _⟩ :=
        (serviceRuntime setup mode deadline).reactiveBinding_resources_history leaks _ horizon
        scheduler _ rawTrace actor rfl event ready
      obtain ⟨serial, selected⟩ := canonicalFreshSlot_isSome actor
        (middle.observe app actor).application least leastSelected
      have fresh : middle.application.candidates.lookup (actor, .prepared serial) = .fresh :=
        canonicalFreshSlot_spec actor _ serial selected
      have valid := (serviceRuntime setup mode deadline).reactiveBindingInvariant_history leaks _
          horizon scheduler rawTrace
      have unused : middle.application.HandleUnused (actor, .prepared serial) :=
        fun field associated => valid.accepted_fixed field _ associated fresh
      have decided := (serviceRuntime setup mode deadline).canonicalServiceDecision_binding leaks
          actor (middle.recall actor) (middle.observe app actor) event payload outputEq codeEq node
          serial selected choice
      change response = _ at decided
      refine ⟨_, decided, fun fits => ?_, ?_⟩
      · have inTime := deadlineOf fits
        refine ⟨⟨_, congrArg ReactiveApplication.Action.transmission decided⟩, rfl, rfl,
          rfl, readyView, fitsViewOf fits, ?_⟩
        refine ⟨?_, ?_⟩
        · change (middle.observe app actor).application.publicView.BindingIncludable
            (serviceRuntime setup mode deadline)
            ⟨(actor, middle.network.nextSerial actor), .commitment event (actor, .prepared serial)⟩
          simp only [PublicView.BindingIncludable, node]
          refine ⟨readyView, ?_, by trivial, by trivial, vacant, unused⟩
          change (match middle.application.activatedAt event with
            | none => False
            | some entered => middle.application.clock - entered <
                (serviceRuntime setup mode deadline).deadline event)
          rw [activated]
          exact inTime
        · change (app.packet (app.submit middle.application actor _) actor
            (middle.network.known actor) _).token = some ⟨event⟩
          rw [reactiveApplication_packet_token]
          exact PublicView.tokenFor_of_eventReady _ _ event rfl readyView
      · rw [decided]
        unfold RealizesAt
        rw [node]
        refine ⟨(actor, .prepared serial), rfl, ?_, ?_⟩
        · change (submitStep _ actor
            (.commitment event (actor, .prepared serial))).candidates.lookup
              (actor, .prepared serial) ≠ .fresh
          simp only [submitStep, ↓reduceIte]
          exact CommitmentCandidates.lookup_freeze_ne_fresh _ _
        · rw [reactiveBinding_result (serviceRuntime setup mode deadline) leaks actor event payload
                  choice serial middle fresh, cast_cast, cast_eq]
  | resolve actor payload binding checks outputEq codeEq =>
      intro effective loud
      have actorEq : actor = owner :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      have isTrue : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) =
          true := by
        cases disclose : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool)
        · exact (loud disclose).elim
        · rfl
      obtain ⟨value, resolved⟩ := effective isTrue
      have stored := EventGraph.EventCode.binding_success_of_resolve_success binding checks true
        middle.application.config.store value resolved
      obtain ⟨handle, associated, handleOwner, fixed⟩ :=
        facts.binding.success_provenance binding value stored
      have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm) true := by
        rw [← isTrue, cast_cast, cast_eq]
      subst actionEq
      have decision :=
          ((serviceRuntime setup mode deadline).canonicalServiceDecision_eq_of_not_bind leaks actor
              (middle.recall actor) (middle.observe app actor) event _
              (fun _ _ _ _ bind => by rw [node] at bind; cases bind)).trans
          ((serviceRuntime setup mode deadline).serviceDecision_successful_opening leaks middle
              facts.inputs actor event payload binding checks outputEq codeEq node handle value
              associated handleOwner fixed resolved)
      change response = _ at decision
      let material : app.Submission :=
        (disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive actor
          (app.observePlayer middle.application actor) (middle.network.known actor)
      have packetEq : app.packet (app.submit middle.application actor material) actor
          (middle.network.known actor) material =
            ⟨.opening event handle ⟨payload, value⟩, some ⟨handle, ⟨payload, value⟩⟩,
              middle.application.publicView.tokenFor (.opening event handle ⟨payload, value⟩)⟩ := by
        have emitted := WitnessedSubmission.normalizeReactive_emit
            (serviceRuntime setup mode deadline) leaks middle.application actor
            (middle.network.known actor)
            (disclosureSubmission (.opening event handle ⟨payload, value⟩))
        have packet := (serviceRuntime setup mode deadline).windowOpening_packet leaks actor event
            handle ⟨payload, value⟩ middle.application (middle.network.known actor)
            handleOwner fixed
        exact emitted.trans packet
      refine ⟨material, decision, fun fits => ?_, ?_⟩
      · have inTime := deadlineOf fits
        refine ⟨⟨material, congrArg ReactiveApplication.Action.transmission decision⟩, rfl, rfl,
          by rw [packetEq]; rfl, readyView, fitsViewOf fits, ?_⟩
        change (serviceRuntime setup mode deadline).freshServiceAcceptable
            middle.application.publicView
            ⟨(actor, middle.network.nextSerial actor), app.packet
                (app.submit middle.application actor material) actor (middle.network.known actor)
                material⟩
        rw [packetEq]
        apply ((serviceRuntime setup mode deadline).freshServiceEnvelope_opening_iff
                middle.application.publicView (actor, middle.network.nextSerial actor) event actor
                payload binding checks outputEq codeEq node handle ⟨payload, value⟩
                (some ⟨handle, ⟨payload, value⟩⟩) _).mpr
        refine ⟨readyView, ?_, by simp only [certifiedOpening, decide_true], ?_, rfl, handleOwner,
          associated, rfl, PublicView.tokenFor_of_eventReady _ _ event rfl readyView⟩
        · change (match middle.application.activatedAt event with
            | none => False
            | some entered => middle.application.clock - entered <
                (serviceRuntime setup mode deadline).deadline event)
          rw [activated]
          exact inTime
        · apply (middle.application.publicView.openingGuardsAccepted_iff actor event payload
            binding checks outputEq codeEq node handle ⟨payload, value⟩ _).mpr
          refine ⟨value, rfl, ?_⟩
          change EventGraph.GuardCheck.allAccepted? checks
            ((serviceGraph setup mode).publicStore middle.application.config.store)
            (.success value) = some true
          rw [EventGraph.GuardCheck.allAccepted?_publicStore]
          exact EventGraph.EventCode.guards_pass_of_resolve_success binding checks true
            middle.application.config.store value resolved
      · rw [decision]
        unfold RealizesAt
        rw [node]
        refine ⟨isTrue, handle, value, by rw [packetEq], handleOwner, associated, ?_, stored,
          ⟨_, resolved⟩⟩
        rw [respond_candidate_fixed setup leaks middle actor _ handle (by rw [fixed]; simp)]
        exact fixed

end FirstTurn

section Turns

variable {setup leaks}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- An element in the middle of a list is the element at the length of its
prefix, and the prefix is the list's take. -/
theorem split_take {α : Type} {list before after : List α} {entry : α}
    (split : list = before ++ entry :: after) :
    before = list.take before.length ∧
      ∃ bound : before.length < list.length, list[before.length] = entry := by
  subst split
  refine ⟨by simp, by simp, by simp⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A split of a list extended by one element is a split of the old list or
ends at the new element. -/
theorem split_snoc {α : Type} {old before after : List α} {entry last : α}
    (split : before ++ entry :: after = old ++ [last]) :
    (before = old ∧ entry = last ∧ after = []) ∨
      ∃ rest, after = rest ++ [last] ∧ before ++ entry :: rest = old := by
  rcases List.eq_nil_or_concat after with empty | ⟨rest, final, rfl⟩
  · subst empty
    have := List.append_inj' split rfl
    left
    exact ⟨this.1, List.singleton_inj.mp this.2, rfl⟩
  · right
    have joined : (before ++ entry :: rest) ++ [final] = old ++ [last] := by
      simpa using split
    have := List.append_inj' joined rfl
    exact ⟨rest, by rw [List.singleton_inj.mp this.2, List.concat_eq_append], this.1⟩

/-- Public readiness, and hence the own turn, is read from the completion
identities alone. -/
theorem ownTurn?_congr {left right : PublicView (serviceGraph setup mode)}
    (same : left.observation = right.observation) (who : Player) :
    left.ownTurn? who = right.ownTurn? who := by
  simp only [PublicView.ownTurn?, PublicView.EventReady, same]

/-- At the first turn no earlier recorded response saw the event as the
player's turn. -/
theorem sourceServiceTurn_first {owner : Player} {event : (serviceGraph setup mode).EventId}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    (first : serviceTurn setup mode deadline leaks owner event past view = some 0) :
    view.application.publicView.ownTurn? owner = some event ∧
      ∀ entry ∈ past, entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
  unfold serviceTurn at first
  split at first
  · rename_i turn
    have counted := Option.some.inj first
    rw [List.countP_eq_zero] at counted
    exact ⟨turn, fun entry member equal => counted entry member (decide_eq_true equal)⟩
  · cases first

/-- The first entry of a recall that saw the event as its player's turn is at
turn index zero. -/
theorem exists_first_turn {owner : Player} {event : (serviceGraph setup mode).EventId}
    (entries : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (seen : ∃ entry ∈ entries,
      entry.beforeView.application.publicView.ownTurn? owner = some event) :
    ∃ before entry after, entries = before ++ entry :: after ∧
      serviceTurn setup mode deadline leaks owner event before entry.beforeView = some 0 := by
  induction entries using List.reverseRecOn with
  | nil => obtain ⟨_, member, _⟩ := seen; cases member
  | append_singleton rest last ih =>
      by_cases earlier : ∃ entry ∈ rest,
          entry.beforeView.application.publicView.ownTurn? owner = some event
      · obtain ⟨before, entry, after, split, first⟩ := ih earlier
        exact ⟨before, entry, after ++ [last], by rw [split]; simp, first⟩
      · obtain ⟨entry, member, turn⟩ := seen
        have isLast : entry = last := by
          rcases List.mem_append.mp member with prior | final
          · exact (earlier ⟨entry, prior, turn⟩).elim
          · exact List.mem_singleton.mp final
        subst isLast
        refine ⟨rest, entry, [], by simp, ?_⟩
        unfold serviceTurn
        simp only [turn, ↓reduceIte, Option.some.injEq]
        rw [List.countP_eq_zero]
        intro other member chosen
        exact earlier ⟨other, member, of_decide_eq_true chosen⟩

/-- Deciding at the first turn submits a fresh packet only there, only before
the event is recorded, and then it is the compiled decision. -/
theorem decidedTurnPolicy_submission {bound : (serviceGraph setup mode).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    {action : (serviceGraph setup mode).Action event}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {response : (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈ (decidedTurnPolicy setup leaks bound owner event action past view).support)
    {other : (serviceGraph setup mode).EventId}
    (submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks response = some other) :
    serviceTurn setup mode deadline leaks owner event past view = some 0 ∧
    (serviceRuntime setup mode deadline).eventRecorded leaks past event = false ∧
      response = (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner past view
          event action := by
  have silenced : ∀ response ∈
      ((serviceApplication setup mode deadline leaks).silentPolicy past view).support,
      (serviceRuntime setup mode deadline).submittedEvent? leaks response = none := by
    intro response member
    obtain rfl := (serviceApplication setup mode deadline leaks).silentPolicy_cases past view
        response member
    rfl
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy at chosen
  dsimp only at chosen
  split at chosen
  · rename_i first
    unfold decidedOpportunity at chosen
    split at chosen
    · rw [silenced response chosen] at submitted
      cases submitted
    · rename_i unrecorded
      split at chosen
      · split at chosen
        · rw [silenced response chosen] at submitted
          cases submitted
        · rw [PMF.mem_support_pure_iff] at chosen
          exact ⟨first, by simpa using unrecorded, chosen⟩
      · rw [silenced response chosen] at submitted
        cases submitted
  · rw [silenced response chosen] at submitted
    cases submitted

/-- A disclosure of `false` is compiled to silence. -/
theorem canonicalServiceDecision_silent (who : Player)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) (silent : SilentAction event action) :
    ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view event
        action).transmission =
      none := by
  revert silent
  unfold SilentAction
  cases node : nodeView (serviceGraph setup mode) event with
  | resolve actor payload binding checks outputEq codeEq =>
      intro withheld
      obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      simp only [cast_cast, cast_eq] at withheld
      subst withheld
      simp only [EventGraphRuntime.canonicalServiceDecision,
        EventGraphRuntime.canonicalReactiveDecision, node,
        reactiveResolutionPacket, cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
        Option.map_none]
      rfl
  | bind => exact False.elim
  | sample => exact False.elim

end Turns

section Phase

variable {setup leaks}

/-- Every response extends each player's recall. -/
theorem respond_recall_prefix (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who observer : Player) (response : (serviceApplication setup mode deadline leaks).Action) :
    execution.recall observer <+:
      (execution.respond (serviceApplication setup mode deadline leaks) who response).recall
      observer := by
  by_cases same : observer = who
  · subst observer
    obtain ⟨_, recalled, _⟩ := respond_recall_self setup leaks execution who response
    rw [recalled]
    exact List.prefix_append _ _
  · rw [(serviceApplication setup mode deadline leaks).respond_recall_other execution who observer
            same response]

/-- The owner decides `action` at the first turn at `event`; everyone else
is silent. -/
def decidedProfile (bound : (serviceGraph setup mode).EventId → Nat) (owner : Player)
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event) :
    Player → (serviceApplication setup mode deadline leaks).Policy :=
  Function.update (fun _ => (serviceApplication setup mode deadline leaks).silentPolicy) owner
    (decidedTurnPolicy setup leaks bound owner event action)

variable (leaks) in
theorem decidedProfile_submitsAtTurn (bound : (serviceGraph setup mode).EventId → Nat)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (action : (serviceGraph setup mode).Action event) (who : Player) :
    SubmitsAtTurn setup leaks (decidedProfile (deadline := deadline) (leaks := leaks) bound owner
      event action who) who := by
  by_cases same : who = owner
  · subst who
    simp only [decidedProfile, Function.update_self]
    exact decidedTurnPolicy_submitsAtTurn setup leaks bound _ event action
  · simp only [decidedProfile, Function.update_of_ne same]
    exact silentPolicy_submitsAtTurn setup leaks who

/-- **The decided phase.** Facts of play on the support of the decided profile
since the completion boundary `start`: the owner's new responses are in the
support of its decided policy; every response submitting for the event is an
acceptable fresh call realizing the action; and every first turn at the event
submits unless the action is silence. -/
structure DecidedPhase (delay bound : (serviceGraph setup mode).EventId → Nat)
    (start : (serviceApplication setup mode deadline leaks).Execution) (owner : Player)
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop where
  recallPrefix : ∀ who, start.recall who <+: execution.recall who
  supported : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (start.recall owner).length ≤ before.length →
    entry.action ∈ (decidedTurnPolicy setup leaks bound owner event action before
      entry.beforeView).support
  submitted : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event →
    ∃ message, entry.emitted = some message ∧
      FreshCall setup leaks owner event bound entry message ∧
      RealizesAt leaks start.application.config execution.application event action entry message
  firstTurn : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (start.recall owner).length ≤ before.length →
    serviceTurn setup mode deadline leaks owner event before entry.beforeView = some 0 →
    ¬ SilentAction event action →
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event

/-- An entry of the recall at the boundary saw the event unready. -/
theorem start_entry_unready
    {start : (serviceApplication setup mode deadline leaks).Execution}
    {event : (serviceGraph setup mode).EventId} (untouched : Untouched setup leaks event start)
    {owner : Player} {entry : (serviceApplication setup mode deadline leaks).PlayerEntry}
    (member : entry ∈ start.recall owner)
    (turn : entry.beforeView.application.publicView.ownTurn? owner = some event) : False :=
    untouched owner entry member (PublicView.ownTurn?_spec _ owner event turn).1

/-- At the boundary the decided phase holds trivially. -/
theorem DecidedPhase.initial (delay bound : (serviceGraph setup mode).EventId → Nat)
    {start : (serviceApplication setup mode deadline leaks).Execution} {owner : Player}
    {event : (serviceGraph setup mode).EventId} (action : (serviceGraph setup mode).Action event)
    (untouched : Untouched setup leaks event start)
    (submissions : OwnSubmissionsAtTurn setup leaks start owner) :
    DecidedPhase delay bound start owner event action start := by
  have tooLong : ∀ before entry after, start.recall owner = before ++ entry :: after →
      (start.recall owner).length ≤ before.length → False := by
    intro before entry after split long
    have := congrArg List.length split
    simp only [List.length_append, List.length_cons] at this
    omega
  refine ⟨fun _ => List.prefix_refl _, fun before entry after split long =>
    (tooLong before entry after split long).elim, ?_, fun before entry after split long =>
    (tooLong before entry after split long).elim⟩
  intro before entry after split submitted
  have member : entry ∈ start.recall owner := by rw [split]; simp
  exact (start_entry_unready untouched member
    (submissions entry member event submitted)).elim

/-- A position before the boundary's recall length lies in that recall. -/
theorem mem_start_of_short
    {start execution : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    (prefixOf : start <+: execution)
    {before after : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {entry : (serviceApplication setup mode deadline leaks).PlayerEntry}
    (split : execution = before ++ entry :: after) (short : before.length < start.length) :
    entry ∈ start := by
  obtain ⟨rest, rfl⟩ := prefixOf
  obtain ⟨_, bound, entryAt⟩ := split_take split
  rw [← entryAt, List.getElem_append_left short]
  exact List.getElem_mem _

/-- The opportunity requirement: an owner whose ready event's deadline is
past its reaction bound has had a turn there. -/
theorem opportunity_turn {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound) {remaining : Nat}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution) {owner : Player}
    {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event) (entered : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (late : entered + delay event < execution.application.clock) : ∃ entry ∈ execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨scheduled, member, activate, _, seenReady⟩ := contract.opportunity _ trace event owner
    entered owned ((execution.application.publicView_eventReady event).mpr ready) activated late
  obtain ⟨answer, answerMember, viewEq⟩ := answered scheduled member owner activate
  have seen : answer.beforeView.application.publicView.EventReady event := by
    rw [viewEq]
    exact seenReady
  exact ⟨answer, answerMember, ownTurn?_of_entry_ready setup leaks execution facts.eventStable
    owner answer answerMember event owned seen ready⟩

end Phase

section Preservation

variable {setup leaks}

/-- At a first turn of the owner, the event became ready at most `delay`
slots ago. -/
theorem first_turn_early {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound) {remaining : Nat}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution) {owner : Player}
    {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    (first : serviceTurn setup mode deadline leaks owner event (execution.recall owner) view = some
        0) : ∃ entered, execution.application.activatedAt event = some entered ∧
      execution.application.clock ≤ entered + delay event := by
  obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler trace).1
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready
    (by rw [owned]; rfl)
  refine ⟨entered, activated, ?_⟩
  by_contra late
  obtain ⟨answer, member, turn⟩ := opportunity_turn contract trace answered owned ready entered
    activated (by omega)
  exact (sourceServiceTurn_first first).2 answer member turn

/-- A response that names the owner's own fresh submission. -/
theorem submittedEvent_submit
    (material : (serviceApplication setup mode deadline leaks).Submission) :
    (serviceRuntime setup mode deadline).submittedEvent? leaks ⟨some material⟩ =
    material.call.packet.event? (serviceGraph setup mode) := rfl

/-- **The decided phase is preserved** by every round before completion. -/
theorem DecidedPhase.round {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) {remaining : Nat}
    {start execution next : (serviceApplication setup mode deadline leaks).Execution}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    {action : (serviceGraph setup mode).Action event}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (phase : DecidedPhase delay bound start owner event action execution)
    (submissions : OwnSubmissionsAtTurn setup leaks execution owner)
    (answered : ActivationsAnswered setup leaks execution)
    (same : execution.application.config = start.application.config)
    (ready : start.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (effective : EffectiveAction start.application.config event action)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (follows : players owner = decidedTurnPolicy setup leaks bound owner event action)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
        execution).support) :
    DecidedPhase delay bound start owner event action next := by
  let app := serviceApplication setup mode deadline leaks
  have readyNow : execution.application.config.cut.Ready event := by rw [same]; exact ready
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  rcases cases with ⟨_, rfl⟩ | ⟨who, active, response, chosen, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro who
      rw [recallEq]
      exact phase.recallPrefix who
    · rw [recallEq]
      exact phase.supported
    · intro before entry after split submitted
      rw [recallEq] at split
      obtain ⟨message, emitted, call, realized⟩ :=
        phase.submitted before entry after split submitted
      exact ⟨message, emitted, call, realized.round reached⟩
    · rw [recallEq]
      exact phase.firstTurn
  have activate : command = .activate who := by
    cases command with
    | activate actor => cases active; rfl
    | «include» => cases active
    | application => cases active
    | wait => cases active
  subst activate
  have sameApp := activation_application setup leaks execution middle who moved
  have prefixNext : ∀ player, execution.recall player <+:
      (middle.respond app who response).recall player := by
    intro player
    have extended := respond_recall_prefix middle who player response
    rw [recallEq] at extended
    exact extended
  by_cases isOwner : who = owner
  swap
  · have ownerRecall : (middle.respond app who response).recall owner = execution.recall owner := by
      rw [app.respond_recall_other middle who owner (Ne.symm isOwner) response, recallEq]
    refine ⟨fun player => (phase.recallPrefix player).trans (prefixNext player), ?_, ?_, ?_⟩
    · rw [ownerRecall]
      exact phase.supported
    · intro before entry after split submitted
      rw [ownerRecall] at split
      obtain ⟨message, emitted, call, realized⟩ :=
        phase.submitted before entry after split submitted
      exact ⟨message, emitted, call, realized.round reached⟩
    · rw [ownerRecall]
      exact phase.firstTurn
  subst isOwner
  rw [follows] at chosen
  rw [recallEq] at chosen
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon scheduler
      remaining execution middle (.activate who) trace selected moved
  have readyMiddle : middle.application.config.cut.Ready event := by rw [sameApp]; exact readyNow
  have effectiveMiddle : EffectiveAction middle.application.config event action := by
    rw [sameApp, same]
    exact effective
  -- The first-turn decision, when the owner's input is its first turn.
  have firstDecision (first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (middle.observe app who) = some 0) (loud : ¬ SilentAction event action) :=
    let early := first_turn_early contract trace answered owned readyNow first
    canonicalServiceDecision_submits (bound := bound) middleTrace event owned readyMiddle
      early.choose (by rw [sameApp]; exact early.choose_spec.1) action effectiveMiddle loud
  have firstFits (first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (middle.observe app who) = some 0) :
      middle.application.clock -
          (first_turn_early contract trace answered owned readyNow first).choose +
        bound event < (serviceRuntime setup mode deadline).deadline event := by
    have early := (first_turn_early contract trace answered owned readyNow first).choose_spec.2
    have bounded := timely event (by rw [owned]; rfl)
    rw [sameApp]
    omega
  have fitsFirst (first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (middle.observe app who) = some 0) :
      PublicView.InclusionFitsDeadline (serviceRuntime setup mode deadline) bound
        (middle.observe app who).application.publicView event := by
    obtain ⟨entered, activated, early⟩ :=
      first_turn_early contract trace answered owned readyNow first
    have bounded := timely event (by rw [owned]; rfl)
    unfold PublicView.InclusionFitsDeadline
    change (match middle.application.activatedAt event with
      | none => False
      | some entered => middle.application.clock - entered + bound event <
          (serviceRuntime setup mode deadline).deadline event)
    rw [sameApp, activated]
    change execution.application.clock - entered + bound event <
        (serviceRuntime setup mode deadline).deadline event
    omega
  have unrecorded (first : serviceTurn setup mode deadline leaks who event (execution.recall who)
      (middle.observe app who) = some 0) :
      (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall who) event =
      false := by
    cases recorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (execution.recall who) event
    · rfl
    · unfold EventGraphRuntime.eventRecorded at recorded
      obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
      exact ((sourceServiceTurn_first first).2 entry member
        (submissions entry member event (of_decide_eq_true submitted))).elim
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
  rw [recallEq] at recalled
  refine ⟨fun player => (phase.recallPrefix player).trans (prefixNext player), ?_, ?_, ?_⟩
  · intro before entry after split long
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      exact chosen
    · exact phase.supported before entry rest oldSplit.symm long
  · intro before entry after split submitted
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      obtain ⟨first, _, decided⟩ := decidedTurnPolicy_submission chosen submitted
      have loud : ¬ SilentAction event action := by
        intro silent
        have quiet := canonicalServiceDecision_silent (leaks := leaks) who (execution.recall who)
          (middle.observe app who) event action silent
        rw [← decided] at quiet
        change (serviceRuntime setup mode deadline).submittedEvent? leaks ⟨response.transmission⟩ =
            _ at submitted
        rw [quiet] at submitted
        cases submitted
      obtain ⟨material, decision, callOf, realized⟩ := firstDecision first loud
      have call := callOf (firstFits first)
      rw [recallEq] at decision call realized
      have responseEq : response = ⟨some material⟩ := decided.trans decision
      subst responseEq
      have submitRecall := respond_submit_recall middle who material
      rw [recallEq, recalled] at submitRecall
      have lastEq := List.append_cancel_left submitRecall
      simp only [List.cons.injEq, and_true] at lastEq
      rw [lastEq]
      rw [decision] at call realized
      refine ⟨_, rfl, call, ?_⟩
      rw [sameApp, same] at realized
      exact realized
    · obtain ⟨message, emittedOld, call, realized⟩ :=
        phase.submitted before entry rest oldSplit.symm submitted
      exact ⟨message, emittedOld, call, realized.round reached⟩
  · intro before entry after split long first loud
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      obtain ⟨material, decision, callOf, _⟩ := firstDecision first loud
      have call := callOf (firstFits first)
      rw [recallEq] at decision call
      have opening := (serviceApplication setup mode deadline leaks).turnScheduledPolicy_selected
        (serviceTurn setup mode deadline leaks who event) (0 : Fin 1)
        (decidedOpportunity setup leaks bound who event action)
        (serviceApplication setup mode deadline leaks).silentPolicy
        (execution.recall who) (middle.observe app who) first
      change decidedTurnPolicy setup leaks bound who event action (execution.recall who)
        (middle.observe app who) = _ at opening
      rw [opening] at chosen
      unfold decidedOpportunity at chosen
      simp only [unrecorded first, fitsFirst first, Bool.false_eq_true, ↓reduceIte] at chosen
      rw [decision] at chosen
      simp only [reduceCtorEq, ↓reduceIte, PMF.mem_support_pure_iff] at chosen
      rw [chosen, submittedEvent_submit]
      exact call.addressed
    · exact phase.firstTurn before entry rest oldSplit.symm long first loud

end Preservation

section Completing

variable {setup leaks}

/-- Steps from equal configurations have the same support. -/
theorem mem_step_of_eq {first second : (serviceGraph setup mode).Config} (same : first = second)
    {event : (serviceGraph setup mode).EventId} (firstReady : first.cut.Ready event)
    (secondReady : second.cut.Ready event) {action : (serviceGraph setup mode).Action event}
    {next : (serviceGraph setup mode).Config}
    (member : next ∈ (first.step event firstReady action).support) :
    next ∈ (second.step event secondReady action).support := by
  subst same
  exact member

/-- Silence is completed by expiry. -/
private theorem silent_expiry {event : (serviceGraph setup mode).EventId}
    {action : (serviceGraph setup mode).Action event}
    (silent : SilentAction event action) : ExpiryAction event action := by
  revert silent
  unfold SilentAction ExpiryAction
  cases nodeView (serviceGraph setup mode) event with
  | resolve => exact id
  | bind => exact False.elim
  | sample => exact False.elim

/-- A fresh submission's packet carries the submission's event. -/
theorem issued_submittedEvent {entry : (serviceApplication setup mode deadline leaks).PlayerEntry}
    {material : (serviceApplication setup mode deadline leaks).Submission}
    (transmission : entry.action.transmission = some material)
    {state : EventGraphRuntime.State (serviceGraph setup mode)} {who : Player}
    {known : List (Message Player (WitnessedPacket (serviceGraph setup mode)))}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (packet : (serviceApplication setup mode deadline leaks).packet state who known material =
        message.payload) :
    (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action =
      message.payload.call.event? (serviceGraph setup mode) := by
  unfold EventGraphRuntime.submittedEvent?
  rw [transmission, ← packet]
  rfl

/-- At most one response of the decided phase submits for the event. -/
theorem DecidedPhase.fresh_unique {delay bound : (serviceGraph setup mode).EventId → Nat}
    {start execution : (serviceApplication setup mode deadline leaks).Execution} {owner : Player}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    (phase : DecidedPhase delay bound start owner event action execution)
    (submissions : OwnSubmissionsAtTurn setup leaks execution owner)
    (untouched : Untouched setup leaks event start)
    {before after before' after' : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {entry entry' : (serviceApplication setup mode deadline leaks).PlayerEntry}
    (split : execution.recall owner = before ++ entry :: after)
    (split' : execution.recall owner = before' ++ entry' :: after')
    (submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action =
        some event)
    (submitted' : (serviceRuntime setup mode deadline).submittedEvent? leaks entry'.action =
        some event) :
    before.length = before'.length := by
  have turnOf : ∀ {b e a}, execution.recall owner = b ++ e :: a →
      (serviceRuntime setup mode deadline).submittedEvent? leaks e.action = some event →
      e.beforeView.application.publicView.ownTurn? owner = some event ∧
        serviceTurn setup mode deadline leaks owner event b e.beforeView = some 0 := by
    intro b e a s submittedHere
    have member : e ∈ execution.recall owner := by rw [s]; simp
    have turn := submissions e member event submittedHere
    refine ⟨turn, ?_⟩
    have long : (start.recall owner).length ≤ b.length := by
      by_contra short
      exact start_entry_unready untouched
        (mem_start_of_short (phase.recallPrefix owner) s (by omega)) turn
    exact (decidedTurnPolicy_submission (phase.supported b e a s long) submittedHere).1
  have earlier : ∀ {b e a b' e' a'}, execution.recall owner = b ++ e :: a →
      execution.recall owner = b' ++ e' :: a' →
      (serviceRuntime setup mode deadline).submittedEvent? leaks e.action = some event →
      (serviceRuntime setup mode deadline).submittedEvent? leaks e'.action = some event →
      ¬ b.length < b'.length := by
    intro b e a b' e' a' s s' sub sub' less
    obtain ⟨_, bound, entryAt⟩ := split_take s
    obtain ⟨takeEq, _, _⟩ := split_take s'
    have member : e ∈ b' := by
      rw [takeEq, ← entryAt]
      exact List.mem_iff_getElem.mpr ⟨b.length, by simp; omega, by simp⟩
    exact (sourceServiceTurn_first (turnOf s' sub').2).2 e member (turnOf s sub).1
  rcases Nat.lt_trichotomy before.length before'.length with less | equal | greater
  · exact (earlier split split' submitted submitted' less).elim
  · exact equal
  · exact (earlier split' split submitted' submitted greater).elim

/-- **The completing round.** A round of the decided phase that changes the
configuration completes the event with the decided action, when no other event
is ever ready together with it. -/
theorem DecidedPhase.complete_round {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {remaining : Nat}
    {start execution next : (serviceApplication setup mode deadline leaks).Execution}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    {action : (serviceGraph setup mode).Action event}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (phase : DecidedPhase delay bound start owner event action execution)
    (submissions : OwnSubmissionsAtTurn setup leaks execution owner)
    (answered : ActivationsAnswered setup leaks execution)
    (untouched : Untouched setup leaks event start)
    (same : execution.application.config = start.application.config)
    (ready : start.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut)
      (other : (serviceGraph setup mode).EventId), cut.Ready event → cut.Ready other →
      other = event)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players execution).support)
    (changed : next.application.config ≠ start.application.config) :
    next.application.config ∈ (start.application.config.step event ready action).support := by
  let app := serviceApplication setup mode deadline leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have readyNow : execution.application.config.cut.Ready event := by rw [same]; exact ready
  have unfinished : event ∉ execution.application.config.cut.completed := readyNow.1
  have soleOf (other : (serviceGraph setup mode).EventId)
      (otherReady : execution.application.config.cut.Ready other) : other = event :=
    alone _ other readyNow otherReady
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have configNext : next.application.config = middle.application.config := by
    rcases cases with ⟨_, rfl⟩ | ⟨who, _, response, _, rfl⟩
    · rfl
    · exact
          ((serviceRuntime setup mode deadline).reactive_respond_application leaks middle who
              response).1
  rw [configNext] at changed ⊢
  rw [← same] at changed
  cases command with
  | activate who =>
      rw [activation_application setup leaks execution middle who moved] at changed
      exact (changed rfl).elim
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact (changed rfl).elim
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending at changed ⊢
      cases found : execution.network.lookup id with
      | none =>
          simp only [found] at changed
          exact (changed rfl).elim
      | some message =>
          simp only [found] at changed ⊢
          cases reactiveAccepted : (serviceApplication setup mode deadline leaks).handle
              execution.application
              message with
          | none =>
              rw [reactiveAccepted] at changed
              exact (changed rfl).elim
          | some state =>
              have accepted := reactiveHandle_call reactiveAccepted
              change state.config ∈ _
              obtain ⟨named, namedEq, namedReady, _, _⟩ :=
                handle_config_mem_step (serviceRuntime setup mode deadline) _ _ _ accepted
              have namedIs := soleOf named namedReady
              subst namedIs
              have sender := handle_sender_actor (serviceRuntime setup mode deadline) _ _ _ accepted
                  named namedEq
              have senderEq : message.sender = owner :=
                Option.some.inj (sender.symm.trans owned)
              obtain ⟨entry, member, material, transmission, emittedEq, _, _, packet⟩ :=
                facts.provenance.pending message (List.mem_of_find?_eq_some found)
              rw [senderEq] at member
              have submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks
                  entry.action = some named := by
                rw [issued_submittedEvent transmission packet]
                exact namedEq
              obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
              obtain ⟨packetMessage, emittedP, call, realized⟩ :=
                phase.submitted before entry after split submitted
              rw [emittedEq] at emittedP
              cases Option.some.inj emittedP
              exact include_realized execution facts.eventStable start.application.config same named
                ready owner owned action entry member call.ready message senderEq realized state
                accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, stepped, rfl⟩ := PMF.support_map .. ▸ supported
      change state.config ≠ _ at changed
      change state.config ∈ _
      change state ∈
          (environmentStep (serviceRuntime setup mode deadline) execution.application
              command).support at stepped
      cases command with
      | advanceClock =>
          simp only [environmentStep, PMF.mem_support_pure_iff] at stepped
          subst stepped
          exact (changed rfl).elim
      | executeSample other =>
          by_cases otherReady : execution.application.config.cut.Ready other
          · have otherIs := soleOf other otherReady
            subst otherIs
            rw [environmentStep_executeSample_of_nonsample _ _ _ otherReady (by
              intro payload law outputEq codeEq viewEq
              have none := nodeView_sample_actor outputEq codeEq
              rw [owned] at none
              cases none), PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim
          · rw [environmentStep_executeSample_of_not_ready _ _ _ otherReady,
              PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim
      | expire other =>
          by_cases otherReady : execution.application.config.cut.Ready other
          · have otherIs := soleOf other otherReady
            subst otherIs
            obtain ⟨⟨entered, activated, late⟩, finish⟩ :=
              expire_completion _ _ other readyNow stepped changed
            by_cases expiring : ExpiryAction other action
            · exact mem_step_of_eq same readyNow ready (finish action expiring)
            · exfalso
              have loud : ¬ SilentAction other action :=
                fun silent => expiring (silent_expiry silent)
              have bounded := timely other (by rw [owned]; rfl)
              obtain ⟨turnEntry, turnMember, turn⟩ := opportunity_turn contract trace answered
                owned readyNow entered activated (by omega)
              obtain ⟨before, first, after, split, firstTurn⟩ :=
                exists_first_turn (execution.recall owner) ⟨turnEntry, turnMember, turn⟩
              have long : (start.recall owner).length ≤ before.length := by
                by_contra short
                exact start_entry_unready untouched
                  (mem_start_of_short (phase.recallPrefix owner) split (by omega))
                  (sourceServiceTurn_first firstTurn).1
              have submittedFirst := phase.firstTurn before first after split long firstTurn loud
              obtain ⟨packet, emittedFirst, call, _⟩ :=
                phase.submitted before first after split submittedFirst
              have firstMember : first ∈ execution.recall owner := by rw [split]; simp
              have sole : ∀ other' ∈ before ++ after,
                  ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other' other
                      packet.id := by
                intro other' otherMember ⟨otherEnvelope, emittedOther, _, addressed, different⟩
                have otherRecall : other' ∈ execution.recall owner := by
                  rw [split]
                  rcases List.mem_append.mp otherMember with left | right
                  · exact List.mem_append_left _ left
                  · exact List.mem_append_right _ (List.mem_cons_of_mem _ right)
                have output : otherEnvelope ∈ app.outputs (execution.recall owner) :=
                  List.mem_filterMap.mpr ⟨other', otherRecall, emittedOther⟩
                rw [← facts.inputs owner] at output
                have inputMember := (List.mem_filter.mp output).1
                have issuerOwner : otherEnvelope.sender = owner :=
                  of_decide_eq_true (List.mem_filter.mp output).2
                obtain ⟨issuer, issuerMember, material, transmission, issuerEmitted, _, _,
                  issuerPacket⟩ := facts.provenance.inputs otherEnvelope inputMember
                have issuerSubmitted : (serviceRuntime setup mode deadline).submittedEvent? leaks
                    issuer.action =
                    some other := by
                  rw [issued_submittedEvent transmission issuerPacket]
                  exact addressed
                rw [issuerOwner] at issuerMember
                obtain ⟨issuerBefore, issuerAfter, issuerSplit⟩ :=
                  List.mem_iff_append.mp issuerMember
                have lengths := phase.fresh_unique submissions untouched issuerSplit split
                  issuerSubmitted submittedFirst
                obtain ⟨_, _, issuerAt⟩ := split_take issuerSplit
                obtain ⟨_, _, firstAt⟩ := split_take split
                have sameEntry : issuer = first := by
                  rw [← issuerAt, ← firstAt]
                  simp only [lengths]
                rw [sameEntry, emittedFirst] at issuerEmitted
                exact different (by rw [Option.some.inj issuerEmitted])
              have settled := settlesFreshCalls_history setup leaks contract.inclusion
                  owner other owned trace before first after packet split call sole
              obtain ⟨enteredThen, activatedThen, early⟩ := call.fits.exists
              have kept := (facts.eventStable owner first firstMember other call.ready
                unfinished).choose_spec.2.2.1 owner owned enteredThen activatedThen
              rw [activated, Option.some.injEq] at kept
              subst kept
              have receipt :=
                  (prescribed_packet_settles setup leaks contract.inclusion trace other
                      owner owned before after first packet split call sole).1
                  (by change _ < execution.application.clock; omega)
              exact unfinished (settled.2.2 receipt)
          · rw [environmentStep_expire_of_not_ready _ _ _ otherReady,
              PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim

end Completing

section Run

variable {setup leaks}

/-- Along the decided run every point keeps the boundary configuration or has
completed the event with the decided action. -/
theorem DecidedPhase.runUntil {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {start : (serviceApplication setup mode deadline leaks).Execution} {owner : Player}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    (untouched : Untouched setup leaks event start)
    (ready : start.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut)
      (other : (serviceGraph setup mode).EventId), cut.Ready event → cut.Ready other →
        other = event)
    (effective : EffectiveAction start.application.config event action)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (follows : players owner = decidedTurnPolicy setup leaks bound owner event action) : ∀
    (count remaining : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution),
    ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode) horizon
        scheduler).Trace (some ⟨remaining + count, none, execution⟩) → DecidedPhase delay bound
    start owner event action execution → OwnSubmissionsAtTurn setup leaks execution owner →
    ActivationsAnswered setup leaks execution → execution.application.config =
    start.application.config → ∀ stopped ∈
    ((serviceApplication setup mode deadline leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).support,
    stopped.application.config = start.application.config ∨ stopped.application.config ∈
    (start.application.config.step event ready action).support
  := by
  let app := serviceApplication setup mode deadline leaks
  intro count
  induction count with
  | zero =>
      intro remaining execution _ _ _ _ same stopped reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact Or.inl same
  | succ count ih =>
      intro remaining execution trace phase submissions answered same stopped reached
      by_cases halt : event ∈ execution.application.config.cut.completed
      · rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ execution halt] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact Or.inl same
      · simp only [ReactiveApplication.runUntil, halt, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        obtain ⟨middleTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon scheduler
          players (remaining + count) execution middle trace moved
        have atTurn : SubmitsAtTurn setup leaks (players owner) owner := by
          rw [follows]
          exact decidedTurnPolicy_submitsAtTurn setup leaks bound owner event action
        have submissions' := round_ownSubmissionsAtTurn setup leaks atTurn submissions moved
        have answered' := round_activationsAnswered setup leaks answered moved
        by_cases unchanged : middle.application.config = start.application.config
        · exact ih remaining middle middleTrace
            (phase.round (remaining := remaining + count) contract timely trace submissions
              answered same ready owned effective follows moved) submissions' answered' unchanged
              stopped
            rest
        · have completed := phase.complete_round (remaining := remaining + count) contract timely
            trace submissions answered untouched same ready owned alone moved
            unchanged
          have finished : event ∈ middle.application.config.cut.completed := by
            rw [start.application.config.step_cut event ready action _ completed,
              EventOrder.Cut.mem_complete]
            exact Or.inl rfl
          rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ middle finished] at rest
          cases (PMF.mem_support_pure_iff _ _).mp rest
          exact Or.inr completed

/-- Under complete play, a completion run of any players from an execution on
a legal history stops only once the event has completed. -/
theorem runUntilHorizon_completes {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (complete : CompletesPlay (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {event : (serviceGraph setup mode).EventId}
    {start : (serviceApplication setup mode deadline leaks).Execution}
    (bounded : start.environmentRecall.length ≤ horizon)
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨horizon - start.environmentRecall.length, none, start⟩))
    (stopped : (serviceApplication setup mode deadline leaks).Execution)
    (reached : stopped ∈
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
    event ∈ stopped.application.config.cut.completed := by
  let app := serviceApplication setup mode deadline leaks
  rcases app.runUntilHorizon_stopped scheduler _ _ horizon
      (horizon - start.environmentRecall.length) start stopped (by omega) reached with
    done | spent
  · exact done
  · obtain ⟨used, within, rounds, length⟩ := app.runUntil_runRounds scheduler _ _ _ start
      stopped reached
    obtain ⟨stoppedTrace⟩ := app.raw_trace_runRounds (serviceInitialLaw setup mode) horizon
        scheduler players 0 used start stopped
      (by
        have count : horizon - start.environmentRecall.length = 0 + used := by omega
        rw [← count]
        exact trace) rounds
    have terminal := complete _ stoppedTrace (by
      change 0 = 0 ∧ _
      exact ⟨rfl, rfl⟩)
    change stopped.application.config.cut.completed = Finset.univ at terminal
    rw [terminal]
    exact Finset.mem_univ _

/-- **Decided completion against any other players.** From a completion
boundary of any players at which the owner has submitted only at its own turns,
under the asynchronous contract with `delay + bound < deadline`, if the owner
decides an effective action at its first turn, then whatever the other players
do every stopped point has completed the event with that action. -/
theorem decided_completion_of_follows {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {reachers : Player → (serviceApplication setup mode deadline leaks).Policy}
    (event : (serviceGraph setup mode).EventId)
    (start : (serviceApplication setup mode deadline leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler reachers event.val start)
    (bounded : start.environmentRecall.length ≤ horizon)
    (ready : start.application.config.cut.Ready event)
    {owner : Player} (owned : (serviceGraph setup mode).actor? event = some owner)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut)
      (other : (serviceGraph setup mode).EventId), cut.Ready event → cut.Ready other →
        other = event)
    (ownStart : OwnSubmissionsAtTurn setup leaks start owner)
    (action : (serviceGraph setup mode).Action event)
    (effective : EffectiveAction start.application.config event action)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (follows : players owner = decidedTurnPolicy setup leaks bound owner event action)
    (stopped : (serviceApplication setup mode deadline leaks).Execution)
    (reached : stopped ∈
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
    stopped.application.config ∈ (start.application.config.step event ready action).support := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    reachers _ bounded start boundary.supported
  have answered := roundsFrom_activationsAnswered _ start boundary.supported
  have untouched := boundary.untouched event le_rfl
  have phase := DecidedPhase.initial delay bound action untouched ownStart (owner := owner)
  rcases DecidedPhase.runUntil contract timely untouched ready owned alone effective
      follows
      (horizon - start.environmentRecall.length) 0 start
      (by simpa only [Nat.zero_add] using startTrace) phase ownStart answered rfl stopped
      reached with unchanged | completed
  · exfalso
    have notDone : event ∉ stopped.application.config.cut.completed := by
      rw [unchanged]
      exact ready.1
    exact notDone (runUntilHorizon_completes contract.completes bounded startTrace stopped reached)
  · exact completed

/-- **Decided completion.** From a completion boundary of the turn-counted
policy, under the asynchronous contract with `delay + bound < deadline`, if the
owner decides an effective action at its first turn and every other response
is silent, every stopped point has completed the event with that action. -/
theorem decided_completion {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) {turns : Nat}
    {timing : TurnTiming setup turns mode} {profile : BehavioralProfile setup.program}
    (event : (serviceGraph setup mode).EventId)
    (start : (serviceApplication setup mode deadline leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) event.val start)
    (bounded : start.environmentRecall.length ≤ horizon)
    (ready : start.application.config.cut.Ready event) {owner : Player}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut)
      (other : (serviceGraph setup mode).EventId), cut.Ready event → cut.Ready other →
        other = event)
    (action : (serviceGraph setup mode).Action event)
    (effective : EffectiveAction start.application.config event action)
    (stopped : (serviceApplication setup mode deadline leaks).Execution)
    (reached : stopped ∈
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
        (decidedProfile (leaks := leaks) bound owner event action)
        (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
    stopped.application.config ∈ (start.application.config.step event ready action).support := by
  obtain ⟨submissions, _⟩ := roundsFrom_turnFacts setup leaks
    (fun who => sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns timing profile who) _
    start boundary.supported
  exact decided_completion_of_follows contract timely event start boundary bounded ready owned
    alone (submissions.own owner) action effective
    (by simp only [decidedProfile, Function.update_self]) stopped reached

end Run

end Vegas
