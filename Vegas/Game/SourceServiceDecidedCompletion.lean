/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTurnSubmissions
import Vegas.Pending.ReactiveBindingResources
import Vegas.Pending.ReactiveDisclosureStability

/-! # A fixed first-turn decision completes its event with that action

From a completion boundary of the turn-counted policy, suppose the owner of
the current event decides a fixed action at its first turn there and every
other response is silent. Under the asynchronous contract with
`delay + bound < deadline`, every stopped point has completed the event with
exactly that action (`Vegas.decided_completion`).

* The first turn comes before any expiry: an expiry needs the deadline to have
  passed, and by then the scheduler has activated the owner.
* Every owned decision submits a fresh, acceptable packet: a commitment for
  a binding, an explicit withholding for `false`, or a certified opening for
  an effective `true` disclosure. Protected inclusion accepts that packet
  before expiry and completes the event with the decided action.

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
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section Actions

variable {setup}

/-- A packet emitted by `entry` realizes `action`: accepted at a state with the
configuration `config`, the candidate meanings of `state`, and an empty
application intention table, the handler completes the event with `action`. -/
def RealizesAt (config : (graph setup).Config) (state : EventGraphRuntime.State (graph setup))
    (event : (graph setup).EventId) (action : (graph setup).Action event)
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  match nodeView (graph setup) event with
  | .bind _ payload outputEq _ =>
      ∃ handle, message.payload.call = .commitment event handle ∧
        state.candidates.lookup handle ≠ .fresh ∧
        state.bindingResult handle payload =
          cast (congrArg EventGraph.EventField.Action outputEq) action
  | .resolve owner payload binding checks outputEq _ =>
      ((cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = false ∧
        message.payload.call = .withhold event) ∨
      ((cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true ∧
      ∃ handle value, message.payload.call = .opening event handle ⟨payload, value⟩ ∧
        handle.1 = owner ∧
        entry.beforeView.application.publicView.accepted binding.field = some handle ∧
        state.candidates.lookup handle = .openable ⟨payload, value⟩ ∧
        binding.get? config.store = some (.success value) ∧
        ∃ result, EventGraph.EventCode.resolveOutput? binding checks true config.store =
          some result)
  | .sample .. => False

end Actions

section Completion

variable {setup leaks}

/-- Realization survives every round before completion: only candidate
meanings are read from the current state, and fixed meanings never change. -/
theorem RealizesAt.round {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy}
    {config : (graph setup).Config} {execution next : (application setup leaks).Execution}
    {event : (graph setup).EventId} {action : (graph setup).Action event}
    {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))}
    (realized : RealizesAt leaks config execution.application event action entry message)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support) :
    RealizesAt leaks config next.application event action entry message := by
  revert realized
  unfold RealizesAt
  cases nodeView (graph setup) event with
  | bind owner payload outputEq codeEq =>
      rintro ⟨handle, call, fixed, result⟩
      have same := round_candidate_fixed setup leaks reached handle fixed
      refine ⟨handle, call, same ▸ fixed, ?_⟩
      simp only [State.bindingResult, same] at result ⊢
      exact result
  | resolve owner payload binding checks outputEq codeEq =>
      rintro (withheld | ⟨isTrue, handle, value, call, owner', associated, fixed, rest⟩)
      · exact Or.inl withheld
      · have same := round_candidate_fixed setup leaks reached handle (by rw [fixed]; simp)
        exact Or.inr ⟨isTrue, handle, value, call, owner', associated, same.trans fixed, rest⟩
  | sample => exact id

/-- The conditions under which the handler accepts a commitment. -/
private theorem commitment_accepted_conditions (state next : EventGraphRuntime.State (graph setup))
    (id : MessageId Player) (event : (graph setup).EventId) (handle : Handle (graph setup))
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (accepted : EventGraphRuntime.handle (runtime setup) state ⟨id, .commitment event handle⟩ =
      some next) :
    state.config.cut.Ready event ∧ state.WithinDeadline (runtime setup) event ∧
      id.1 = owner ∧ handle.1 = owner ∧ state.accepted (.inr event) = none ∧
      state.HandleUnused handle := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline (runtime setup) event
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
private theorem opening_accepted_timely (state next : EventGraphRuntime.State (graph setup))
    (id : MessageId Player) (event : (graph setup).EventId) (handle : Handle (graph setup))
    (raw : Raw L) (ready : state.config.cut.Ready event)
    (accepted : EventGraphRuntime.handle (runtime setup) state
      ⟨id, .opening event handle raw⟩ = some next) :
    state.WithinDeadline (runtime setup) event := by
  by_contra late
  simp [EventGraphRuntime.handle, ready, late] at accepted

/-- **Completion through a realizing packet.** If the handler accepts a packet
that realizes `action`, the event completes with `action`. -/
theorem include_realized (execution : (application setup leaks).Execution)
    (stable : EntryStable (runtime setup) leaks execution)
    (config : (graph setup).Config) (same : execution.application.config = config)
    (event : (graph setup).EventId) (ready : config.cut.Ready event)
    (unremembered : execution.application.remembered event = none)
    (owner : Player) (owned : (graph setup).actor? event = some owner)
    (action : (graph setup).Action event) (entry : (application setup leaks).PlayerEntry)
    (member : entry ∈ execution.recall owner)
    (seen : entry.beforeView.application.publicView.EventReady event)
    (message : Message Player (WitnessedPacket (graph setup)))
    (authored : message.sender = owner)
    (realized : RealizesAt leaks config execution.application event action entry message)
    (next : EventGraphRuntime.State (graph setup))
    (accepted : EventGraphRuntime.handle (runtime setup) execution.application
      ⟨message.id, message.payload.call⟩ = some next) :
    next.config ∈ (config.step event ready action).support := by
  subst same
  revert realized
  unfold RealizesAt
  cases node : nodeView (graph setup) event with
  | bind actor payload outputEq codeEq =>
      rintro ⟨handle, call, _, result⟩
      rw [call] at accepted
      obtain ⟨_, timely, sender, handleOwner, vacant, unused⟩ :=
        commitment_accepted_conditions _ _ _ _ _ actor payload outputEq codeEq node accepted
      rw [handle_commitment_eq (runtime setup) _ _ event handle actor payload outputEq codeEq
        node ready timely sender handleOwner vacant unused, Option.some.injEq] at accepted
      subst accepted
      have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (execution.application.bindingResult handle payload) := by
        rw [result, cast_cast, cast_eq]
      rw [actionEq, Vegas.commit_step _ _ ready outputEq codeEq]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | resolve actor payload binding checks outputEq codeEq =>
      rintro (⟨isFalse, call⟩ | ⟨isTrue, handle, value, call, handleOwner, associatedThen,
        verified, stored, result, resolved⟩)
      · have actorEq : actor = owner :=
          Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
        subst actorEq
        rw [call] at accepted
        have timely : execution.application.WithinDeadline (runtime setup) event := by
          by_contra late
          simp [EventGraphRuntime.handle, ready, late] at accepted
        rw [handle_withhold_unremembered_eq (runtime setup) _ _ event actor payload binding
          checks outputEq codeEq node ready timely authored unremembered,
          Option.some.injEq] at accepted
        subst accepted
        have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
            false := by
          rw [← isFalse, cast_cast, cast_eq]
        have resolved : EventGraph.EventCode.resolveOutput? binding checks false
            execution.application.config.store = some .failure := by
          apply EventGraph.EventCode.resolveOutput?_false_eq_failure binding checks
            execution.application.config.store
          intro field member
          apply execution.application.config.read_available ready
          rw [resolution_readFields event actor payload binding checks outputEq codeEq]
          exact member
        rw [actionEq, execution.application.config.step_eq_map_of_code event ready outputEq _
          codeEq false (PMF.pure .failure)
          (by rw [EventGraph.EventCode.resolve_eval?, resolved]; rfl), PMF.pure_map]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      · have actorEq : actor = owner := by
          have actorOf := nodeView_resolve_actor outputEq codeEq
          exact Option.some.inj (actorOf.symm.trans owned)
        subst actorEq
        rw [call] at accepted
        have timely := opening_accepted_timely _ _ _ _ _ _ ready accepted
        have associated : execution.application.accepted binding.field = some handle := by
          have current := (entry_view_current setup leaks execution stable actor entry member event
            seen (fun completed => ready.1 completed)).2.1
          rw [← current]
          exact associatedThen
        rw [handle_opening_eq (runtime setup) _ _ event handle actor payload binding checks outputEq
          codeEq node ready timely authored handleOwner associated value verified stored result
          resolved, Option.some.injEq] at accepted
        subst accepted
        have actionEq : action =
            cast (congrArg EventGraph.EventField.Action outputEq.symm) true := by
          rw [← isTrue, cast_cast, cast_eq]
        rw [actionEq, execution.application.config.step_eq_map_of_code event ready outputEq _ codeEq
          true (PMF.pure result) (by rw [EventGraph.EventCode.resolve_eval?, resolved]; rfl),
          PMF.pure_map]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
  | sample => exact False.elim

/-- A strategic expiry that changes the configuration is due. -/
theorem expiry_due (state next : EventGraphRuntime.State (graph setup))
    (event : (graph setup).EventId) (ready : state.config.cut.Ready event)
    (moved : next ∈ (environmentStep (runtime setup) state (.expire event)).support)
    (changed : next.config ≠ state.config) :
    ∃ entered, state.activatedAt event = some entered ∧
      (runtime setup).deadline event ≤ state.clock - entered := by
  have due : ∃ entered, state.activatedAt event = some entered ∧
      (runtime setup).deadline event ≤ state.clock - entered := by
    cases activated : state.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated _ _ event ready activated,
          PMF.mem_support_pure_iff] at moved
        exact (changed (by rw [moved])).elim
    | some entered =>
        by_cases late : (runtime setup).deadline event ≤ state.clock - entered
        · exact ⟨entered, rfl, late⟩
        · rw [environmentStep_expire_of_not_due _ _ event ready entered activated late,
            PMF.mem_support_pure_iff] at moved
          exact (changed (by rw [moved])).elim
  exact due

end Completion

section FirstTurn

variable {setup leaks}

/-- The initial law is the image of initial inputs. -/
theorem initialLaw_eq_inputs :
    initialLaw setup =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := graph setup)) := by
  rw [PMF.map_comp]
  rfl

/-- The entry a fresh submission appends to its author's recall. -/
theorem respond_submit_recall (execution : (application setup leaks).Execution) (who : Player)
    (material : (application setup leaks).Submission) :
    (execution.respond (application setup leaks) who ⟨some material⟩).recall who =
      execution.recall who ++ [⟨execution.observe (application setup leaks) who,
        ⟨some material⟩,
        some ⟨(who, execution.network.nextSerial who), (application setup leaks).packet
          ((application setup leaks).submit execution.application who material) who
          (execution.network.known who) material⟩⟩] := by
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
  rfl

/-- **The first turn decides.** At a legal history where the owner of the
ready `event` is active within `delay event` slots of readiness, the compiled
decision for an effective action transmits a fresh call that is
acceptable on the owner's view and realizes the action. -/
theorem firstTurn_freshCall {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (timely : AsyncTimely (runtime setup) delay bound) {remaining : Nat}
    {owner : Player} {middle : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, middle⟩))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (ready : middle.application.config.cut.Ready event)
    (entered : Nat) (activated : middle.application.activatedAt event = some entered)
    (early : middle.application.clock ≤ entered + delay event)
    (action : (graph setup).Action event)
    (effective : EffectiveAction middle.application.config event action) :
    let app := application setup leaks
    let response := (runtime setup).canonicalServiceDecision leaks owner (middle.recall owner)
      (middle.observe app owner) event action
    ∃ material, response = ⟨some material⟩ ∧
      let entry : app.PlayerEntry := ⟨middle.observe app owner, response,
        some ⟨(owner, middle.network.nextSerial owner), app.packet
          (app.submit middle.application owner material) owner
          (middle.network.known owner) material⟩⟩
      let message : Message Player (WitnessedPacket (graph setup)) :=
        ⟨(owner, middle.network.nextSerial owner), app.packet
          (app.submit middle.application owner material) owner
          (middle.network.known owner) material⟩
      FreshCall setup leaks owner event bound entry message ∧
        RealizesAt leaks middle.application.config
          (middle.respond app owner response).application event action entry message := by
  intro app response
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have deadline : middle.application.clock - entered < (runtime setup).deadline event := by
    have bounded := timely event (by rw [owned]; rfl)
    omega
  have fitsView : (middle.observe app owner).application.publicView.InclusionFitsDeadline
      (runtime setup) bound event := by
    have bounded := timely event (by rw [owned]; rfl)
    unfold PublicView.InclusionFitsDeadline
    change (match middle.application.activatedAt event with
      | none => False
      | some entered => middle.application.clock - entered + bound event <
          (runtime setup).deadline event)
    rw [activated]
    change middle.application.clock - entered + bound event < (runtime setup).deadline event
    omega
  have readyView : (middle.observe app owner).application.publicView.EventReady event :=
    (middle.application.publicView_eventReady event).mpr ready
  revert effective
  unfold EffectiveAction
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | bind actor payload outputEq codeEq =>
      intro _
      have actorEq : actor = owner :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      have rawTrace := trace
      rw [initialLaw_eq_inputs] at rawTrace
      obtain ⟨least, _, leastSelected, _, _, vacant, _⟩ :=
        (runtime setup).reactiveBinding_resources_history leaks _ horizon scheduler _ rawTrace
          actor rfl event ready
      obtain ⟨serial, selected⟩ := canonicalFreshSlot_isSome actor
        (middle.observe app actor).application least leastSelected
      have fresh : middle.application.candidates.lookup (actor, .prepared serial) = .fresh :=
        canonicalFreshSlot_spec actor _ serial selected
      have valid := (runtime setup).reactiveBindingInvariant_history leaks _ horizon scheduler
        rawTrace
      have unused : middle.application.HandleUnused (actor, .prepared serial) :=
        fun field associated => valid.accepted_fixed field _ associated fresh
      have decided := (runtime setup).canonicalServiceDecision_binding leaks actor
        (middle.recall actor) (middle.observe app actor) event payload outputEq codeEq node serial
        selected choice
      change response = _ at decided
      refine ⟨_, decided, ?_, ?_⟩
      · refine ⟨⟨_, congrArg ReactiveApplication.Action.transmission decided⟩, rfl, rfl,
          rfl, readyView, fitsView, ?_⟩
        refine ⟨?_, ?_⟩
        · change (middle.observe app actor).application.publicView.BindingIncludable
            (runtime setup)
            ⟨(actor, middle.network.nextSerial actor), .commitment event (actor, .prepared serial)⟩
          simp only [PublicView.BindingIncludable, node]
          refine ⟨readyView, ?_, by trivial, by trivial, vacant, unused⟩
          change (match middle.application.activatedAt event with
            | none => False
            | some entered => middle.application.clock - entered < (runtime setup).deadline event)
          rw [activated]
          exact deadline
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
        · rw [reactiveBinding_result (runtime setup) leaks actor event payload choice serial middle
            fresh, cast_cast, cast_eq]
  | resolve actor payload binding checks outputEq codeEq =>
      intro effective
      have actorEq : actor = owner :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      by_cases isFalse : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) =
          false
      · have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
            false := by
          rw [← isFalse, cast_cast, cast_eq]
        subst actionEq
        have decision := (runtime setup).canonicalServiceDecision_resolution_false leaks actor
          (middle.recall actor) (middle.observe app actor) event actor payload binding checks
          outputEq codeEq node
        change response = _ at decision
        let material : app.Submission := ⟨⟨.withhold event, none⟩, .none⟩
        have packetEq : app.packet (app.submit middle.application actor material) actor
            (middle.network.known actor) material =
              ⟨.withhold event, none,
                middle.application.publicView.tokenFor (.withhold event)⟩ := by
          rfl
        refine ⟨material, decision, ?_, ?_⟩
        · refine ⟨⟨material, congrArg ReactiveApplication.Action.transmission decision⟩, rfl, rfl,
            by rw [packetEq]; rfl, readyView, fitsView, ?_⟩
          change (runtime setup).freshServiceAcceptable middle.application.publicView
            ⟨(actor, middle.network.nextSerial actor), app.packet
              (app.submit middle.application actor material) actor
              (middle.network.known actor) material⟩
          rw [packetEq]
          apply ((runtime setup).freshServiceEnvelope_withhold_iff middle.application.publicView
            (actor, middle.network.nextSerial actor) event actor payload binding checks outputEq
            codeEq node none _).mpr
          refine ⟨readyView, ?_, rfl,
            PublicView.tokenFor_of_eventReady _ _ event rfl readyView, rfl⟩
          change (match middle.application.activatedAt event with
            | none => False
            | some entered => middle.application.clock - entered < (runtime setup).deadline event)
          rw [activated]
          exact deadline
        · rw [decision]
          unfold RealizesAt
          rw [node]
          exact Or.inl ⟨by simp, by rw [packetEq]⟩
      · have isTrue : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) =
            true := by
          cases selected : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool)
          · exact (isFalse selected).elim
          · rfl
        obtain ⟨value, resolved⟩ := effective isTrue
        have stored := EventGraph.EventCode.binding_success_of_resolve_success binding checks true
          middle.application.config.store value resolved
        obtain ⟨handle, associated, handleOwner, fixed⟩ :=
          facts.binding.success_provenance binding value stored
        have actionEq : action =
            cast (congrArg EventGraph.EventField.Action outputEq.symm) true := by
          rw [← isTrue, cast_cast, cast_eq]
        subst actionEq
        have decision := ((runtime setup).canonicalServiceDecision_eq_of_not_bind leaks actor
          (middle.recall actor) (middle.observe app actor) event _
          (fun _ _ _ _ bind => by rw [node] at bind; cases bind)).trans
            ((runtime setup).serviceDecision_successful_opening leaks middle facts.inputs
              actor event payload binding checks outputEq codeEq node handle value associated
              handleOwner fixed resolved)
        change response = _ at decision
        let material : app.Submission :=
          (disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive actor
            (app.observePlayer middle.application actor) (middle.network.known actor)
        have packetEq : app.packet (app.submit middle.application actor material) actor
            (middle.network.known actor) material =
              ⟨.opening event handle ⟨payload, value⟩, some ⟨handle, ⟨payload, value⟩⟩,
                middle.application.publicView.tokenFor
                  (.opening event handle ⟨payload, value⟩)⟩ := by
          have emitted := WitnessedSubmission.normalizeReactive_emit (runtime setup) leaks
            middle.application actor (middle.network.known actor)
              (disclosureSubmission (.opening event handle ⟨payload, value⟩))
          have verified : middle.application.candidates.verify handle ⟨payload, value⟩ = true :=
            (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr fixed
          apply emitted.trans
          simp only [application, EventGraphRuntime.reactiveApplication,
            disclosureSubmission, WitnessedSubmission.emit, Submission.register,
            submitStep_opening, handleOwner, verified,
            and_self, ↓reduceIte]
        refine ⟨material, decision, ?_, ?_⟩
        · refine ⟨⟨material, congrArg ReactiveApplication.Action.transmission decision⟩, rfl, rfl,
            by rw [packetEq]; rfl, readyView, fitsView, ?_⟩
          change (runtime setup).freshServiceAcceptable middle.application.publicView
            ⟨(actor, middle.network.nextSerial actor), app.packet
              (app.submit middle.application actor material) actor
              (middle.network.known actor) material⟩
          rw [packetEq]
          apply ((runtime setup).freshServiceEnvelope_opening_iff middle.application.publicView
            (actor, middle.network.nextSerial actor) event actor payload binding checks outputEq
            codeEq node handle ⟨payload, value⟩ (some ⟨handle, ⟨payload, value⟩⟩) _).mpr
          refine ⟨readyView, ?_, by simp only [certifiedOpening, decide_true], ?_, rfl, handleOwner,
            associated, rfl, PublicView.tokenFor_of_eventReady _ _ event rfl readyView⟩
          · change (match middle.application.activatedAt event with
              | none => False
              | some entered => middle.application.clock - entered <
                  (runtime setup).deadline event)
            rw [activated]
            exact deadline
          · apply (middle.application.publicView.openingGuardsAccepted_iff actor event payload
              binding checks outputEq codeEq node handle ⟨payload, value⟩ _).mpr
            refine ⟨value, rfl, ?_⟩
            change EventGraph.GuardCheck.allAccepted? checks
              ((graph setup).publicStore middle.application.config.store) (.success value) =
                some true
            rw [EventGraph.GuardCheck.allAccepted?_publicStore]
            exact EventGraph.EventCode.guards_pass_of_resolve_success binding checks true
              middle.application.config.store value resolved
        · rw [decision]
          unfold RealizesAt
          rw [node]
          refine Or.inr ⟨isTrue, handle, value, by rw [packetEq], handleOwner, associated, ?_,
            stored, ⟨_, resolved⟩⟩
          rw [respond_candidate_fixed setup leaks middle actor _ handle (by rw [fixed]; simp)]
          exact fixed

end FirstTurn

section Turns

variable {setup leaks}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- An element in the middle of a list is the element at the length of its
prefix, and the prefix is the list's take. -/
private theorem split_take {α : Type} {list before after : List α} {entry : α}
    (split : list = before ++ entry :: after) :
    before = list.take before.length ∧
      ∃ bound : before.length < list.length, list[before.length] = entry := by
  subst split
  refine ⟨by simp, by simp, by simp⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A split of a list extended by one element is a split of the old list or
ends at the new element. -/
private theorem split_snoc {α : Type} {old before after : List α} {entry last : α}
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
theorem ownTurn?_congr {left right : PublicView (graph setup)}
    (same : left.observation = right.observation) (who : Player) :
    left.ownTurn? who = right.ownTurn? who := by
  simp only [PublicView.ownTurn?, PublicView.EventReady, same]

/-- At the first turn no earlier recorded response saw the event as the
player's turn. -/
theorem sourceServiceTurn_first {owner : Player} {event : (graph setup).EventId}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (first : sourceServiceTurn setup leaks owner event past view = some 0) :
    view.application.publicView.ownTurn? owner = some event ∧
      ∀ entry ∈ past, entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
  unfold sourceServiceTurn at first
  split at first
  · rename_i turn
    have counted := Option.some.inj first
    rw [List.countP_eq_zero] at counted
    exact ⟨turn, fun entry member equal => counted entry member (decide_eq_true equal)⟩
  · cases first

/-- The first entry of a recall that saw the event as its player's turn is at
turn index zero. -/
theorem exists_first_turn {owner : Player} {event : (graph setup).EventId}
    (entries : List (application setup leaks).PlayerEntry)
    (seen : ∃ entry ∈ entries,
      entry.beforeView.application.publicView.ownTurn? owner = some event) :
    ∃ before entry after, entries = before ++ entry :: after ∧
      sourceServiceTurn setup leaks owner event before entry.beforeView = some 0 := by
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
        unfold sourceServiceTurn
        simp only [turn, ↓reduceIte, Option.some.injEq]
        rw [List.countP_eq_zero]
        intro other member chosen
        exact earlier ⟨other, member, of_decide_eq_true chosen⟩

/-- Deciding at the first turn submits a fresh packet only there, only before
the event is recorded, and then it is the compiled decision. -/
theorem decidedTurnPolicy_submission {bound : (graph setup).EventId → Nat} {owner : Player}
    {event : (graph setup).EventId} {action : (graph setup).Action event}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (chosen : response ∈
      (decidedTurnPolicy setup leaks bound owner event action past view).support)
    {other : (graph setup).EventId}
    (submitted : (runtime setup).submittedEvent? leaks response = some other) :
    sourceServiceTurn setup leaks owner event past view = some 0 ∧
      (runtime setup).eventRecorded leaks past event = false ∧
      response = (runtime setup).canonicalServiceDecision leaks owner past view event action := by
  have silenced : ∀ response ∈ ((application setup leaks).silentPolicy past view).support,
      (runtime setup).submittedEvent? leaks response = none := by
    intro response member
    obtain rfl := (application setup leaks).silentPolicy_cases past view response member
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

end Turns

section Phase

variable {setup leaks}

/-- Every response extends each player's recall. -/
theorem respond_recall_prefix (execution : (application setup leaks).Execution)
    (who observer : Player) (response : (application setup leaks).Action) :
    execution.recall observer <+:
      (execution.respond (application setup leaks) who response).recall observer := by
  by_cases same : observer = who
  · subst observer
    obtain ⟨_, recalled, _⟩ := respond_recall_self setup leaks execution who response
    rw [recalled]
    exact List.prefix_append _ _
  · rw [(application setup leaks).respond_recall_other execution who observer same response]

/-- The owner decides `action` at the first turn at `event`; everyone else
is silent. -/
def decidedProfile (bound : (graph setup).EventId → Nat) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event) :
    Player → (application setup leaks).Policy :=
  Function.update (fun _ => (application setup leaks).silentPolicy) owner
    (decidedTurnPolicy setup leaks bound owner event action)

variable (leaks) in
theorem decidedProfile_submitsAtTurn (bound : (graph setup).EventId → Nat) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event) (who : Player) :
    SubmitsAtTurn setup leaks (decidedProfile (leaks := leaks) bound owner event action who)
      who := by
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
submits its decision packet. -/
structure DecidedPhase (delay bound : (graph setup).EventId → Nat)
    (start : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event)
    (execution : (application setup leaks).Execution) : Prop where
  recallPrefix : ∀ who, start.recall who <+: execution.recall who
  supported : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (start.recall owner).length ≤ before.length →
    entry.action ∈ (decidedTurnPolicy setup leaks bound owner event action before
      entry.beforeView).support
  submitted : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (runtime setup).submittedEvent? leaks entry.action = some event →
    ∃ message, entry.emitted = some message ∧
      FreshCall setup leaks owner event bound entry message ∧
      RealizesAt leaks start.application.config execution.application event action entry message
  firstTurn : ∀ before entry after, execution.recall owner = before ++ entry :: after →
    (start.recall owner).length ≤ before.length →
    sourceServiceTurn setup leaks owner event before entry.beforeView = some 0 →
    (runtime setup).submittedEvent? leaks entry.action = some event

/-- An entry of the recall at the boundary saw the event unready. -/
private theorem start_entry_unready {start : (application setup leaks).Execution}
    {event : (graph setup).EventId} (untouched : Untouched setup leaks event start)
    {owner : Player} {entry : (application setup leaks).PlayerEntry}
    (member : entry ∈ start.recall owner)
    (turn : entry.beforeView.application.publicView.ownTurn? owner = some event) : False :=
  untouched owner entry member (PublicView.ownTurn?_spec _ owner event turn).1

/-- At the boundary the decided phase holds trivially. -/
theorem DecidedPhase.initial (delay bound : (graph setup).EventId → Nat)
    {start : (application setup leaks).Execution} {owner : Player}
    {event : (graph setup).EventId} (action : (graph setup).Action event)
    (untouched : Untouched setup leaks event start)
    (submissions : SubmissionsAtTurn setup leaks start) :
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
    (submissions owner entry member event submitted)).elim

/-- A position before the boundary's recall length lies in that recall. -/
private theorem mem_start_of_short {start execution : List (application setup leaks).PlayerEntry}
    (prefixOf : start <+: execution) {before after : List (application setup leaks).PlayerEntry}
    {entry : (application setup leaks).PlayerEntry}
    (split : execution = before ++ entry :: after) (short : before.length < start.length) :
    entry ∈ start := by
  obtain ⟨rest, rfl⟩ := prefixOf
  obtain ⟨_, bound, entryAt⟩ := split_take split
  rw [← entryAt, List.getElem_append_left short]
  exact List.getElem_mem _

/-- The opportunity requirement: an owner whose ready event's deadline is
past its reaction bound has had a turn there. -/
theorem opportunity_turn {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    {owner : Player} {event : (graph setup).EventId}
    (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event) (entered : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (late : entered + delay event < execution.application.clock) :
    ∃ entry ∈ execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨scheduled, member, activate, _, seenReady⟩ := contract.opportunity _ trace event owner
    entered owned ((execution.application.publicView_eventReady event).mpr ready) activated late
  obtain ⟨answer, answerMember, viewEq⟩ := answered scheduled member owner activate
  have seen : answer.beforeView.application.publicView.EventReady event := by
    rw [viewEq]
    exact seenReady
  have current := (entry_view_current setup leaks execution facts.stable owner answer answerMember
    event seen (fun completed => ready.1 completed)).1
  refine ⟨answer, answerMember, ?_⟩
  rw [ownTurn?_congr current owner]
  exact ownTurn?_of_ready setup execution.application ready owned

end Phase

section Preservation

variable {setup leaks}

/-- At a first turn of the owner, the event became ready at most `delay`
slots ago. -/
private theorem first_turn_early {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    {owner : Player} {event : (graph setup).EventId}
    (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    {view : (application setup leaks).PlayerView}
    (first : sourceServiceTurn setup leaks owner event (execution.recall owner) view = some 0) :
    ∃ entered, execution.application.activatedAt event = some entered ∧
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
private theorem submittedEvent_submit (material : (application setup leaks).Submission) :
    (runtime setup).submittedEvent? leaks ⟨some material⟩ =
      material.call.packet.event? (graph setup) := rfl

/-- **The decided phase is preserved** by every round before completion. -/
theorem DecidedPhase.round {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {remaining : Nat} {start execution next : (application setup leaks).Execution}
    {owner : Player} {event : (graph setup).EventId} {action : (graph setup).Action event}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (phase : DecidedPhase delay bound start owner event action execution)
    (submissions : SubmissionsAtTurn setup leaks execution)
    (answered : ActivationsAnswered setup leaks execution)
    (same : execution.application.config = start.application.config)
    (ready : start.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (effective : EffectiveAction start.application.config event action)
    (reached : next ∈ ((application setup leaks).round scheduler
      (decidedProfile (leaks := leaks) bound owner event action) execution).support) :
    DecidedPhase delay bound start owner event action next := by
  let app := application setup leaks
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
  simp only [decidedProfile, Function.update_self] at chosen
  rw [recallEq] at chosen
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler remaining
    execution middle (.activate who) trace selected moved
  have readyMiddle : middle.application.config.cut.Ready event := by rw [sameApp]; exact readyNow
  have effectiveMiddle : EffectiveAction middle.application.config event action := by
    rw [sameApp, same]
    exact effective
  -- The first-turn decision, when the owner's input is its first turn.
  have firstDecision (first : sourceServiceTurn setup leaks who event (execution.recall who)
      (middle.observe app who) = some 0) :=
    let early := first_turn_early contract trace answered owned readyNow first
    firstTurn_freshCall timely middleTrace event owned readyMiddle early.choose
      (by rw [sameApp]; exact early.choose_spec.1) (by rw [sameApp]; exact early.choose_spec.2)
      action effectiveMiddle
  have fitsFirst (first : sourceServiceTurn setup leaks who event (execution.recall who)
      (middle.observe app who) = some 0) :
      PublicView.InclusionFitsDeadline (runtime setup) bound
        (middle.observe app who).application.publicView event := by
    obtain ⟨entered, activated, early⟩ :=
      first_turn_early contract trace answered owned readyNow first
    have bounded := timely event (by rw [owned]; rfl)
    unfold PublicView.InclusionFitsDeadline
    change (match middle.application.activatedAt event with
      | none => False
      | some entered => middle.application.clock - entered + bound event <
          (runtime setup).deadline event)
    rw [sameApp, activated]
    change execution.application.clock - entered + bound event < (runtime setup).deadline event
    omega
  have unrecorded (first : sourceServiceTurn setup leaks who event (execution.recall who)
      (middle.observe app who) = some 0) :
      (runtime setup).eventRecorded leaks (execution.recall who) event = false := by
    cases recorded : (runtime setup).eventRecorded leaks (execution.recall who) event
    · rfl
    · unfold EventGraphRuntime.eventRecorded at recorded
      obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
      exact ((sourceServiceTurn_first first).2 entry member
        (submissions who entry member event (of_decide_eq_true submitted))).elim
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
      obtain ⟨material, decision, call, realized⟩ := firstDecision first
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
  · intro before entry after split long first
    rw [recalled] at split
    rcases split_snoc split.symm with ⟨beforeEq, entryEq, _⟩ | ⟨rest, _, oldSplit⟩
    · subst beforeEq entryEq
      obtain ⟨material, decision, call, _⟩ := firstDecision first
      rw [recallEq] at decision call
      have opening := (application setup leaks).turnScheduledPolicy_selected
        (sourceServiceTurn setup leaks who event) (0 : Fin 1)
        (decidedOpportunity setup leaks bound who event action)
        (application setup leaks).silentPolicy
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
    · exact phase.firstTurn before entry rest oldSplit.symm long first

end Preservation

section Completing

variable {setup leaks}

/-- Steps from equal configurations have the same support. -/
private theorem mem_step_of_eq {first second : (graph setup).Config} (same : first = second)
    {event : (graph setup).EventId} (firstReady : first.cut.Ready event)
    (secondReady : second.cut.Ready event) {action : (graph setup).Action event}
    {next : (graph setup).Config} (member : next ∈ (first.step event firstReady action).support) :
    next ∈ (second.step event secondReady action).support := by
  subst same
  exact member

/-- A fresh submission's packet carries the submission's event. -/
private theorem issued_submittedEvent {entry : (application setup leaks).PlayerEntry}
    {material : (application setup leaks).Submission}
    (transmission : entry.action.transmission = some material)
    {state : EventGraphRuntime.State (graph setup)} {who : Player}
    {known : List (Message Player (WitnessedPacket (graph setup)))}
    {message : Message Player (WitnessedPacket (graph setup))}
    (packet : (application setup leaks).packet state who known material = message.payload) :
    (runtime setup).submittedEvent? leaks entry.action =
      message.payload.call.event? (graph setup) := by
  unfold EventGraphRuntime.submittedEvent?
  rw [transmission, ← packet]
  rfl

/-- At most one response of the decided phase submits for the event. -/
theorem DecidedPhase.fresh_unique {delay bound : (graph setup).EventId → Nat}
    {start execution : (application setup leaks).Execution} {owner : Player}
    {event : (graph setup).EventId} {action : (graph setup).Action event}
    (phase : DecidedPhase delay bound start owner event action execution)
    (submissions : SubmissionsAtTurn setup leaks execution)
    (untouched : Untouched setup leaks event start)
    {before after before' after' : List (application setup leaks).PlayerEntry}
    {entry entry' : (application setup leaks).PlayerEntry}
    (split : execution.recall owner = before ++ entry :: after)
    (split' : execution.recall owner = before' ++ entry' :: after')
    (submitted : (runtime setup).submittedEvent? leaks entry.action = some event)
    (submitted' : (runtime setup).submittedEvent? leaks entry'.action = some event) :
    before.length = before'.length := by
  have turnOf : ∀ {b e a}, execution.recall owner = b ++ e :: a →
      (runtime setup).submittedEvent? leaks e.action = some event →
      e.beforeView.application.publicView.ownTurn? owner = some event ∧
        sourceServiceTurn setup leaks owner event b e.beforeView = some 0 := by
    intro b e a s submittedHere
    have member : e ∈ execution.recall owner := by rw [s]; simp
    have turn := submissions owner e member event submittedHere
    refine ⟨turn, ?_⟩
    have long : (start.recall owner).length ≤ b.length := by
      by_contra short
      exact start_entry_unready untouched
        (mem_start_of_short (phase.recallPrefix owner) s (by omega)) turn
    exact (decidedTurnPolicy_submission (phase.supported b e a s long) submittedHere).1
  have earlier : ∀ {b e a b' e' a'}, execution.recall owner = b ++ e :: a →
      execution.recall owner = b' ++ e' :: a' →
      (runtime setup).submittedEvent? leaks e.action = some event →
      (runtime setup).submittedEvent? leaks e'.action = some event →
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
configuration completes the event with the decided action. -/
theorem DecidedPhase.complete_round {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {remaining : Nat} {start execution next : (application setup leaks).Execution}
    {owner : Player} {event : (graph setup).EventId} {action : (graph setup).Action event}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (phase : DecidedPhase delay bound start owner event action execution)
    (submissions : SubmissionsAtTurn setup leaks execution)
    (answered : ActivationsAnswered setup leaks execution)
    (untouched : Untouched setup leaks event start)
    (same : execution.application.config = start.application.config)
    (ready : start.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (reached : next ∈ ((application setup leaks).round scheduler
      (decidedProfile (leaks := leaks) bound owner event action) execution).support)
    (changed : next.application.config ≠ start.application.config) :
    next.application.config ∈ (start.application.config.step event ready action).support := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have readyNow : execution.application.config.cut.Ready event := by rw [same]; exact ready
  have unfinished : event ∉ execution.application.config.cut.completed := readyNow.1
  have soleOf (other : (graph setup).EventId)
      (otherReady : execution.application.config.cut.Ready other) : other = event :=
    (soleReady_of_ready setup execution.application readyNow).2 other
      ((execution.application.publicView_eventReady other).mpr otherReady)
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have configNext : next.application.config = middle.application.config := by
    rcases cases with ⟨_, rfl⟩ | ⟨who, _, response, _, rfl⟩
    · rfl
    · exact ((runtime setup).reactive_respond_application leaks middle who response).1
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
          cases reactiveAccepted : (application setup leaks).handle execution.application
              message with
          | none =>
              rw [reactiveAccepted] at changed
              exact (changed rfl).elim
          | some state =>
              have accepted := reactiveHandle_call reactiveAccepted
              change state.config ∈ _
              obtain ⟨named, namedEq, namedReady, _, _⟩ :=
                handle_config_mem_step (runtime setup) _ _ _ accepted
              have namedIs := soleOf named namedReady
              subst namedIs
              have sender := handle_sender_actor (runtime setup) _ _ _ accepted named namedEq
              have senderEq : message.sender = owner :=
                Option.some.inj (sender.symm.trans owned)
              obtain ⟨entry, member, material, transmission, emittedEq, _, _, packet⟩ :=
                facts.provenance.pending message (List.mem_of_find?_eq_some found)
              rw [senderEq] at member
              have submitted : (runtime setup).submittedEvent? leaks entry.action = some named := by
                rw [issued_submittedEvent transmission packet]
                exact namedEq
              obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
              obtain ⟨packetMessage, emittedP, call, realized⟩ :=
                phase.submitted before entry after split submitted
              rw [emittedEq] at emittedP
              cases Option.some.inj emittedP
              exact include_realized execution facts.stable start.application.config same named
                ready (congrFun facts.remembered named) owner owned action entry member call.ready
                message senderEq realized state accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, stepped, rfl⟩ := PMF.support_map .. ▸ supported
      change state.config ≠ _ at changed
      change state.config ∈ _
      change state ∈ (environmentStep (runtime setup) execution.application command).support
        at stepped
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
            obtain ⟨entered, activated, late⟩ :=
              expiry_due _ _ other readyNow stepped changed
            exfalso
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
            have submittedFirst := phase.firstTurn before first after split long firstTurn
            obtain ⟨packet, emittedFirst, call, _⟩ :=
              phase.submitted before first after split submittedFirst
            have firstMember : first ∈ execution.recall owner := by rw [split]; simp
            have sole : ∀ other' ∈ before ++ after,
                ¬ EmitsOtherFor (runtime setup) leaks other' other packet.id := by
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
              obtain ⟨issuer, issuerMember, material, transmission, issuerEmitted, _, _,
                issuerPacket⟩ := facts.provenance.inputs otherEnvelope inputMember
              have issuerSubmitted : (runtime setup).submittedEvent? leaks issuer.action =
                  some other := by
                rw [issued_submittedEvent transmission issuerPacket]
                exact addressed
              have issuerTurn := submissions _ issuer issuerMember other issuerSubmitted
              have issuerOwner : otherEnvelope.sender = owner :=
                Option.some.inj ((PublicView.ownTurn?_spec _ _ other issuerTurn).2.symm.trans
                  owned)
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
            have settled := settlesFreshCalls_history setup leaks contract.inclusion owner other
              owned trace before first after packet split call sole
            obtain ⟨enteredThen, activatedThen, early⟩ := call.fits.exists
            have activatedSame := (entry_view_current setup leaks execution facts.stable owner
              first firstMember other call.ready unfinished).2.2
            rw [activatedSame, activated, Option.some.injEq] at activatedThen
            subst activatedThen
            have receipt := (prescribed_packet_settles setup leaks contract.inclusion trace other
              owner owned before after first packet split call sole).1
              (by change _ < execution.application.clock; omega)
            exact unfinished (settled.2.2.1 receipt)
          · rw [environmentStep_expire_of_not_ready _ _ _ otherReady,
              PMF.mem_support_pure_iff] at stepped
            subst stepped
            exact (changed rfl).elim

end Completing

section Run

variable {setup leaks}

/-- Along the decided run every point keeps the boundary configuration or has
completed the event with the decided action. -/
theorem DecidedPhase.runUntil {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {start : (application setup leaks).Execution} {owner : Player}
    {event : (graph setup).EventId} {action : (graph setup).Action event}
    (untouched : Untouched setup leaks event start)
    (ready : start.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (effective : EffectiveAction start.application.config event action) :
    ∀ (count remaining : Nat) (execution : (application setup leaks).Execution),
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining + count, none, execution⟩) →
      DecidedPhase delay bound start owner event action execution →
      SubmissionsAtTurn setup leaks execution → ActivationsAnswered setup leaks execution →
      execution.application.config = start.application.config →
      ∀ stopped ∈ ((application setup leaks).runUntil scheduler
          (decidedProfile (leaks := leaks) bound owner event action)
          (fun final => event ∈ final.application.config.cut.completed) count execution).support,
        stopped.application.config = start.application.config ∨
          stopped.application.config ∈ (start.application.config.step event ready action).support
  := by
  let app := application setup leaks
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
        obtain ⟨middleTrace⟩ := app.raw_trace_round (initialLaw setup) horizon scheduler
          (decidedProfile (leaks := leaks) bound owner event action) (remaining + count) execution
          middle trace moved
        have atTurn := decidedProfile_submitsAtTurn leaks bound owner event action
        have submissions' := round_submissionsAtTurn setup leaks atTurn submissions moved
        have answered' := round_activationsAnswered setup leaks answered moved
        by_cases unchanged : middle.application.config = start.application.config
        · exact ih remaining middle middleTrace
            (phase.round (remaining := remaining + count) contract timely trace submissions
              answered same ready owned effective moved) submissions' answered' unchanged stopped
            rest
        · have completed := phase.complete_round (remaining := remaining + count) contract timely
            trace submissions answered untouched same ready owned moved unchanged
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
    {scheduler : (application setup leaks).Scheduler}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {players : Player → (application setup leaks).Policy} {event : (graph setup).EventId}
    {start : (application setup leaks).Execution}
    (bounded : start.environmentRecall.length ≤ horizon)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨horizon - start.environmentRecall.length, none, start⟩))
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
    event ∈ stopped.application.config.cut.completed := by
  let app := application setup leaks
  rcases app.runUntilHorizon_stopped scheduler _ _ horizon
      (horizon - start.environmentRecall.length) start stopped (by omega) reached with
    done | spent
  · exact done
  · obtain ⟨used, within, rounds, length⟩ := app.runUntil_runRounds scheduler _ _ _ start
      stopped reached
    obtain ⟨stoppedTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler
      players 0 used start stopped
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

/-- **Decided completion.** From a completion boundary of the turn-counted
policy, under the asynchronous contract with `delay + bound < deadline`, if the
owner decides an effective action at its first turn and every other response
is silent, every stopped point has completed the event with that action. -/
theorem decided_completion {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {turns : Nat} {timing : TurnTiming setup turns} {profile : BehavioralProfile setup.program}
    (event : (graph setup).EventId) (start : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns timing profile) event.val start)
    (bounded : start.environmentRecall.length ≤ horizon)
    (ready : start.application.config.cut.Ready event)
    {owner : Player} (owned : (graph setup).actor? event = some owner)
    (action : (graph setup).Action event)
    (effective : EffectiveAction start.application.config event action)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (decidedProfile (leaks := leaks) bound owner event action)
      (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
    stopped.application.config ∈ (start.application.config.step event ready action).support := by
  let app := application setup leaks
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
    (sourceServiceTurnPolicy setup leaks bound turns timing profile) _ bounded start
    boundary.supported
  obtain ⟨submissions, answered⟩ := roundsFrom_turnFacts setup leaks
    (fun who => sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns timing profile who) _
    start boundary.supported
  have untouched := boundary.untouched event rfl
  have phase := DecidedPhase.initial delay bound action untouched submissions (owner := owner)
  rcases DecidedPhase.runUntil contract timely untouched ready owned effective
      (horizon - start.environmentRecall.length) 0 start
      (by simpa only [Nat.zero_add] using startTrace) phase submissions answered rfl stopped
      reached with unchanged | completed
  · exfalso
    have notDone : event ∉ stopped.application.config.cut.completed := by
      rw [unchanged]
      exact ready.1
    exact notDone (runUntilHorizon_completes contract.completes bounded startTrace stopped reached)
  · exact completed

end Run

end Vegas
