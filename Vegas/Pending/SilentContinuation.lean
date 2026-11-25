module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.SilentAction
public import Vegas.Pending.PrefixBoundary
public import Vegas.Pending.ReactiveSubmissionRecall
public import Vegas.Pending.ReactiveCanonicalDecision
public import Vegas.Pending.PublicFailureEvidence
public import Vegas.Pending.EventCommandFrame
public import Vegas.Pending.AcceptedEventOwnership
public import Vegas.Pending.ReactiveStateInvariant
public import Vegas.Pending.ExclusionPolicyLaw
public import Vegas.EventGraph.SolitaryEvent
public import Interaction.ReactiveProvenance

@[expose] public section

/-! # Silent actions at a solitary graph event

While the owner remains silent and no pending message of the owner names the
event, only expiry can complete it. The resulting configuration includes all
automatic completions caused by the expiry.
-/

noncomputable section

namespace Vegas
open EventGraphRuntime EventGraph GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace EventGraphRuntime

/-- At an initialized execution where `event` is untouched, a player whose
prior submissions were at its turn has no pending call for it. -/
theorem untouched_no_pending_of_ownSubmissions (timeouts : EventTimeouts
    graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {initial : PMF (State graph)} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (execution :
      ((reactiveApplication timeouts) leaks).Execution)
    (supported : execution ∈ (((reactiveApplication timeouts) leaks).roundsFrom
      initial scheduler players execution.environmentRecall.length).support)
    (untouched : ∀ who, ∀ entry ∈ execution.logs who,
      ¬ entry.beforeView.application.publicView.EventReady event)
    (owner : Player) (truthful : ∀ entry ∈ execution.logs owner, ∀ query,
      submittedEvent? timeouts leaks entry.action = some query →
        entry.beforeView.application.publicView.ownTurn? owner = some query) :
    ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? graph ≠ some event := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom
    initial execution.environmentRecall.length
    scheduler players execution.environmentRecall.length le_rfl execution supported
  have provenance := app.history_provenance initial execution.environmentRecall.length scheduler
    trace
  intro message pending sender named
  obtain ⟨entry, entryPresent, material, transmitted, _emitted, state, known, packet⟩ :=
    provenance.pending message pending
  have old : entry ∈ execution.logs owner := sender ▸ entryPresent
  have call : material.call.packet = message.payload.call :=
    congrArg (fun value => value.call) packet
  have submitted : (submittedEvent? timeouts) leaks entry.action = some event := by
    simp only [EventGraphRuntime.submittedEvent?, transmitted]
    rw [call]
    exact named
  have turn := truthful entry old event submitted
  exact untouched owner entry old
    (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1

private theorem silent_step_eq_failure (state : EventGraphRuntime.State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (action : graph.Action event) (silent : SilentAction event action) :
    state.config.step event ready action = PMF.pure (state.completeFailure event ready).config := by
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      simp only [SilentAction, node] at silent
  | bind owner payload outputEq codeEq =>
      have chosen : cast (congrArg EventField.Action outputEq) action = none := by
        simpa only [SilentAction, node] using silent
      have castBack := congrArg (cast (congrArg EventField.Action outputEq.symm)) chosen
      simp only [cast_cast, cast_eq] at castBack
      rw [castBack]
      rw [state.config.step_eq_map_of_code event ready outputEq (.bind owner payload) codeEq
        none (PMF.pure PublicationResult.failure)
        (by simp [EventCode.effectiveAction, EventCode.actor, EventCode.failureAction])]
      simp [EventGraphRuntime.State.completeFailure, node, EventGraphRuntime.State.complete,
        PMF.pure_map]
  | resolve owner payload binding checks outputEq codeEq =>
      have chosen : cast (congrArg EventField.Action outputEq) action = false := by
        simpa only [SilentAction, node] using silent
      have castBack := congrArg (cast (congrArg EventField.Action outputEq.symm)) chosen
      simp only [cast_cast, cast_eq] at castBack
      rw [castBack]
      rw [state.config.step_eq_map_of_code event ready outputEq
        (.resolve owner payload binding checks) codeEq false (PMF.pure PublicationResult.failure)]
      · simp [EventGraphRuntime.State.completeFailure, node, EventGraphRuntime.State.complete,
          PMF.pure_map]
      · simp only [EventCode.effectiveAction, EventCode.actor, EventCode.failureAction, ite_self]
        have absent := EventCode.resolveOutput?_false_eq_failure binding checks state.config.store
          (fun field read => by
            apply state.config.read_available ready
            rw [← EventCode.readFields_cast outputEq
              (graph.nodes event), codeEq]
            exact read)
        rw [EventCode.resolve_eval?, absent]
        rfl

private theorem expire_silent_eq (timeouts : EventTimeouts graph)
    (state : EventGraphRuntime.State graph) (event :
      graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (silent : SilentAction event action) (entered : Nat)
    (activated : state.activatedAt event = some entered)
    (due : timeouts.duration event ≤ state.clock - entered) :
    environmentStep timeouts state (.expire event) =
      PMF.pure (state.completeFailure event ready) := by
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      simp only [SilentAction, node] at silent
  | bind owner payload outputEq codeEq =>
      rw [environmentStep_expire_bind_eq timeouts state event ready entered activated due
        owner payload outputEq codeEq node]
      simp only [EventGraphRuntime.State.completeFailure, node]
  | resolve owner payload binding checks outputEq codeEq =>
      rw [environmentStep_expire_resolve_eq timeouts state event ready entered activated due
        owner payload binding checks outputEq codeEq node]
      simp only [EventGraphRuntime.State.completeFailure, node]

private theorem environment_pending_subset (app : ReactiveApplication Player)
    (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.network.pending ⊆ execution.network.pending := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst next
      exact List.Subset.refl _
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact List.Subset.refl _
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact List.Subset.refl _
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst next
      intro message present
      cases found : execution.network.lookup id with
      | none =>
          simpa only [ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found] using present
      | some selected =>
          apply MessagePool.mem_of_mem_removeFirst id message execution.network.pending
          simpa only [ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found] using present

private theorem respond_no_owned_pending (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : ((reactiveApplication timeouts) leaks).Execution) (owner : Player)
    (event : graph.EventId) (actor : Player)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? graph ≠ some event)
    (silent : actor = owner → response.transmission = none) :
    ∀ message ∈
      (execution.respond ((reactiveApplication timeouts) leaks) actor response).network.pending,
      message.sender = owner → message.payload.call.event?
        graph ≠ some event := by
  by_cases same : actor = owner
  · simp only [ReactiveApplication.Execution.respond, silent same]
    exact safe
  · rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact safe
    | some material =>
        intro message present sender named
        change message ∈ execution.network.pending ++ [_] at present
        rcases List.mem_append.mp present with old | fresh
        · exact safe message old sender named
        · obtain rfl := List.mem_singleton.mp fresh
          exact same sender

private theorem pending_call_rejected (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (event : graph.EventId) (solitary :
      graph.Solitary event)
        (ready : execution.application.config.cut.Ready event)
    (owner : Player) (owned : graph.actor? event = some owner)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? graph ≠ some event)
    (message : Message Player (WitnessedPacket graph))
    (pending : message ∈ execution.network.pending) :
    ((reactiveApplication timeouts) leaks).handle execution.application message = none := by
  apply reactiveHandle_none
  cases handled : handle timeouts execution.application ⟨message.id, message.payload.call⟩ with
  | none => rfl
  | some next =>
      obtain ⟨query, named, queryReady, _action, _moved⟩ :=
        handle_config_mem_step timeouts execution.application next _ handled
      have same := solitary _ queryReady ready
      subst query
      have authored := handle_sender_actor timeouts execution.application next _ handled event named
      have sender : message.sender = owner := Option.some.inj (authored.symm.trans owned)
      exact (safe message pending sender named).elim

private theorem environment_silent_result (timeouts : EventTimeouts graph)
    {Result : Type*} (continuation : graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (state next : EventGraphRuntime.State graph)
    (operation : EnvironmentCommand graph)
    (event : graph.EventId) (solitary :
      graph.Solitary event) (ready : state.config.cut.Ready event)
    (owner : Player) (owned : graph.actor? event = some owner)
    (action : graph.Action event) (silent : SilentAction event action)
    (quiescent : ∀ query, ¬ state.AutomaticReady query)
    (moved : next ∈ (environmentStep timeouts state operation).support) :
    next.drain.config = state.config ∨
      event ∈ next.drain.config.cut.completed ∧
        continuation next.drain.config =
        (state.config.step event ready action).bind fun after =>
          continuation after := by
  rcases completionStep_environmentStep timeouts state next operation moved with
    ⟨same, _⟩ | ⟨query, queryReady, queryAction, queryMoved, _⟩
  · have cleared : ∀ query, ¬ next.AutomaticReady query := by
      simpa only [EventGraphRuntime.State.AutomaticReady, same] using quiescent
    exact Or.inl ((congrArg EventGraphRuntime.State.config
      (next.drain_eq_of_clear cleared)).trans same)
  · have same := solitary _ queryReady ready
    subst query
    have done : event ∈ next.config.cut.completed := by
      rw [state.config.step_cut event queryReady queryAction next.config queryMoved,
        EventOrder.Cut.mem_complete]
      exact Or.inl rfl
    have advancing : next.config ≠ state.config := by
      intro same
      exact ready.1 (same ▸ done)
    have expires : operation = .expire event := by
      by_contra other
      exact ready.1 ((environmentStep_owned_completed_iff timeouts state next operation event owner
        owned other moved).mp done)
    subst operation
    obtain ⟨entered, activated, due⟩ : ∃ entered, state.activatedAt event = some entered ∧
        timeouts.duration event ≤ state.clock - entered := by
      cases activated : state.activatedAt event with
      | none =>
          rw [environmentStep_expire_of_not_activated timeouts state event ready activated,
            PMF.mem_support_pure_iff] at moved
          exact (advancing (congrArg EventGraphRuntime.State.config moved)).elim
      | some entered =>
          by_cases due : timeouts.duration event ≤ state.clock - entered
          · exact ⟨entered, rfl, due⟩
          · rw [environmentStep_expire_of_not_due timeouts state event ready entered activated due,
              PMF.mem_support_pure_iff] at moved
            exact (advancing (congrArg EventGraphRuntime.State.config moved)).elim
    have expired := expire_silent_eq timeouts state event ready action silent entered activated due
    rw [expired, PMF.mem_support_pure_iff] at moved
    subst next
    refine Or.inr ⟨(state.completeFailure event ready).drainFuel_completed_subset _ done, ?_⟩
    rw [drained, silent_step_eq_failure state event ready action silent, PMF.pure_bind]


private theorem include_silent_config (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (event : graph.EventId) (solitary :
      graph.Solitary event)
        (ready : execution.application.config.cut.Ready event)
    (owner : Player) (owned : graph.actor? event = some owner)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? graph ≠ some event)
    (id : MessageId Player) :
    (execution.includePending ((reactiveApplication timeouts) leaks) id).application.config =
      execution.application.config := by
  cases found : execution.network.lookup id with
  | none =>
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found]
  | some message =>
      have rejected := pending_call_rejected timeouts leaks execution event solitary ready owner
        owned safe
        message (List.mem_of_find?_eq_some found)
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, rejected, Option.getD_none]

private theorem round_silent_result (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {Result : Type*} (continuation : graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (event : graph.EventId) (solitary :
      graph.Solitary event)
        (ready : execution.application.config.cut.Ready event)
    (owner : Player) (owned : graph.actor? event = some owner)
    (action : graph.Action event) (silent : SilentAction event action)
    (quiescent : ∀ query, ¬ execution.application.AutomaticReady query)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? graph ≠ some event)
    (quiet : ∀ past view, view.application.publicView.ownTurn? owner = some event →
      players owner past view = PMF.pure ⟨none⟩)
    (reached : next ∈
      (((reactiveApplication timeouts) leaks).round scheduler players execution).support) :
    (next.application.config = execution.application.config ∧
      ∀ message ∈ next.network.pending, message.sender = owner →
        message.payload.call.event? graph ≠ some event) ∨
    (event ∈ next.application.config.cut.completed ∧
      continuation next.application.config =
      (execution.application.config.step event ready action).bind fun after =>
        continuation after) := by
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨command, _, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have sub := environment_pending_subset app execution middle command moved
  cases command with
  | wait =>
      change next ∈ (PMF.pure middle).support at resumed
      have sameNext := (PMF.mem_support_pure_iff _ _).mp resumed
      subst next
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at moved
      subst middle
      exact Or.inl ⟨rfl, safe⟩
  | «include» id =>
      change next ∈ (PMF.pure middle).support at resumed
      have sameNext := (PMF.mem_support_pure_iff _ _).mp resumed
      subst next
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at moved
      subst middle
      refine Or.inl ⟨include_silent_config timeouts leaks execution event solitary ready owner
        owned safe id,
        ?_⟩
      exact fun message present => safe message (sub present)
  | application operation =>
      change next ∈ (PMF.pure middle).support at resumed
      have sameNext := (PMF.mem_support_pure_iff _ _).mp resumed
      subst next
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep timeouts execution.application operation).map
        EventGraphRuntime.State.drain).support at changed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      rcases environment_silent_result timeouts continuation drained execution.application native
        operation
          event solitary ready owner owned action silent quiescent nativeMoved with same | done
      · exact Or.inl ⟨same, safe⟩
      · exact Or.inr done
  | activate actor =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ resumed
      refine Or.inl ⟨((reactive_respond_application timeouts) leaks _ actor response).1, ?_⟩
      apply respond_no_owned_pending timeouts leaks _ owner event actor response
      · exact safe
      · intro same
        subst actor
        rw [quiet _ _ (by
          exact execution.application.ownTurn?_of_ready solitary.ownerSolitary ready owned),
          PMF.mem_support_pure_iff] at chosen
        exact congrArg ReactiveApplication.Action.transmission chosen


private theorem runUntil_silent_result (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {Result : Type*} (continuation : graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (solitary :
      graph.Solitary event) (owner : Player)
    (owned : graph.actor? event = some owner)
    (action : graph.Action event) (silent : SilentAction event action)
    (quiet : ∀ past view, view.application.publicView.ownTurn? owner = some event →
      players owner past view = PMF.pure ⟨none⟩) :
    ∀ (count : Nat) (execution stopped : ((reactiveApplication timeouts) leaks).Execution)
      (ready : execution.application.config.cut.Ready event),
      (∀ query, ¬ execution.application.AutomaticReady query) →
      (∀ message ∈ execution.network.pending, message.sender = owner →
        message.payload.call.event? graph ≠ some event) →
      stopped ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).support →
      event ∈ stopped.application.config.cut.completed →
      continuation stopped.application.config =
      (execution.application.config.step event ready action).bind fun after =>
        continuation after := by
  let app := (reactiveApplication timeouts) leaks
  intro count
  induction count with
  | zero =>
      intro execution stopped ready _ _ reached done
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (ready.1 done).elim
  | succ count ih =>
      intro execution stopped ready quiescent safe reached done
      have running : ¬ event ∈ execution.application.config.cut.completed := ready.1
      simp only [ReactiveApplication.runUntil, running, ↓reduceIte] at reached
      obtain ⟨middle, moved, rest⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      rcases round_silent_result timeouts leaks continuation drained scheduler players execution
        middle event
          solitary ready owner owned action silent quiescent safe quiet moved with
        ⟨same, safeMiddle⟩ | ⟨completed, continuation⟩
      · have readyMiddle : middle.application.config.cut.Ready event := by
          rw [same]
          exact ready
        have quietMiddle : ∀ query, ¬ middle.application.AutomaticReady query := by
          simpa only [EventGraphRuntime.State.AutomaticReady, same] using quiescent
        simpa only [same] using ih middle stopped readyMiddle quietMiddle safeMiddle rest done
      · rw [app.runUntil_of_stop scheduler players _ count middle completed,
          PMF.mem_support_pure_iff] at rest
        subst stopped
        exact continuation


/-- Silence at an owned ready head has the same continuation as the source
omission, even when expiry automatically completes further events. The initial
execution may be any actual raw idle history. -/
theorem silent_runUntil_bind_continuation
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {Result : Type*} (continuation : graph.Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State graph,
      continuation state.drain.config = continuation state.config)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    {initial : PMF (State graph)} (horizon : Nat)
    (complete : CompletesPlay timeouts leaks initial horizon scheduler)
    (event : graph.EventId) (solitary :
      graph.Solitary event) (owner : Player)
    (owned : graph.actor? event = some owner)
    (action : graph.Action event) (silent : SilentAction event action)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (quiescent : ∀ query, ¬ execution.application.AutomaticReady query)
    {remaining : Nat}
    (trace : (((reactiveApplication timeouts) leaks).protocol
      initial horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? graph ≠ some event)
    (quiet : ∀ past view, view.application.publicView.ownTurn? owner = some event →
      players owner past view = PMF.pure ⟨none⟩) :
    ((((reactiveApplication timeouts) leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        continuation stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        continuation after := by
  let app := (reactiveApplication timeouts) leaks
  have accounted : execution.environmentRecall.length + remaining = horizon :=
    app.raw_trace_horizon initial horizon scheduler trace
  have countEq : horizon - execution.environmentRecall.length = remaining := by omega
  apply (bind_congr_on_support _ fun stopped reached => ?_).trans (PMF.bind_const _ _)
  have reachedRemaining := reached
  change stopped ∈ (app.runUntil scheduler players
    (fun final => event ∈ final.application.config.cut.completed)
      (horizon - execution.environmentRecall.length) execution).support at reachedRemaining
  rw [countEq] at reachedRemaining
  apply runUntil_silent_result timeouts leaks continuation drained scheduler players event solitary
    owner owned
    action
    silent quiet remaining execution stopped ready quiescent safe reachedRemaining
  rcases app.runUntil_stopped scheduler players _ remaining execution stopped reachedRemaining with
    done | spent
  · exact done
  · obtain ⟨used, enough, rounds, lengthEq⟩ := app.runUntil_runRounds scheduler players _
      remaining execution stopped reachedRemaining
    obtain ⟨stoppedTrace⟩ := app.raw_trace_runRounds
      initial horizon scheduler players
      (remaining - used) used execution stopped
      (by simpa only [Nat.sub_add_cancel enough] using trace) rounds
    have terminal := complete _ stoppedTrace (by
      change remaining - used = 0 ∧ _
      exact ⟨by omega, rfl⟩)
    change stopped.application.config.cut.completed = Finset.univ at terminal
    rw [terminal]
    exact Finset.mem_univ _

/-- Silence at an owned ready head has the same continuation as the graph
omission, even when expiry automatically completes further events. The initial
execution may be any actual raw idle history. -/
theorem silent_runUntil_bind_runPlan
    (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (profile : graph.sequentialize.BehavioralProfile)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    {inputs : PMF graph.sequentialize.Inputs} (horizon : Nat)
    (complete : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (event : graph.sequentialize.EventId) (owner : Player)
    (owned : graph.sequentialize.actor? event = some owner)
    (action : graph.sequentialize.Action event) (silent : SilentAction event action)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    {remaining : Nat}
    (trace : (((reactiveApplication timeouts) leaks).protocol (inputs.map State.initial) horizon
      scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? graph.sequentialize ≠ some event)
    (quiet : ∀ past view, view.application.publicView.ownTurn? owner = some event →
      players owner past view = PMF.pure ⟨none⟩) :
    ((((reactiveApplication timeouts) leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        graph.sequentialize.runPlan (graph.sequentialize.policyPlan profile
          graph.sequentialize.canonicalScheduler)
          stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        graph.sequentialize.runPlan (graph.sequentialize.policyPlan profile
          graph.sequentialize.canonicalScheduler)
          after.remaining after :=
  silent_runUntil_bind_continuation timeouts leaks
    (fun config => graph.sequentialize.runPlan
      (graph.sequentialize.policyPlan profile graph.sequentialize.canonicalScheduler)
        config.remaining config)
    (fun state => (EventGraphRuntime.State.drain_runPlan_canonical graph profile
      state).symm) scheduler players horizon complete event
    (graph.sequentialize_solitary event) owner owned action silent execution ready
    (reactive_history_quiescent timeouts leaks inputs horizon scheduler trace) trace safe quiet

end EventGraphRuntime
end Vegas
