/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFirstTurnMixture
import Vegas.Game.SourceServiceCompletion
import Vegas.Game.SourceServiceFacts
import Vegas.Pending.ExclusionPolicyLaw
import Vegas.Pending.PublicFailureEvidence
import Vegas.Pending.EventCommandFrame
import Vegas.Pending.AcceptedEventOwnership
import Interaction.ReactiveRawRoundTrace


/-! # Native continuation at a silent source instruction

When an owner is silent while its head event is ready, pending messages cannot
complete that event if none of its own pending calls names it. The native
runtime completes it by expiry. Composing the resulting endpoint with the
ordinary graph continuation gives the silent source step's full continuation,
including every automatic completion after default.

At an initialized untouched boundary, own-submission-at-turn discipline already
implies the required pending-message fact. Other players and the scheduler are
arbitrary; completion by the horizon is supplied by the ordinary service contract.
-/

noncomputable section
namespace Vegas
open SourceProgram EventGraphRuntime EventGraph GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

private theorem silent_step_eq_failure (state : EventGraphRuntime.State (graph setup))
    (event : (graph setup).EventId) (ready : state.config.cut.Ready event)
    (action : (graph setup).Action event) (silent : SilentAction event action) :
    state.config.step event ready action = PMF.pure (state.completeFailure event ready).config := by
  cases node : nodeView (graph setup) event with
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
            rw [← EventCode.readFields_cast outputEq ((graph setup).nodes event), codeEq]
            exact read)
        rw [EventCode.resolve_eval?, absent]
        rfl

private theorem expire_silent_eq (runtime : EventGraphRuntime (graph setup))
    (state : EventGraphRuntime.State (graph setup)) (event : (graph setup).EventId)
    (ready : state.config.cut.Ready event) (action : (graph setup).Action event)
    (silent : SilentAction event action) (entered : Nat)
    (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered) :
    environmentStep runtime state (.expire event) =
      PMF.pure (state.completeFailure event ready) := by
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      simp only [SilentAction, node] at silent
  | bind owner payload outputEq codeEq =>
      rw [environmentStep_expire_bind_eq runtime state event ready entered activated due
        owner payload outputEq codeEq node]
      simp only [EventGraphRuntime.State.completeFailure, node]
  | resolve owner payload binding checks outputEq codeEq =>
      rw [environmentStep_expire_resolve_eq runtime state event ready entered activated due
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

/-- At an untouched initialized boundary, a player whose prior submissions
were at its turn has no pending call for the head event. -/
theorem CompletionBoundary.no_pending_of_ownSubmissions (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (event : (graph setup).EventId) (execution : (application setup runtime leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (owner : Player) (truthful : OwnSubmissionsAtTurn setup leaks execution owner) :
    ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event := by
  let app := application setup runtime leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) execution.environmentRecall.length
    scheduler players execution.environmentRecall.length le_rfl execution boundary.supported
  have facts := legalFacts setup leaks execution.environmentRecall.length scheduler _ trace
  intro message pending sender named
  obtain ⟨entry, entryPresent, material, transmitted, _emitted, state, known, packet⟩ :=
    facts.provenance.pending message pending
  have old : entry ∈ execution.recall owner := sender ▸ entryPresent
  have call : material.call.packet = message.payload.call :=
    congrArg (fun value => value.call) packet
  have submitted : runtime.submittedEvent? leaks entry.action = some event := by
    simp only [EventGraphRuntime.submittedEvent?, transmitted]
    rw [call]
    exact named
  have turn := truthful entry old event submitted
  exact boundary.untouched event le_rfl owner entry old
    (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1

private theorem respond_no_owned_pending (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup runtime leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (actor : Player)
    (response : (application setup runtime leaks).Action)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event)
    (silent : actor = owner → response.transmission = none) :
    ∀ message ∈
      (execution.respond (application setup runtime leaks) actor response).network.pending,
      message.sender = owner → message.payload.call.event? (graph setup) ≠ some event := by
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

private theorem pending_call_rejected (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup runtime leaks).Execution)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owner : Player) (owned : (graph setup).actor? event = some owner)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event)
    (message : Message Player (WitnessedPacket (graph setup)))
    (pending : message ∈ execution.network.pending) :
    (application setup runtime leaks).handle execution.application message = none := by
  apply reactiveHandle_none
  cases handled : handle runtime execution.application ⟨message.id, message.payload.call⟩ with
  | none => rfl
  | some next =>
      obtain ⟨query, named, queryReady, _action, _moved⟩ :=
        handle_config_mem_step runtime execution.application next _ handled
      have same := setup.eventGraph.sequentialize_ready_unique _ queryReady ready
      subst query
      have authored := handle_sender_actor runtime execution.application next _ handled event named
      have sender : message.sender = owner := Option.some.inj (authored.symm.trans owned)
      exact (safe message pending sender named).elim

private theorem environment_silent_result (runtime : EventGraphRuntime (graph setup))
    (profile : (graph setup).BehavioralProfile)
    (state next : EventGraphRuntime.State (graph setup))
    (operation : EnvironmentCommand (graph setup))
    (event : (graph setup).EventId) (ready : state.config.cut.Ready event)
    (owner : Player) (owned : (graph setup).actor? event = some owner)
    (action : (graph setup).Action event) (silent : SilentAction event action)
    (quiescent : ∀ query, ¬ state.AutomaticReady query)
    (moved : next ∈ (environmentStep runtime state operation).support) :
    next.drain.config = state.config ∨
      event ∈ next.drain.config.cut.completed ∧
        (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          next.drain.config.remaining next.drain.config =
        (state.config.step event ready action).bind fun after =>
          (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
            after.remaining after := by
  rcases completionStep_environmentStep runtime state next operation moved with
    ⟨same, _⟩ | ⟨query, queryReady, queryAction, queryMoved, _⟩
  · have cleared : ∀ query, ¬ next.AutomaticReady query := by
      simpa only [EventGraphRuntime.State.AutomaticReady, same] using quiescent
    exact Or.inl ((congrArg EventGraphRuntime.State.config
      (next.drain_eq_of_clear cleared)).trans same)
  · have same := setup.eventGraph.sequentialize_ready_unique _ queryReady ready
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
      exact ready.1 ((environmentStep_owned_completed_iff runtime state next operation event owner
        owned other moved).mp done)
    subst operation
    obtain ⟨entered, activated, due⟩ : ∃ entered, state.activatedAt event = some entered ∧
        runtime.deadline event ≤ state.clock - entered := by
      cases activated : state.activatedAt event with
      | none =>
          rw [environmentStep_expire_of_not_activated runtime state event ready activated,
            PMF.mem_support_pure_iff] at moved
          exact (advancing (congrArg EventGraphRuntime.State.config moved)).elim
      | some entered =>
          by_cases due : runtime.deadline event ≤ state.clock - entered
          · exact ⟨entered, rfl, due⟩
          · rw [environmentStep_expire_of_not_due runtime state event ready entered activated due,
              PMF.mem_support_pure_iff] at moved
            exact (advancing (congrArg EventGraphRuntime.State.config moved)).elim
    have expired := expire_silent_eq runtime state event ready action silent entered activated due
    rw [expired, PMF.mem_support_pure_iff] at moved
    subst next
    refine Or.inr ⟨(state.completeFailure event ready).drainFuel_completed_subset _ done, ?_⟩
    rw [← EventGraphRuntime.State.drain_runPlan_canonical setup.eventGraph profile,
      silent_step_eq_failure state event ready action silent, PMF.pure_bind]


private theorem include_silent_config (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup runtime leaks).Execution)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owner : Player) (owned : (graph setup).actor? event = some owner)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event)
    (id : MessageId Player) :
    (execution.includePending (application setup runtime leaks) id).application.config =
      execution.application.config := by
  cases found : execution.network.lookup id with
  | none =>
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found]
  | some message =>
      have rejected := pending_call_rejected runtime leaks execution event ready owner owned safe
        message (List.mem_of_find?_eq_some found)
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, rejected, Option.getD_none]

private theorem round_silent_result (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (execution next : (application setup runtime leaks).Execution)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owner : Player) (owned : (graph setup).actor? event = some owner)
    (action : (graph setup).Action event) (silent : SilentAction event action)
    (quiescent : ∀ query, ¬ execution.application.AutomaticReady query)
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event)
    (quiet : ∀ past view, view.application.publicView.ownTurn? owner = some event →
      players owner past view = PMF.pure ⟨none⟩)
    (reached : next ∈
      ((application setup runtime leaks).round scheduler players execution).support) :
    (next.application.config = execution.application.config ∧
      ∀ message ∈ next.network.pending, message.sender = owner →
        message.payload.call.event? (graph setup) ≠ some event) ∨
    (event ∈ next.application.config.cut.completed ∧
      (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
        next.application.config.remaining next.application.config =
      (execution.application.config.step event ready action).bind fun after =>
        (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          after.remaining after) := by
  let app := application setup runtime leaks
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
      refine Or.inl ⟨include_silent_config runtime leaks execution event ready owner owned safe id,
        ?_⟩
      exact fun message present => safe message (sub present)
  | application operation =>
      change next ∈ (PMF.pure middle).support at resumed
      have sameNext := (PMF.mem_support_pure_iff _ _).mp resumed
      subst next
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep runtime execution.application operation).map
        EventGraphRuntime.State.drain).support at changed
      obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ changed
      rcases environment_silent_result runtime profile execution.application native operation
          event ready owner owned action silent quiescent nativeMoved with same | done
      · exact Or.inl ⟨same, safe⟩
      · exact Or.inr done
  | activate actor =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ resumed
      refine Or.inl ⟨(runtime.reactive_respond_application leaks _ actor response).1, ?_⟩
      apply respond_no_owned_pending runtime leaks _ owner event actor response
      · exact safe
      · intro same
        subst actor
        rw [quiet _ _ (by
          exact ownTurn?_of_ready setup execution.application ready owned),
          PMF.mem_support_pure_iff] at chosen
        exact congrArg ReactiveApplication.Action.transmission chosen


private theorem runUntil_silent_result (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (action : (graph setup).Action event) (silent : SilentAction event action)
    (quiet : ∀ past view, view.application.publicView.ownTurn? owner = some event →
      players owner past view = PMF.pure ⟨none⟩) :
    ∀ (count : Nat) (execution stopped : (application setup runtime leaks).Execution)
      (ready : execution.application.config.cut.Ready event),
      (∀ query, ¬ execution.application.AutomaticReady query) →
      (∀ message ∈ execution.network.pending, message.sender = owner →
        message.payload.call.event? (graph setup) ≠ some event) →
      stopped ∈ ((application setup runtime leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).support →
      event ∈ stopped.application.config.cut.completed →
      (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
        stopped.application.config.remaining stopped.application.config =
      (execution.application.config.step event ready action).bind fun after =>
        (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          after.remaining after := by
  let app := application setup runtime leaks
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
      rcases round_silent_result runtime leaks profile scheduler players execution middle event
          ready owner owned action silent quiescent safe quiet moved with
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
theorem silent_runUntil_bind_runPlan
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (horizon : Nat)
    (complete : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (action : (graph setup).Action event) (silent : SilentAction event action)
    (execution : (application setup runtime leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    {remaining : Nat}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (safe : ∀ message ∈ execution.network.pending, message.sender = owner →
      message.payload.call.event? (graph setup) ≠ some event)
    (quiet : ∀ past view, view.application.publicView.ownTurn? owner = some event →
      players owner past view = PMF.pure ⟨none⟩) :
    (((application setup runtime leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          after.remaining after := by
  let app := application setup runtime leaks
  have accounted : execution.environmentRecall.length + remaining = horizon :=
    app.raw_trace_horizon (initialLaw setup) horizon scheduler trace
  have countEq : horizon - execution.environmentRecall.length = remaining := by omega
  have facts := legalFacts setup leaks horizon scheduler _ trace
  apply (bind_congr_on_support _ fun stopped reached => ?_).trans (PMF.bind_const _ _)
  have reachedRemaining := reached
  change stopped ∈ (app.runUntil scheduler players
    (fun final => event ∈ final.application.config.cut.completed)
      (horizon - execution.environmentRecall.length) execution).support at reachedRemaining
  rw [countEq] at reachedRemaining
  apply runUntil_silent_result runtime leaks profile scheduler players event owner owned action
    silent quiet remaining execution stopped ready facts.quiescent safe reachedRemaining
  rcases app.runUntil_stopped scheduler players _ remaining execution stopped reachedRemaining with
    done | spent
  · exact done
  · obtain ⟨used, enough, rounds, lengthEq⟩ := app.runUntil_runRounds scheduler players _
      remaining execution stopped reachedRemaining
    obtain ⟨stoppedTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler players
      (remaining - used) used execution stopped
      (by simpa only [Nat.sub_add_cancel enough] using trace) rounds
    have terminal := complete _ stoppedTrace (by
      change remaining - used = 0 ∧ _
      exact ⟨by omega, rfl⟩)
    change stopped.application.config.cut.completed = Finset.univ at terminal
    rw [terminal]
    exact Finset.mem_univ _

end Vegas
