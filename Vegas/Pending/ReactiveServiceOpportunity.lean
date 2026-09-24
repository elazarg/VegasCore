/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceCompletion
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventHonestDeadline

/-! # Timely recurring owner opportunities after dependency settlement

The existing reactive epoch visits every event before its one clock tick.
An event newly activated during an arbitrary epoch is at most one tick old
at the boundary. Its next reserved owner activation therefore remains timely
when the configured deadline is at least two, unless another allowed action
has already completed the event. Player omissions, malformed submissions,
passive leaks, and network reactions are unrestricted.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactive_respond_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    State.ActivationOrigin execution.application
      (execution.respond (runtime.reactiveApplication leaks) who action).application :=
  State.activationOrigin_of_activatedEq
    (congrArg PublicView.activatedAt (runtime.reactive_respond_application
      leaks execution who action).2)

theorem reactive_environment_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (supported : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : State.ActivationOrigin execution.application next.application := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at supported
      cases FinDist.mem_support_pure.mp supported
      exact State.activationOrigin_of_activatedEq rfl
  | activate who =>
      obtain ⟨updated, selected, rfl⟩ := FinDist.support_map .. ▸ supported
      obtain ⟨observed, _, rfl⟩ := FinDist.support_map .. ▸ selected
      exact State.activationOrigin_of_activatedEq rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at supported
      cases FinDist.mem_support_pure.mp supported
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => exact State.activationOrigin_of_activatedEq rfl
      | some message =>
          change State.ActivationOrigin execution.application
            ((handle runtime execution.application
              ⟨message.id, message.payload.call⟩).getD execution.application)
          cases accepted : handle runtime execution.application
              ⟨message.id, message.payload.call⟩ with
          | none => exact State.activationOrigin_of_activatedEq rfl
          | some state =>
              exact State.activationOrigin_of_refreshEq (handle_clock_activated runtime
                execution.application state ⟨message.id, message.payload.call⟩ accepted).2
  | application command =>
      obtain ⟨updated, selected, rfl⟩ := FinDist.support_map .. ▸ supported
      obtain ⟨state, reached, rfl⟩ := FinDist.support_map .. ▸ selected
      cases command with
      | grant event =>
          change state ∈ (environmentStep runtime execution.application (.grant event)).support
            at reached
          simp only [environmentStep, FinDist.mem_support_pure] at reached
          subst state
          exact State.activationOrigin_of_activatedEq rfl
      | advanceClock =>
          change state ∈ (environmentStep runtime execution.application .advanceClock).support
            at reached
          simp only [environmentStep, FinDist.mem_support_pure] at reached
          subst state
          exact State.activationOrigin_of_activatedEq rfl
      | executeSample event =>
          obtain ⟨_, stutter | changed⟩ :=
            runtime.environmentStep_executeSample_config_activated
              execution.application state event reached
          · exact State.activationOrigin_of_activatedEq stutter.2
          · obtain ⟨_, _, _, activated⟩ := changed
            exact State.activationOrigin_of_refreshEq activated
      | expire event =>
          obtain ⟨_, stutter | changed⟩ :=
            runtime.environmentStep_expire_config_activated
              execution.application state event reached
          · exact State.activationOrigin_of_activatedEq stutter.2
          · obtain ⟨_, _, _, activated⟩ := changed
            exact State.activationOrigin_of_refreshEq activated

theorem reactive_dispatch_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (invariant : execution.application.Invariant inputs)
    (supported : next ∈ ((runtime.reactiveApplication leaks).dispatch players command
      execution).support) : State.ActivationOrigin execution.application next.application := by
  obtain ⟨middle, environment, response⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have first := runtime.reactive_environment_activationOrigin leaks execution middle command
    environment
  have progress := runtime.reactive_environment_progress leaks inputs execution middle command
    invariant environment
  have second : State.ActivationOrigin middle.application next.application := by
    cases actor : command.actor? (runtime.reactiveApplication leaks) with
    | none =>
        rw [actor] at response
        cases FinDist.mem_support_pure.mp response
        exact State.activationOrigin_of_activatedEq rfl
    | some who =>
        rw [actor] at response
        obtain ⟨action, _, rfl⟩ := FinDist.support_map .. ▸ response
        exact runtime.reactive_respond_activationOrigin leaks middle who action
  exact first.trans second (by rw [progress.clock]; omega)
    (runtime.reactive_resume_progress leaks inputs players _ middle next
      progress.invariant response).completed

theorem runInteractionPlan_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (plan : List (ServiceInstruction graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (supported : next ∈ (runtime.runInteractionPlan leaks players network plan
      execution).support) : State.ActivationOrigin execution.application next.application := by
  induction plan generalizing execution with
  | nil =>
      cases FinDist.mem_support_pure.mp supported
      exact State.activationOrigin_of_activatedEq rfl
  | cons instruction rest ih =>
      obtain ⟨middle, moved, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      have first := runtime.interactionStep_facts leaks inputs players network instruction
        execution middle invariant moved
      have restProgress := runtime.runInteractionPlan_facts leaks inputs players network rest
        middle next first.invariant reached
      obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ moved)
      exact (runtime.reactive_dispatch_activationOrigin leaks inputs players execution middle
        command invariant dispatched).trans (ih middle first.invariant reached)
          (by rw [first.clock]; omega) restProgress.completed

/-- Newly activated events remain at most one actual tick old, regardless of
which predecessor omission, expiry, or accepted packet made them ready. -/
theorem interactionEpoch_new_activation_age (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (supported : next ∈ (runtime.runInteractionPlan leaks players network
      (interactionEpoch chosen networkTurns) execution).support)
    (event : graph.EventId) (absent : execution.application.activatedAt event = none)
    (entered : Nat) (activated : next.application.activatedAt event = some entered)
    (unfinished : event ∉ next.application.config.cut.completed) :
    next.application.clock - entered ≤ 1 := by
  have origin := runtime.runInteractionPlan_activationOrigin leaks inputs players network
    (interactionEpoch chosen networkTurns) execution next invariant supported
  rcases origin event entered activated unfinished with retained | created
  · rw [absent] at retained
    cases retained
  · have progress := runtime.runInteractionPlan_facts leaks inputs players network
      (interactionEpoch chosen networkTurns) execution next invariant supported
    rw [progress.clock, interactionEpoch_ticks]
    omega

omit [DecidableEq Player] in
theorem interactionEpoch_split_owner (chosen : ServiceOrder graph) (networkTurns : Nat)
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner) :
    ∃ before after, interactionEpoch chosen networkTurns =
      before ++ ServiceInstruction.player owner :: after ∧ serviceTicks before = 0 := by
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp (chosen.mem event)
  let visits := earlier.flatMap (interactionVisit networkTurns)
  refine ⟨visits ++ [.grant event],
    List.replicate networkTurns .wire ++ [.includeLatest event owner, .sample event] ++
      later.flatMap (interactionVisit networkTurns) ++ [.tick] ++
      (List.finRange graph.order.eventCount).map .expire, ?_, ?_⟩
  · simp only [interactionEpoch, split, List.flatMap_append, List.flatMap_cons,
      interactionVisit, actor, visits, List.append_assoc, List.cons_append,
      List.nil_append]
  · have allZero : ∀ events : List graph.EventId,
          serviceTicks (events.flatMap (interactionVisit networkTurns)) = 0 := by
      intro events
      induction events with
      | nil => rfl
      | cons current rest ih =>
          rw [List.flatMap_cons, serviceTicks_append, interactionVisit_ticks, ih]
    have zero : serviceTicks visits = 0 := allZero earlier
    rw [serviceTicks_append, zero]
    rfl

/-- The real next epoch reaches a reserved owner activation while the event
is ready and timely, or has already completed it through another allowed call.
The prefix includes arbitrary player responses and partial-leak reactions. -/
theorem interactionEpoch_owner_opportunity (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (entered : Nat) (activated : execution.application.activatedAt event = some entered)
    (age : execution.application.clock - entered ≤ 1)
    (supported : next ∈ (runtime.runInteractionPlan leaks players network
      (interactionEpoch chosen networkTurns) execution).support) :
    ∃ before after prior responded,
      interactionEpoch chosen networkTurns = before ++ .player owner :: after ∧
      prior ∈ (runtime.runInteractionPlan leaks players network before execution).support ∧
      responded ∈ (runtime.interactionStep leaks players network (.player owner) prior).support ∧
      next ∈ (runtime.runInteractionPlan leaks players network after responded).support ∧
      (event ∈ prior.application.config.cut.completed ∨
        (prior.application.config.cut.Ready event ∧
          prior.application.WithinDeadline runtime event)) := by
  obtain ⟨before, after, split, zero⟩ :=
    interactionEpoch_split_owner chosen networkTurns event owner actor
  rw [split] at supported
  obtain ⟨prior, prefixMem, responded, response, suffix⟩ :=
    runtime.runInteractionPlan_support_instruction leaks players network before after
      (.player owner) execution next supported
  refine ⟨before, after, prior, responded, split, prefixMem, response, suffix, ?_⟩
  have progress := runtime.runInteractionPlan_facts leaks inputs players network before
    execution prior invariant prefixMem
  rcases progress.ready_or_completed event ready with done | stillReady
  · exact Or.inl done
  · refine Or.inr ⟨stillReady, ?_⟩
    apply withinDeadline_of_age_le_one runtime feasible prior.application event entered
      (progress.activated event entered activated stillReady.1)
    rw [progress.clock, zero, Nat.add_zero]
    exact age

/-- A first completed dependency epoch is followed by a usable owner visit in
the existing recurring service. The predecessor's behavior is unrestricted. -/
theorem interactionEpoch_new_activation_opportunity (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution middle next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner)
    (absent : execution.application.activatedAt event = none)
    (ready : middle.application.config.cut.Ready event)
    (first : middle ∈ (runtime.runInteractionPlan leaks players network
      (interactionEpoch chosen networkTurns) execution).support)
    (second : next ∈ (runtime.runInteractionPlan leaks players network
      (interactionEpoch chosen networkTurns) middle).support) :
    ∃ before after prior responded,
      interactionEpoch chosen networkTurns = before ++ .player owner :: after ∧
      prior ∈ (runtime.runInteractionPlan leaks players network before middle).support ∧
      responded ∈ (runtime.interactionStep leaks players network (.player owner) prior).support ∧
      next ∈ (runtime.runInteractionPlan leaks players network after responded).support ∧
      (event ∈ prior.application.config.cut.completed ∨
        (prior.application.config.cut.Ready event ∧
          prior.application.WithinDeadline runtime event)) := by
  have progress := runtime.runInteractionPlan_facts leaks inputs players network
    (interactionEpoch chosen networkTurns) execution middle invariant first
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
    ((progress.invariant.activated_iff event).2 ⟨ready, by simp only [actor, Option.isSome_some]⟩)
  exact runtime.interactionEpoch_owner_opportunity feasible leaks inputs chosen networkTurns
    players network middle next progress.invariant event owner actor ready entered activated
    (runtime.interactionEpoch_new_activation_age leaks inputs chosen networkTurns
      players network execution middle invariant first event absent entered activated ready.1)
    second

end Vegas.EventGraphRuntime
