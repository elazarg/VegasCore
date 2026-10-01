/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPrescribedPotential
import Vegas.Pending.EventActivationAge
import Vegas.Pending.EventOpponentFrame
import Vegas.Pending.EventPrescribedAction

/-! # Environment conservation for partly prescribed play

Packet inclusion and application commands preserve the prescribed
continuation. For a free player this uses only the action its graph policy
selects at the concrete completion. Every prescribed player's accepted packet
is related to that player's cached action by the native protocol invariants.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The protocol facts needed only for prescribed players. No coherence or
cache condition is imposed on a free player's native implementation. -/
structure PrescribedEnvironmentState (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (prescribed : Player → Prop) : Prop where
  authorship : runtime.application.Authorship execution
  coherent : ∀ owner, prescribed owner → PolicyCoherentAll runtime execution owner
  bindingCoherent : ∀ owner, prescribed owner →
    BindingPolicyCoherentAll runtime execution owner
  resources : ∀ owner, prescribed owner →
    execution.native.application.CanonicalResources owner
  bindingSubmissions : ∀ owner, prescribed owner →
    execution.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner)
  resolutionOrigins : ∀ owner, prescribed owner →
    ResolutionOrigins runtime execution owner
  bindingInvariant : execution.native.application.BindingInvariant
  activationAge : ∀ owner, prescribed owner → ∀ event,
    graph.actor? event = some owner → ∀ entered,
      execution.native.application.activatedAt event = some entered →
      event ∉ execution.native.application.config.cut.completed →
      execution.native.application.clock - entered ≤ 1

theorem handle_withinDeadline
    (runtime : EventGraphRuntime graph) (before after : State graph)
    (message : Message Player (Payload graph)) (event : graph.EventId)
    (addressed : Payload.event? graph message.payload = some event)
    (accepted : runtime.handle before message = some after) :
    before.WithinDeadline runtime event := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [Payload.event?] at addressed
  | commitment addressedEvent candidate =>
      have same : addressedEvent = event := Option.some.inj addressed
      subst event
      by_contra late
      simp [handle, late] at accepted
  | opening addressedEvent candidate raw =>
      have same : addressedEvent = event := Option.some.inj addressed
      subst event
      by_contra late
      simp [handle, late] at accepted
  | withhold addressedEvent =>
      have same : addressedEvent = event := Option.some.inj addressed
      subst event
      by_contra late
      simp [handle, late] at accepted

/-- An accepted pending packet preserves the prescribed continuation. The
free-player premise mentions only this concrete effective completion;
prescribed players are discharged from the actual prescribed protocol. -/
theorem handle_prescribedContinuation
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile) (prescribed : Player → Prop) [DecidablePred prescribed]
    (execution : runtime.application.PolicyExecution)
    (assumptions : PrescribedEnvironmentState runtime execution prescribed)
    (message : Message Player (Payload graph))
    (pending : message ∈ execution.native.pool.pending)
    (next : State graph)
    (accepted : runtime.handle execution.native.application message = some next)
    (freeAction : ∀ event
      (_addressed : Payload.event? graph message.payload = some event)
      (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event)
      (_member : next.config ∈
        (execution.native.application.config.step event ready action).support)
      (owner : Player) (actor : graph.actor? event = some owner), ¬ prescribed owner →
      graph.normalizePolicy owner (profile owner) event actor
        (graph.playerObserve owner execution.native.application.config) =
          PMF.pure action) :
    next.prescribedContinuation profile prescribed =
      execution.native.application.prescribedContinuation profile prescribed := by
  obtain ⟨event, addressed, actor⟩ :=
    handle_event_actor runtime execution.native.application next message accepted
  obtain ⟨actualEvent, actualAddressed, ready, action, member, _⟩ :=
    runtime.handle_effectiveCompletion execution.native.application next message accepted
  have sameEvent : actualEvent = event :=
    Option.some.inj (actualAddressed.symm.trans addressed)
  subst actualEvent
  by_cases prescribedSender : prescribed message.sender
  · let owner := message.sender
    have other : prescribed owner := prescribedSender
    have timely := handle_withinDeadline runtime execution.native.application next message event
      addressed accepted
    obtain ⟨cachedAction, cached, cachedMember, _, memory⟩ :=
      runtime.handle_prescribed_owner_cached_action execution owner assumptions.authorship
        (assumptions.coherent owner other) (assumptions.bindingCoherent owner other)
        (assumptions.resources owner other) (assumptions.bindingSubmissions owner other)
        (assumptions.resolutionOrigins owner other) assumptions.bindingInvariant event ready timely
        actor message pending rfl addressed next accepted
    exact State.prescribedContinuation_eq_of_effective_step prescribed
      execution.native.application next ordered profile owner event ready actor
      cachedAction cachedMember memory
      (fun free => (free other).elim) (fun _ => cached)
  · exact State.prescribedContinuation_eq_of_effective_step prescribed
      execution.native.application next ordered profile message.sender event ready actor
      action member (runtime.handle_remembered _ _ _ accepted)
      (fun free => freeAction event addressed ready action member message.sender actor free)
      (fun prescribedOwner => (prescribedSender prescribedOwner).elim)

/-- Deadline resolution preserves the prescribed continuation. Prescribed
players' events cannot yet be due under their owner-local age certificate; a
free player's expiry is justified by its concrete effective action. -/
theorem environmentStep_expire_prescribedContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (prescribed : Player → Prop) [DecidablePred prescribed]
    (execution : runtime.application.PolicyExecution)
    (assumptions : PrescribedEnvironmentState runtime execution prescribed)
    (event : graph.EventId)
    (freeAction : ∀ (next : State graph)
      (_supported : next ∈
        (environmentStep runtime execution.native.application (.expire event)).support)
      (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event)
      (_member : next.config ∈
        (execution.native.application.config.step event ready action).support)
      (owner : Player) (actor : graph.actor? event = some owner), ¬ prescribed owner →
      graph.normalizePolicy owner (profile owner) event actor
        (graph.playerObserve owner execution.native.application.config) =
          PMF.pure action) :
    (environmentStep runtime execution.native.application (.expire event)).bind
        (fun next => next.prescribedContinuation profile prescribed) =
      execution.native.application.prescribedContinuation profile prescribed := by
  cases actorEq : graph.actor? event with
  | some owner =>
      by_cases prescribedOwner : prescribed owner
      · rw [runtime.environmentStep_expire_eq_of_age execution.native.application event
          (feasible event) (assumptions.activationAge owner prescribedOwner event actorEq)]
        simp
      · calc
          _ = (environmentStep runtime execution.native.application (.expire event)).bind
              (fun _ => execution.native.application.prescribedContinuation profile
                prescribed) := by
            apply bind_congr_on_support _
            intro next supported
            obtain unchanged | ⟨ready, action, member⟩ :=
              runtime.environmentStep_expire_config_eq_or_mem_step
                execution.native.application next event supported
            · exact next.prescribedContinuation_congr prescribed execution.native.application
                profile unchanged (fun query _ _ => congrFun
                  (runtime.environmentStep_remembered _ _ _ supported) query)
            · exact State.prescribedContinuation_eq_of_effective_step prescribed
                execution.native.application next ordered profile owner event ready actorEq
                action member (runtime.environmentStep_remembered _ _ _ supported)
                (fun free => freeAction next supported ready action member owner actorEq free)
                (fun prescribed => (prescribedOwner prescribed).elim)
          _ = _ := PMF.bind_const _ _
  | none =>
      cases view : nodeView graph event with
      | bind owner payload outputEq codeEq | resolve owner payload binding checks outputEq codeEq =>
          have strategic : graph.actor? event = some owner :=
            (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
              (congrArg EventCode.actor codeEq)
          rw [actorEq] at strategic
          contradiction
      | sample payload law outputEq codeEq =>
          by_cases ready : execution.native.application.config.cut.Ready event
          · cases activated : execution.native.application.activatedAt event with
            | none =>
                rw [runtime.environmentStep_expire_of_not_activated
                  execution.native.application event ready activated]
                simp
            | some entered =>
                by_cases due : runtime.deadline event ≤
                    execution.native.application.clock - entered
                · rw [runtime.environmentStep_expire_sample_eq
                    execution.native.application event ready entered activated due payload law
                    outputEq codeEq view]
                  simp
                · rw [runtime.environmentStep_expire_of_not_due
                    execution.native.application event ready entered activated due]
                  simp
          · rw [runtime.environmentStep_expire_of_not_ready
              execution.native.application event ready]
            simp

/-- Every direct environment application command preserves the prescribed
continuation under the local free-player expiry-action premise. -/
theorem environmentStep_prescribedContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (prescribed : Player → Prop) [DecidablePred prescribed]
    (execution : runtime.application.PolicyExecution)
    (assumptions : PrescribedEnvironmentState runtime execution prescribed)
    (command : EnvironmentCommand graph)
    (freeExpiry : ∀ event, command = .expire event → ∀ (next : State graph)
      (_supported : next ∈
        (environmentStep runtime execution.native.application (.expire event)).support)
      (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event)
      (_member : next.config ∈
        (execution.native.application.config.step event ready action).support)
      (owner : Player) (actor : graph.actor? event = some owner), ¬ prescribed owner →
      graph.normalizePolicy owner (profile owner) event actor
        (graph.playerObserve owner execution.native.application.config) =
          PMF.pure action) :
    (environmentStep runtime execution.native.application command).bind
        (fun next => next.prescribedContinuation profile prescribed) =
      execution.native.application.prescribedContinuation profile prescribed := by
  cases command with
  | advanceClock =>
      exact environmentStep_tick_prescribedContinuation prescribed runtime
        execution.native.application profile
  | executeSample event =>
      exact environmentStep_sample_prescribedContinuation prescribed runtime
        execution.native.application ordered profile event
  | expire event =>
      exact runtime.environmentStep_expire_prescribedContinuation feasible ordered profile
        prescribed execution assumptions event (freeExpiry event rfl)

/-- Delivery and waiting are application stutters. Inclusion either stutters
or consumes one accepted packet, and application commands use their exact
native kernel. -/
theorem environmentPolicyStep_prescribedContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (prescribed : Player → Prop) [DecidablePred prescribed]
    (execution : runtime.application.PolicyExecution)
    (assumptions : PrescribedEnvironmentState runtime execution prescribed)
    (command : runtime.application.EnvironmentPolicyCommand)
    (freeInclude : ∀ id, command = .include id →
      ∀ (message : Message Player (Payload graph)) (next : State graph)
      (_lookup : execution.native.pool.lookup id = some message)
      (_pending : message ∈ execution.native.pool.pending)
      (_accepted : runtime.handle execution.native.application message = some next)
      (event : graph.EventId)
      (_addressed : Payload.event? graph message.payload = some event)
      (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event)
      (_member : next.config ∈
        (execution.native.application.config.step event ready action).support)
      (owner : Player) (actor : graph.actor? event = some owner), ¬ prescribed owner →
      graph.normalizePolicy owner (profile owner) event actor
        (graph.playerObserve owner execution.native.application.config) =
          PMF.pure action)
    (freeExpiry : ∀ event, command = .application (.expire event) → ∀ (next : State graph)
      (_supported : next ∈
        (environmentStep runtime execution.native.application (.expire event)).support)
      (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event)
      (_member : next.config ∈
        (execution.native.application.config.step event ready action).support)
      (owner : Player) (actor : graph.actor? event = some owner), ¬ prescribed owner →
      graph.normalizePolicy owner (profile owner) event actor
        (graph.playerObserve owner execution.native.application.config) =
          PMF.pure action) :
    (runtime.application.environmentPolicyStep execution command).bind
        (fun next => next.native.application.prescribedContinuation profile prescribed) =
      execution.native.application.prescribedContinuation profile prescribed := by
  cases command with
  | deliver observer id | wait =>
      simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step]
  | «include» id =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        PMF.pure_bind]
      cases lookup : execution.native.pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing execution.native id lookup]
      | some message =>
          cases acceptedEq : runtime.handle execution.native.application message with
          | none =>
              rw [runtime.application.includePending_reject execution.native id message lookup
                acceptedEq]
          | some next =>
              rw [runtime.application.includePending_accept execution.native id message next
                lookup acceptedEq]
              apply runtime.handle_prescribedContinuation ordered profile prescribed execution
                assumptions message (List.mem_of_find?_eq_some lookup) next acceptedEq
              intro event addressed ready action member owner actor free
              exact freeInclude id rfl message next lookup (List.mem_of_find?_eq_some lookup)
                acceptedEq event addressed ready action member owner actor free
  | application applicationCommand =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        PMF.bind_bind, PMF.pure_bind]
      rw [PMF.bind_map]
      change (environmentStep runtime execution.native.application applicationCommand).bind
          (fun next => next.prescribedContinuation profile prescribed) =
        execution.native.application.prescribedContinuation profile prescribed
      exact runtime.environmentStep_prescribedContinuation feasible ordered profile prescribed
        execution assumptions applicationCommand
        (fun event same => freeExpiry event (congrArg _ same))

end Vegas.EventGraphRuntime
