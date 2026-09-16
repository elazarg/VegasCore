/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventDeviationPotential
import Vegas.Pending.EventHonestDeadline
import Vegas.Pending.EventOpponentFrame
import Vegas.Pending.EventPrescribedAction

/-! # Environment conservation for native event deviations

Packet inclusion and application commands preserve the deviation continuation.
For the deviating player this uses only the action extracted at the concrete
completion.  Every other player's accepted packet is related to that player's
cached prescribed action by the native protocol invariants.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem eventCode_actor_cast (event : graph.EventId) (output : EventField Player L)
    (same : graph.outputLayout event = output) :
    EventCode.actor
        (cast (congrArg (EventCode graph.layout) same) (graph.nodes event)) =
      graph.actor? event := by
  cases same
  rfl

/-- The protocol facts needed only for unchanged players.  No coherence or
cache condition is imposed on the focal player's native implementation. -/
structure DeviationEnvironmentState (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (focal : Player) : Prop where
  authorship : runtime.application.Authorship execution
  coherent : ∀ owner, owner ≠ focal → PolicyCoherentAll runtime execution owner
  bindingCoherent : ∀ owner, owner ≠ focal →
    BindingPolicyCoherentAll runtime execution owner
  resources : ∀ owner, owner ≠ focal →
    execution.native.application.CanonicalResources owner
  bindingSubmissions : ∀ owner, owner ≠ focal →
    execution.native.pool.Satisfies
      (PrescribedBindingSubmissions (graph := graph) owner)
  resolutionOrigins : ∀ owner, owner ≠ focal →
    ResolutionOrigins runtime execution owner
  bindingInvariant : execution.native.application.BindingInvariant
  activationAge : ∀ owner, owner ≠ focal → ∀ event,
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

/-- An accepted pending packet preserves the deviation continuation.  The
focal premise mentions only this concrete effective completion; opponents are
discharged from the actual prescribed protocol. -/
theorem handle_deviationContinuation
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile) (focal : Player)
    (execution : runtime.application.PolicyExecution)
    (assumptions : DeviationEnvironmentState runtime execution focal)
    (message : Message Player (Payload graph))
    (pending : message ∈ execution.native.pool.pending)
    (next : State graph)
    (accepted : runtime.handle execution.native.application message = some next)
    (focalAction : ∀ event
      (_addressed : Payload.event? graph message.payload = some event)
      (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event)
      (_member : next.config ∈
        (execution.native.application.config.step event ready action).support)
      (actor : graph.actor? event = some focal),
      graph.normalizePolicy focal (profile focal) event actor
        (graph.playerObserve focal execution.native.application.config) =
          FinDist.pure action) :
    next.deviationContinuation profile focal =
      execution.native.application.deviationContinuation profile focal := by
  obtain ⟨event, addressed, actor⟩ :=
    handle_event_actor runtime execution.native.application next message accepted
  obtain ⟨actualEvent, actualAddressed, ready, action, member, _⟩ :=
    runtime.handle_effectiveCompletion execution.native.application next message accepted
  have sameEvent : actualEvent = event :=
    Option.some.inj (actualAddressed.symm.trans addressed)
  subst actualEvent
  by_cases sender : message.sender = focal
  · have focalActor : graph.actor? event = some focal := actor.trans (congrArg some sender)
    exact State.deviationContinuation_eq_of_effective_step
      execution.native.application next ordered profile focal focal event ready focalActor
      action member (runtime.handle_remembered _ _ _ accepted)
      (fun _ owned => focalAction event addressed ready action member owned)
      (fun different => (different rfl).elim)
  · let owner := message.sender
    have other : owner ≠ focal := sender
    have timely := handle_withinDeadline runtime execution.native.application next message event
      addressed accepted
    obtain ⟨cachedAction, cached, cachedMember, _, memory⟩ :=
      runtime.handle_prescribed_owner_cached_action execution owner assumptions.authorship
        (assumptions.coherent owner other) (assumptions.bindingCoherent owner other)
        (assumptions.resources owner other) (assumptions.bindingSubmissions owner other)
        (assumptions.resolutionOrigins owner other) assumptions.bindingInvariant event ready timely
        actor message pending rfl addressed next accepted
    exact State.deviationContinuation_eq_of_effective_step
      execution.native.application next ordered profile focal owner event ready actor
      cachedAction cachedMember memory
      (fun same => (other same).elim) (fun _ => cached)

/-- Deadline resolution preserves the deviation continuation.  Opponent-owned
events cannot yet be due under their owner-local age certificate; a focal
expiry is justified by its concrete extracted effective action. -/
theorem environmentStep_expire_deviationContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (focal : Player) (execution : runtime.application.PolicyExecution)
    (assumptions : DeviationEnvironmentState runtime execution focal)
    (event : graph.EventId)
    (focalAction : ∀ (next : State graph)
      (_supported : next ∈
        (environmentStep runtime execution.native.application (.expire event)).support)
      (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event)
      (_member : next.config ∈
        (execution.native.application.config.step event ready action).support)
      (actor : graph.actor? event = some focal),
      graph.normalizePolicy focal (profile focal) event actor
        (graph.playerObserve focal execution.native.application.config) =
          FinDist.pure action) :
    (environmentStep runtime execution.native.application (.expire event)).bind
        (fun next => next.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  cases actorEq : graph.actor? event with
  | some owner =>
      by_cases same : owner = focal
      · subst owner
        calc
          _ = (environmentStep runtime execution.native.application (.expire event)).bind
              (fun _ => execution.native.application.deviationContinuation profile focal) := by
            apply FinDist.bind_congr
            intro next supported
            obtain unchanged | ⟨ready, action, member⟩ :=
              runtime.environmentStep_expire_config_eq_or_mem_step
                execution.native.application next event supported
            · exact next.deviationContinuation_congr execution.native.application profile focal
                unchanged (fun query _ _ => congrFun
                  (runtime.environmentStep_remembered _ _ _ supported) query)
            · exact State.deviationContinuation_eq_of_effective_step
                execution.native.application next ordered profile focal focal event ready actorEq
                action member (runtime.environmentStep_remembered _ _ _ supported)
                (fun _ owned => focalAction next supported ready action member owned)
                (fun different => (different rfl).elim)
          _ = _ := FinDist.bind_const _ _
      · rw [runtime.environmentStep_expire_eq_of_age execution.native.application event
          (feasible event) (assumptions.activationAge owner same event actorEq)]
        simp
  | none =>
      cases view : nodeView graph event with
      | bind owner payload outputEq codeEq | resolve owner payload binding checks outputEq codeEq =>
          have strategic : graph.actor? event = some owner :=
            (eventCode_actor_cast event _ outputEq).symm.trans
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

/-- Every direct environment application command preserves the deviation
continuation under the local focal expiry-action premise. -/
theorem environmentStep_deviationContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (focal : Player) (execution : runtime.application.PolicyExecution)
    (assumptions : DeviationEnvironmentState runtime execution focal)
    (command : EnvironmentCommand graph)
    (focalExpiry : ∀ event, command = .expire event → ∀ (next : State graph)
      (_supported : next ∈
        (environmentStep runtime execution.native.application (.expire event)).support)
      (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event)
      (_member : next.config ∈
        (execution.native.application.config.step event ready action).support)
      (actor : graph.actor? event = some focal),
      graph.normalizePolicy focal (profile focal) event actor
        (graph.playerObserve focal execution.native.application.config) =
          FinDist.pure action) :
    (environmentStep runtime execution.native.application command).bind
        (fun next => next.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  cases command with
  | grant event =>
      exact environmentStep_grant_deviationContinuation runtime execution.native.application
        profile focal event
  | advanceClock =>
      exact environmentStep_tick_deviationContinuation runtime execution.native.application
        profile focal
  | executeSample event =>
      exact environmentStep_sample_deviationContinuation runtime execution.native.application
        ordered profile focal event
  | expire event =>
      exact runtime.environmentStep_expire_deviationContinuation feasible ordered profile focal
        execution assumptions event (focalExpiry event rfl)

/-- Delivery and waiting are application stutters. Inclusion either stutters
or consumes one accepted packet, and application commands use their exact
native kernel. -/
theorem environmentPolicyStep_deviationContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (focal : Player) (execution : runtime.application.PolicyExecution)
    (assumptions : DeviationEnvironmentState runtime execution focal)
    (command : runtime.application.EnvironmentPolicyCommand)
    (focalInclude : ∀ id, command = .include id →
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
      (actor : graph.actor? event = some focal),
      graph.normalizePolicy focal (profile focal) event actor
        (graph.playerObserve focal execution.native.application.config) =
          FinDist.pure action)
    (focalExpiry : ∀ event, command = .application (.expire event) → ∀ (next : State graph)
      (_supported : next ∈
        (environmentStep runtime execution.native.application (.expire event)).support)
      (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event)
      (_member : next.config ∈
        (execution.native.application.config.step event ready action).support)
      (actor : graph.actor? event = some focal),
      graph.normalizePolicy focal (profile focal) event actor
        (graph.playerObserve focal execution.native.application.config) =
          FinDist.pure action) :
    (runtime.application.environmentPolicyStep execution command).bind
        (fun next => next.native.application.deviationContinuation profile focal) =
      execution.native.application.deviationContinuation profile focal := by
  cases command with
  | deliver observer id | wait =>
      simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step]
  | «include» id =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.pure_bind]
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
              apply runtime.handle_deviationContinuation ordered profile focal execution assumptions
                message (List.mem_of_find?_eq_some lookup) next acceptedEq
              intro event addressed ready action member actor
              exact focalInclude id rfl message next lookup (List.mem_of_find?_eq_some lookup)
                acceptedEq event addressed ready action member actor
  | application applicationCommand =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.bind_bind, FinDist.pure_bind]
      rw [FinDist.bind_map]
      change (environmentStep runtime execution.native.application applicationCommand).bind
          (fun next => next.deviationContinuation profile focal) =
        execution.native.application.deviationContinuation profile focal
      exact runtime.environmentStep_deviationContinuation feasible ordered profile focal execution
        assumptions applicationCommand (fun event same => focalExpiry event (congrArg _ same))

end Vegas.EventGraphRuntime
