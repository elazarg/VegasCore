/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PublicFailureEvidence
import Vegas.Pending.AcceptedEventOwnership
import Vegas.Pending.EventCommandFrame
import Interaction.ReactiveMessageIdentity

/-! # Factual origins of native completion records

An environment command first includes a packet or executes its native operation,
then drains ready events of defaulted owners. Newly recorded completions retain
that distinction, including their actual decisions and public default metadata.
-/

noncomputable section

namespace Vegas

open Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L}

/-- Completing a ready event changes the configuration. -/
theorem config_ne_of_step {config next : graph.Config} {event : graph.EventId}
    {ready : config.cut.Ready event} {action : graph.Action event}
    (member : next ∈ (config.step event ready action).support) : next ≠ config := by
  intro same
  have completed : event ∈ next.cut.completed := by
    rw [config.step_cut event ready action next member]
    exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
  rw [same] at completed
  exact ready.1 completed

/-- A common one-step endpoint identifies the completed event. Requested
actions need not agree when their owner's default suppresses them. -/
theorem step_event_unique {config next : graph.Config}
    {first second : graph.EventId} {firstReady : config.cut.Ready first}
    {secondReady : config.cut.Ready second} {firstAction : graph.Action first}
    {secondAction : graph.Action second}
    (firstMember : next ∈ (config.step first firstReady firstAction).support)
    (secondMember : next ∈ (config.step second secondReady secondAction).support) :
    first = second := by
  have completed : first ∈ next.cut.completed := by
    rw [config.step_cut first firstReady firstAction next firstMember]
    exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
  rw [config.step_cut second secondReady secondAction next secondMember,
    EventOrder.Cut.mem_complete] at completed
  exact completed.resolve_right firstReady.1

private theorem completion_eq_of_new_step {config next : graph.Config}
    {event : graph.EventId} {ready : config.cut.Ready event} {action : graph.Action event}
    (member : next ∈ (config.step event ready action).support) (record : graph.Completion)
    (fresh : record ∉ config.history) (present : record ∈ next.history) :
    ∃ value, record = EventGraph.Completion.fromDecision event
      (config.actualDecision event action) value := by
  obtain ⟨value, _output, history⟩ := config.step_completion event ready action next member
  rw [history] at present
  exact ⟨value, List.mem_singleton.mp ((List.mem_append.mp present).resolve_left fresh)⟩

namespace EventGraphRuntime

/-- The typed requested failure action used by native expiry. -/
inductive ExpiredAction (event : graph.EventId) : graph.Action event → Prop
  | binding (owner : Player) (payload : L.Ty)
      (outputEq : graph.outputLayout event = .binding owner payload) :
      ExpiredAction event (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (none : Option (PublicationResult (L.Val payload))))
  | publication (payload : L.Ty) (outputEq : graph.outputLayout event = .publication payload) :
      ExpiredAction event (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)

omit [DecidableEq Player] in
/-- An expired publication uses the withholding action. -/
theorem ExpiredAction.publication_eq {event : graph.EventId} {action : graph.Action event}
    (expired : ExpiredAction event action) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .publication payload) :
    action = cast (congrArg EventGraph.EventField.Action outputEq.symm) false := by
  cases expired with
  | binding owner other binding => rw [binding] at outputEq; cases outputEq
  | publication other publication =>
      have same := EventGraph.EventField.publication.inj (publication.symm.trans outputEq)
      cases same
      rfl

/-- Automatic service appends chronology without an actual decision or a new default. -/
theorem State.completeAutomatic_history (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    (state.completeAutomatic event eligible).config.history =
      state.config.history ++ [⟨event, none, none⟩] := by
  obtain ⟨owner, acting, inactive⟩ := eligible.owned
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  obtain ⟨value, _output, history⟩ := state.config.step_completion event eligible.1 action
    (state.completeAutomatic event eligible).config supported
  rw [state.config.actualDecision_of_defaulted event owner acting inactive action] at history
  exact history

/-- Every new record in the actual automatic drain has no decision or new
default, and belongs to an owner defaulted before that drain began. -/
theorem State.drain_new_completion (state : State graph) (record : graph.Completion)
    (fresh : record ∉ state.config.history) (present : record ∈ state.drain.config.history) :
    record.decision = none ∧ record.defaultEvent = none ∧
      ∃ owner, graph.actor? record.event = some owner ∧ owner ∈ state.config.defaulted := by
  have origin : ∀ {before after : State graph},
      Relation.ReflTransGen State.AutomaticStep before after →
      record ∉ before.config.history → record ∈ after.config.history →
      record.decision = none ∧ record.defaultEvent = none ∧
        ∃ owner, graph.actor? record.event = some owner ∧ owner ∈ before.config.defaulted := by
    intro before after path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun absent inside => (absent inside).elim
    | @head before middle moved _ ih =>
        obtain ⟨event, eligible, rfl⟩ := moved
        intro absent inside
        by_cases recorded : record ∈ (before.completeAutomatic event eligible).config.history
        · rw [before.completeAutomatic_history event eligible] at recorded
          have same := List.mem_singleton.mp
            ((List.mem_append.mp recorded).resolve_left absent)
          subst record
          exact ⟨rfl, rfl, eligible.owned⟩
        · obtain ⟨silent, unchanged, owner, acting, inactive⟩ := ih recorded inside
          exact ⟨silent, unchanged, owner, acting, by
            simpa only [before.completeAutomatic_defaulted event eligible] using inactive⟩
  exact origin state.drain_trace fresh present

private theorem native_new_completion_cases (runtime : EventGraphRuntime graph)
    (state native : State graph) (command : EnvironmentCommand graph)
    (supported : native ∈ (environmentStep runtime state command).support)
    (record : graph.Completion) (fresh : record ∉ state.config.history)
    (present : record ∈ native.config.history) :
    (command = .expire record.event ∧
      ∃ entered, state.activatedAt record.event = some entered ∧
        runtime.deadline record.event ≤ state.clock - entered ∧
        ∃ (action : graph.Action record.event) (value : (graph.outputLayout record.event).Value),
          ExpiredAction record.event action ∧ record = EventGraph.Completion.fromDecision
            record.event (state.config.actualDecision record.event action) value) ∨
      graph.actor? record.event = none := by
  rcases completionStep_environmentStep runtime state native command supported with
    ⟨same, _⟩ | ⟨event, ready, action, member, _⟩
  · exact (fresh (by simpa only [same] using present)).elim
  obtain ⟨value, recorded⟩ := completion_eq_of_new_step member record fresh present
  have same : record.event = event := congrArg EventGraph.Completion.event recorded
  subst event
  cases acting : graph.actor? record.event with
  | none => exact Or.inr rfl
  | some owner =>
      have expired : command = .expire record.event := by
        by_contra other
        have kept := environmentStep_owned_completed_iff runtime state native command
          record.event owner acting other supported
        have completed : record.event ∈ native.config.cut.completed :=
          (native.config.history_exact record.event).mp (List.mem_map.mpr ⟨record, present, rfl⟩)
        exact ready.1 (kept.mp completed)
      subst command
      have stutter : native.config = state.config → False := config_ne_of_step member
      have timed : ∃ entered, state.activatedAt record.event = some entered ∧
          runtime.deadline record.event ≤ state.clock - entered := by
        cases activated : state.activatedAt record.event with
        | none =>
            rw [environmentStep_expire_of_not_activated runtime state record.event ready
              activated, PMF.mem_support_pure_iff] at supported
            exact (stutter (congrArg State.config supported)).elim
        | some entered =>
            by_cases due : runtime.deadline record.event ≤ state.clock - entered
            · exact ⟨entered, rfl, due⟩
            · rw [environmentStep_expire_of_not_due runtime state record.event ready entered
                activated due, PMF.mem_support_pure_iff] at supported
              exact (stutter (congrArg State.config supported)).elim
      obtain ⟨entered, activated, due⟩ := timed
      left
      refine ⟨rfl, entered, activated, due, ?_⟩
      cases view : nodeView graph record.event with
      | sample payload law outputEq codeEq =>
          rw [nodeView_sample_actor outputEq codeEq] at acting
          cases acting
      | bind bindingOwner payload outputEq codeEq =>
          rw [environmentStep_expire_bind_eq runtime state record.event ready entered activated
            due bindingOwner payload outputEq codeEq view, PMF.mem_support_pure_iff] at supported
          rw [supported] at present
          refine ⟨_, cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload)),
            .binding bindingOwner payload outputEq, ?_⟩
          exact List.mem_singleton.mp ((List.mem_append.mp present).resolve_left fresh)
      | resolve bindingOwner payload binding checks outputEq codeEq =>
          rw [environmentStep_expire_resolve_eq runtime state record.event ready entered activated
            due bindingOwner payload binding checks outputEq codeEq view,
            PMF.mem_support_pure_iff] at supported
          rw [supported] at present
          refine ⟨_, cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload)),
            .publication payload outputEq, ?_⟩
          exact List.mem_singleton.mp ((List.mem_append.mp present).resolve_left fresh)

/-- Every newly appended native record comes from the actual accepted packet,
due expiry, chance event, or automatic service after the actual primitive result.
Automatic records retain their inherited defaulted actor and both silent metadata fields. -/
theorem reactive_new_completion_cases (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈
      (execution.environmentStep (runtime.reactiveApplication leaks) command).support)
    (record : graph.Completion) (fresh : record ∉ execution.application.config.history)
    (present : record ∈ next.application.config.history) :
    (∃ message ∈ execution.network.pending, ∃ native,
      message ∈ next.network.ledger ∧ (message.id, true) ∈ next.receipts ∧
      message.payload.call.event? graph = some record.event ∧
      graph.actor? record.event = some message.sender ∧
      handle runtime execution.application ⟨message.id, message.payload.call⟩ = some native ∧
      native.drain = next.application ∧ record ∈ native.config.history) ∨
    (command = .application (.expire record.event) ∧
      ∃ entered, execution.application.activatedAt record.event = some entered ∧
        runtime.deadline record.event ≤ execution.application.clock - entered ∧
        ∃ (action : graph.Action record.event) (value : (graph.outputLayout record.event).Value),
          ExpiredAction record.event action ∧ record = EventGraph.Completion.fromDecision
            record.event (execution.application.config.actualDecision record.event action) value) ∨
    graph.actor? record.event = none ∨
    (∃ native, native.drain = next.application ∧ record ∉ native.config.history ∧
      ((∃ message ∈ execution.network.pending, command = .include message.id ∧
          handle runtime execution.application ⟨message.id, message.payload.call⟩ = some native) ∨
        ∃ operation, command = .application operation ∧
          native ∈ (environmentStep runtime execution.application operation).support) ∧
      record.decision = none ∧ record.defaultEvent = none ∧
        ∃ owner, graph.actor? record.event = some owner ∧ owner ∈ native.config.defaulted) := by
  cases command with
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact (fresh present).elim
  | wait =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact (fresh present).elim
  | «include» id =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      cases found : execution.network.lookup id with
      | none =>
          have unchanged : (execution.includePending (runtime.reactiveApplication leaks)
              id).application = execution.application := by
            simp only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found]
          exact (fresh (by simpa only [unchanged] using present)).elim
      | some message =>
          have identified : message.id = id := by
            have same := (List.find?_eq_some_iff_append.mp found).1
            simpa only [decide_eq_true_eq] using same
          have pending := List.mem_of_find?_eq_some found
          cases accepted : (runtime.reactiveApplication leaks).handle execution.application
              message with
          | none =>
              have unchanged : (execution.includePending (runtime.reactiveApplication leaks)
                  id).application = execution.application := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_none]
              exact (fresh (by simpa only [unchanged] using present)).elim
          | some after =>
              have applicationEq : (execution.includePending (runtime.reactiveApplication leaks)
                  id).application = after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
              have recordAfter : record ∈ native.drain.config.history := by
                simpa only [applicationEq, ← drained] using present
              by_cases primary : record ∈ native.config.history
              · obtain ⟨event, named, ready, action, moved⟩ :=
                  handle_config_mem_step runtime execution.application native _ handled
                obtain ⟨value, same⟩ := completion_eq_of_new_step moved record fresh primary
                have namedRecord : record.event = event := congrArg EventGraph.Completion.event same
                obtain ⟨other, otherNamed, actor⟩ :=
                  handle_event_actor runtime execution.application native _ handled
                have sameEvent : other = event := Option.some.inj (otherNamed.symm.trans named)
                subst other
                change graph.actor? event = some message.sender at actor
                left
                refine ⟨message, pending, native, ?_, ?_, ?_, ?_, handled, ?_, primary⟩
                · have network := (runtime.reactiveApplication leaks).includePending_network
                    execution id
                  rw [network]
                  simp only [MessageNetwork.includePending, found]
                  exact List.mem_append_right _ (List.mem_singleton_self _)
                · rw [show (execution.includePending (runtime.reactiveApplication leaks)
                      id).receipts = execution.receipts ++ [(id, true)] by
                    simp only [ReactiveApplication.Execution.includePending,
                      MessageNetwork.includePending, found, accepted, Option.isSome_some],
                    identified]
                  exact List.mem_append_right _ (List.mem_singleton_self _)
                · simpa only [namedRecord] using named
                · simpa only [namedRecord] using actor
                · exact drained.trans applicationEq.symm
              · right; right; right
                refine ⟨native, drained.trans applicationEq.symm, primary, ?_,
                  native.drain_new_completion record primary recordAfter⟩
                exact Or.inl ⟨message, pending, by rw [identified], handled⟩
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((environmentStep runtime execution.application operation).map
        State.drain).support at changed
      obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
      by_cases primary : record ∈ native.config.history
      · rcases native_new_completion_cases runtime execution.application native operation
          moved record fresh primary with expired | ownerless
        · obtain ⟨same, timed⟩ := expired
          subst operation
          exact Or.inr (Or.inl ⟨rfl, timed⟩)
        · exact Or.inr (Or.inr (Or.inl ownerless))
      · right; right; right
        exact ⟨native, rfl, primary, Or.inr ⟨operation, rfl, moved⟩,
          native.drain_new_completion record primary present⟩

end EventGraphRuntime
end Vegas
