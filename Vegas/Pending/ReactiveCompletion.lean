/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.AcceptedEventOwnership
import Vegas.Pending.EventCommandFrame
import Interaction.ReactiveMessageIdentity

/-! # Factual origins of reactive graph completions -/

noncomputable section

namespace Vegas

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L}

omit [DecidableEq Player] in
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

omit [DecidableEq Player] in
/-- A reached completion determines both its event and dependent action. -/
theorem step_completion_unique {config next : graph.Config}
    {first second : graph.EventId} {firstReady : config.cut.Ready first}
    {secondReady : config.cut.Ready second} {firstAction : graph.Action first}
    {secondAction : graph.Action second}
    (firstMember : next ∈ (config.step first firstReady firstAction).support)
    (secondMember : next ∈ (config.step second secondReady secondAction).support) :
    (⟨first, firstAction⟩ : graph.Completion) = ⟨second, secondAction⟩ := by
  have firstHistory := config.step_history first firstReady firstAction next firstMember
  have secondHistory := config.step_history second secondReady secondAction next secondMember
  rw [firstHistory] at secondHistory
  exact List.singleton_injective (List.append_cancel_left secondHistory)

namespace EventGraphRuntime

/-- The typed failure action used by expiry at an owned event. -/
inductive ExpiredAction (event : graph.EventId) : graph.Action event → Prop
  | binding (owner : Player) (payload : L.Ty)
      (outputEq : graph.outputLayout event = .binding owner payload) :
      ExpiredAction event (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))
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

/-- The same actual accepted message supplies its pending origin, ledger entry,
receipt, authenticated actor and handler result. An owned completion without
such a message is a due expiry with its exact typed failure action. -/
theorem reactive_completion_cases (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈
      (execution.environmentStep (runtime.reactiveApplication leaks) command).support)
    {event : graph.EventId} (ready : execution.application.config.cut.Ready event)
    (action : graph.Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support) :
    (∃ message ∈ execution.network.pending, message ∈ next.network.ledger ∧
      (message.id, true) ∈ next.receipts ∧ message.payload.call.event? graph = some event ∧
      graph.actor? event = some message.sender ∧
      handle runtime execution.application ⟨message.id, message.payload.call⟩ =
        some next.application) ∨
    (command = .application (.expire event) ∧
      ∃ entered, execution.application.activatedAt event = some entered ∧
        runtime.deadline event ≤ execution.application.clock - entered ∧
        next.application.accepted = execution.application.accepted ∧ ExpiredAction event action) ∨
    graph.actor? event = none := by
  have stutter : next.application.config = execution.application.config → False :=
    config_ne_of_step member
  cases command with
  | activate who =>
      exfalso
      apply stutter
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | wait =>
      exfalso
      apply stutter
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | «include» id =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change (execution.includePending (runtime.reactiveApplication leaks) id).application.config ∈
        _ at member
      cases found : execution.network.lookup id with
      | none =>
          exact (config_ne_of_step member (by
            simp only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found])).elim
      | some message =>
          have identified : message.id = id := by
            have same := (List.find?_eq_some_iff_append.mp found).1
            simpa only [decide_eq_true_eq] using same
          have ledgerEq : (execution.network.includePending id).2.ledger =
              execution.network.ledger ++ [message] := by
            simp only [MessageNetwork.includePending, found]
          cases accepted :
              (runtime.reactiveApplication leaks).handle execution.application message with
          | none =>
              exact (config_ne_of_step member (by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_none])).elim
          | some after =>
              have applicationEq :
                  (execution.includePending (runtime.reactiveApplication leaks) id).application =
                    after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              have receiptsEq :
                  (execution.includePending (runtime.reactiveApplication leaks) id).receipts =
                    execution.receipts ++ [(id, true)] := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.isSome_some]
              have networkEq :
                  (execution.includePending (runtime.reactiveApplication leaks) id).network =
                    (execution.network.includePending id).2 :=
                (runtime.reactiveApplication leaks).includePending_network execution id
              have call := reactiveHandle_call accepted
              obtain ⟨other, named, otherReady, otherAction, otherMember⟩ :=
                handle_config_mem_step runtime execution.application after _ call
              rw [applicationEq] at member
              cases step_completion_unique otherMember member
              obtain ⟨namedEvent, namedAgain, actor⟩ :=
                handle_event_actor runtime execution.application after _ call
              have same : namedEvent = event := Option.some.inj (namedAgain.symm.trans named)
              subst namedEvent
              refine Or.inl ⟨message, List.mem_of_find?_eq_some found, ?_, ?_, named, actor, ?_⟩
              · rw [networkEq, ledgerEq]
                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
              · rw [receiptsEq, identified]
                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
              · simpa only [applicationEq] using call
  | application command =>
      have changed : next.application ∈
          (environmentStep runtime execution.application command).support := by
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
        exact changed
      cases acting : graph.actor? event with
      | none => exact Or.inr (Or.inr rfl)
      | some owner =>
          have expired : command = .expire event := by
            by_contra other
            have same := environmentStep_owned_completed_iff runtime execution.application
              next.application command event owner acting other changed
            apply ready.1
            apply same.mp
            rw [execution.application.config.step_cut event ready action next.application.config
              member]
            exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
          subst command
          have timed : ∃ entered, execution.application.activatedAt event = some entered ∧
              runtime.deadline event ≤ execution.application.clock - entered := by
            cases activated : execution.application.activatedAt event with
            | none =>
                rw [environmentStep_expire_of_not_activated runtime _ event ready activated,
                  PMF.mem_support_pure_iff] at changed
                exact (stutter (congrArg (fun state => state.config) changed)).elim
            | some entered =>
                by_cases due : runtime.deadline event ≤ execution.application.clock - entered
                · exact ⟨entered, rfl, due⟩
                · rw [environmentStep_expire_of_not_due runtime _ event ready entered activated due,
                    PMF.mem_support_pure_iff] at changed
                  exact (stutter (congrArg (fun state => state.config) changed)).elim
          obtain ⟨entered, activated, due⟩ := timed
          refine Or.inr (Or.inl ⟨rfl, entered, activated, due,
            (environmentStep_tables runtime _ _ (.expire event) changed).1, ?_⟩)
          have actionOf : ∀ {output : EventGraph.EventField Player L}
              (outputEq : graph.outputLayout event = output) (value : output.Value)
              (choice : output.Action),
              next.application = execution.application.complete event ready
                (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
                (cast (congrArg EventGraph.EventField.Value outputEq.symm) value) →
              action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice := by
            intro output outputEq value choice completed
            have history := execution.application.config.step_history event ready action _ member
            rw [completed] at history
            change execution.application.config.history ++ [⟨event, _⟩] = _ at history
            exact (eq_of_heq (EventGraph.Completion.mk.inj
              (List.singleton_injective (List.append_cancel_left history))).2).symm
          cases view : nodeView graph event with
          | sample _ _ outputEq codeEq =>
              have ownerless : graph.actor? event = none := by
                change (graph.nodes event).actor = none
                rw [← EventGraph.EventCode.actor_cast outputEq (graph.nodes event), codeEq]
                rfl
              rw [ownerless] at acting
              cases acting
          | bind bindingOwner payload outputEq codeEq =>
              rw [environmentStep_expire_bind_eq runtime _ event ready entered activated due
                bindingOwner payload outputEq codeEq view, PMF.mem_support_pure_iff] at changed
              rw [actionOf outputEq _ _ changed]
              exact .binding bindingOwner payload outputEq
          | resolve bindingOwner payload binding checks outputEq codeEq =>
              rw [environmentStep_expire_resolve_eq runtime _ event ready entered activated due
                bindingOwner payload binding checks outputEq codeEq view,
                PMF.mem_support_pure_iff] at changed
              rw [actionOf outputEq _ _ changed]
              exact .publication payload outputEq

end EventGraphRuntime
end Vegas
