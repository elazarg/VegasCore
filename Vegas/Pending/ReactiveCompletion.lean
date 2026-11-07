/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PublicFailureEvidence
import Vegas.Pending.ExclusionEvidence
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
    ∃ value, record = EventGraph.completion graph event
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

/-- A record newly appended by a native environment command comes from a due expiry
or from chance. -/
theorem native_new_completion_cases (runtime : EventGraphRuntime graph)
    (state native : State graph) (command : EnvironmentCommand graph)
    (supported : native ∈ (environmentStep runtime state command).support)
    (record : graph.Completion) (fresh : record ∉ state.config.history)
    (present : record ∈ native.config.history) :
    (command = .expire record.event ∧
      ∃ entered, state.activatedAt record.event = some entered ∧
        runtime.deadline record.event ≤ state.clock - entered ∧
        ∃ (action : graph.Action record.event) (value : (graph.outputLayout record.event).Value),
          ExpiredAction record.event action ∧ record = EventGraph.completion graph
            record.event (state.config.actualDecision record.event action) value) ∨
      graph.actor? record.event = none := by
  rcases completionStep_environmentStep runtime state native command supported with
    ⟨same, _⟩ | ⟨event, ready, action, member, _⟩
  · exact (fresh (by simpa only [same] using present)).elim
  obtain ⟨value, recorded⟩ := completion_eq_of_new_step member record fresh present
  have same : record.event = event := congrArg EventCompletion.event recorded
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
          ExpiredAction record.event action ∧ record = EventGraph.completion graph
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
                have namedRecord : record.event = event := congrArg EventCompletion.event same
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
      change state ∈ ((EventGraphRuntime.environmentStep runtime execution.application
        operation).map State.drain).support at changed
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

namespace Vegas.EventGraphRuntime.ExclusionEvidence

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem failed_primary (before native : State graph)
    (evidence : ExclusionEvidence 0 ∅ before)
    (nativeEvidence : ExclusionEvidence 0 ∅ native)
    (event : graph.EventId) (ready : before.config.cut.Ready event)
    (action : graph.Action event)
    (supported : native.config ∈ (before.config.step event ready action).support)
    (footprint : CompletionStep before native)
    (owner : Player) (active : owner ∉ before.config.defaulted)
    (introduced : owner ∈ native.config.defaulted) : native.PublicFailure event := by
  obtain ⟨query, owned, failed⟩ := (nativeEvidence.defaulted_zero owner).mp introduced
  rcases footprint with ⟨same, _accepted, _activated⟩ |
      ⟨named, namedReady, chosen, moved, _activated, acceptedOnly⟩
  · exact (config_ne_of_step supported same).elim
  · have namedCompleted : named ∈ native.config.cut.completed := by
      rw [before.config.step_cut named namedReady chosen _ moved]
      exact Finset.mem_insert_self _ _
    have same := State.completed_event_eq_of_step supported namedReady.1 namedCompleted
    subst named
    by_cases same : query = event
    · simpa only [same] using failed
    · have failedBefore := (State.PublicFailure.of_step_of_ne supported
        (fun field changed => (acceptedOnly field changed).2) same).mp failed
      exact (active ((evidence.defaulted_zero owner).mpr ⟨query, owned, failedBefore⟩)).elim

/-- A newly defaulted owner is attributed to the primary owned event of the
actual command. Automatic completions introduce no new default. -/
theorem new_default_origin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support)
    (owner : Player) (active : owner ∉ execution.application.config.defaulted)
    (introduced : owner ∈ next.application.config.defaulted)
    (evidence : ExclusionEvidence 0 ∅ execution.application) :
    ∃ event, graph.actor? event = some owner ∧ execution.application.config.cut.Ready event ∧
      next.application.PublicFailure event ∧
      ((∃ message ∈ execution.network.pending, command = .include message.id ∧
        message.sender = owner ∧ message.payload.call.event? graph = some event) ∨
      (command = .application (.expire event) ∧
        ∃ entered, execution.application.activatedAt event = some entered ∧
          runtime.deadline event ≤ execution.application.clock - entered)) := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst next
      exact (active introduced).elim
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact (active introduced).elim
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst next
      cases found : execution.network.lookup id with
      | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found] at introduced
          exact (active introduced).elim
      | some message =>
          cases accepted : (runtime.reactiveApplication leaks).handle execution.application
              message with
          | none =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, accepted, Option.getD_none] at introduced
              exact (active introduced).elim
          | some state =>
              have stateMember : owner ∈ state.config.defaulted := by
                simpa only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some] using introduced
              obtain ⟨native, handled, drained⟩ := reactiveHandle_call accepted
              have nativeMember : owner ∈ native.config.defaulted := by
                rw [← native.drain_defaulted, drained]
                exact stateMember
              obtain ⟨event, named, ready, action, moved⟩ :=
                handle_config_mem_step runtime execution.application native _ handled
              have owned := EventGraph.Config.step_new_default_actor
                execution.application.config native.config event ready action moved owner active
                nativeMember
              have authored := handle_sender_actor runtime execution.application native _ handled
                event named
              have failed := failed_primary execution.application native evidence
                (evidence.handle runtime _ native handled) event ready action moved
                (completionStep_handle runtime _ _ _ handled) owner active nativeMember
              have finalFailed : State.PublicFailure
                  (execution.includePending (runtime.reactiveApplication leaks) id).application
                  event := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
                rw [← drained]
                exact failed.of_completionPath native.drain_completionPath
              refine ⟨event, owned, ready, finalFailed,
                Or.inl ⟨message, List.mem_of_find?_eq_some found, ?_,
                  Option.some.inj (authored.symm.trans owned), named⟩⟩
              have identified : message.id = id := by simpa using List.find?_some found
              rw [identified]
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      change state ∈ ((EventGraphRuntime.environmentStep runtime execution.application
        operation).map State.drain).support at changed
      obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
      have nativeMember : owner ∈ native.config.defaulted := by
        rw [← native.drain_defaulted]
        exact introduced
      rcases completionStep_environmentStep runtime execution.application native operation moved
        with ⟨same, _, _⟩ | ⟨event, ready, action, sampled, _, _⟩
      · rw [same] at nativeMember
        exact (active nativeMember).elim
      · have owned := EventGraph.Config.step_new_default_actor
          execution.application.config native.config event ready action sampled owner active
          nativeMember
        have expired : operation = .expire event := by
          by_contra different
          apply ready.1
          apply (environmentStep_owned_completed_iff runtime execution.application native
            operation event owner owned different moved).mp
          rw [execution.application.config.step_cut event ready action native.config sampled]
          exact Finset.mem_insert_self _ _
        subst operation
        have timed : ∃ entered, execution.application.activatedAt event = some entered ∧
            runtime.deadline event ≤ execution.application.clock - entered := by
          cases activated : execution.application.activatedAt event with
          | none =>
              rw [environmentStep_expire_of_not_activated runtime execution.application event
                ready activated, PMF.mem_support_pure_iff] at moved
              exact (config_ne_of_step sampled (congrArg State.config moved)).elim
          | some entered =>
              by_cases due : runtime.deadline event ≤ execution.application.clock - entered
              · exact ⟨entered, rfl, due⟩
              · rw [environmentStep_expire_of_not_due runtime execution.application event ready
                  entered activated due, PMF.mem_support_pure_iff] at moved
                exact (config_ne_of_step sampled (congrArg State.config moved)).elim
        have failed := failed_primary execution.application native evidence
          (evidence.environmentStep runtime (.expire event) native moved) event ready action
          sampled (completionStep_environmentStep runtime _ _ (.expire event) moved)
          owner active nativeMember
        exact ⟨event, owned, ready, failed.of_completionPath native.drain_completionPath,
          Or.inr ⟨rfl, timed⟩⟩


end Vegas.EventGraphRuntime.ExclusionEvidence
