/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketAcceptedTable

/-! # The two ways an event with an actor completes

A scheduler round completing an event with an actor either includes an
accepted packet of the actor naming the event, whose call content at the state
it is included at is the decoded action, or is a contract command, an expiry,
that keeps the table of accepted handles and decodes to a failing action
(`Vegas.completion_cases`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **The two ways an actor completes.** A scheduler round completing an
event with an actor either includes an accepted packet of the actor naming the
event, whose call content at the state it is included at is the decoded
action, or is a contract command that keeps the accepted handles and whose
decoded action is failing. -/
theorem completion_cases
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support)
    {actor : Player} (acts : (graph setup).actor? event = some actor) :
    (∃ message ∈ next.network.ledger, message.sender = actor ∧
      message.payload.call.event? (graph setup) = some event ∧
      decodeEventAction setup.program event action =
        callContent setup execution.application message.payload.call ∧
      (∀ named candidate, message.payload.call = .commitment named candidate →
        candidate.1 = actor) ∧
      ∀ owner payload, (graph setup).outputLayout event = .binding owner payload →
        next.application.accepted (.inr event) ≠ none) ∨
    (next.application.accepted = execution.application.accepted ∧
      Failing (decodeEventAction setup.program event action)) := by
  have stutter : next.application.config = execution.application.config → False :=
    config_ne_of_step member
  cases command with
  | activate who =>
      exfalso
      apply stutter
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
  | wait =>
      exfalso
      apply stutter
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | «include» id =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change (execution.includePending (application setup leaks) id).application.config ∈ _
        at member
      refine Or.inl ?_
      change ∃ message ∈ (execution.includePending (application setup leaks) id).network.ledger,
        _
      cases found : execution.network.lookup id with
      | none =>
          exact (config_ne_of_step member (by
            simp only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found])).elim
      | some message =>
          obtain ⟨identified, _, ledgerEq⟩ :=
            includePending_found execution.network id message found
          cases accepted : (application setup leaks).handle execution.application message with
          | none =>
              exact (config_ne_of_step member (by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_none])).elim
          | some after =>
              have applicationEq :
                  (execution.includePending (application setup leaks) id).application = after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              have networkEq : (execution.includePending (application setup leaks) id).network =
                  (execution.network.includePending id).2 :=
                (application setup leaks).includePending_network execution id
              obtain ⟨_, namedEvent, named, _, _, sender⟩ :=
                accepted_inclusion execution.application after message accepted
              have call := reactiveHandle_call accepted
              rw [applicationEq] at member
              have onLedger : message ∈ (execution.includePending (application setup leaks)
                  id).network.ledger := by
                rw [networkEq, ledgerEq]
                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
              cases packet : message.payload.call with
              | malformed raw =>
                  rw [packet] at call
                  simp [handle] at call
              | commitment other candidate =>
                  rw [packet] at call
                  obtain ⟨owned, otherReady, owner, payload, outputEq, codeEq, view, configEq⟩ :=
                    handle_commitment_action execution.application after message.id other
                      candidate call
                  have otherMember : after.config ∈ (execution.application.config.step other
                      otherReady (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                        (execution.application.bindingResult candidate payload))).support := by
                    rw [commit_step _ other otherReady outputEq codeEq, configEq]
                    exact (PMF.mem_support_pure_iff _ _).mpr rfl
                  cases step_completion_unique otherMember member
                  rw [packet] at named
                  cases Option.some.inj named
                  obtain ⟨_, _, table, _⟩ := handle_commitment_accepted execution.application
                    after message.id _ candidate call
                  refine ⟨message, onLedger, Option.some.inj (sender.symm.trans acts),
                    by rw [packet]; rfl, ?_, fun named' candidate' same => ?_,
                    fun _ _ _ => ?_⟩
                  · rw [packet]
                    simp only [callContent, view]
                  · rw [packet] at same
                    cases same
                    exact owned.trans (Option.some.inj (sender.symm.trans acts))
                  · rw [applicationEq, table, Function.update_self]
                    exact Option.some_ne_none _
              | opening other candidate raw =>
                  rw [packet] at call
                  obtain ⟨otherReady, otherAction, otherMember, _, _, owner, payload, binding,
                    checks, outputEq, codeEq, view, actionEq⟩ :=
                    handle_opening_config_step (runtime setup) execution.application after
                      message.id other candidate raw call
                  cases step_completion_unique otherMember member
                  rw [packet] at named
                  cases Option.some.inj named
                  refine ⟨message, onLedger, Option.some.inj (sender.symm.trans acts), ?_, ?_,
                    fun _ _ same => ?_, fun _ _ layout => ?_⟩
                  · rw [packet]
                    rfl
                  rotate_left
                  · rw [packet] at same
                    cases same
                  · rw [outputEq] at layout
                    cases layout
                  rw [actionEq, packet]
                  simp only [callContent, view]
  | application command =>
      obtain ⟨changed, _⟩ := applicationStep_facts execution next command reached
      refine Or.inr ⟨(environmentStep_tables (runtime setup) _ _ command changed).1, ?_⟩
      cases command with
      | advanceClock =>
          exfalso
          apply stutter
          simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at changed
          rw [changed]
      | executeSample sampled =>
          exfalso
          obtain ⟨_, effect⟩ := environmentStep_executeSample_config_activated (runtime setup)
            execution.application next.application sampled changed
          rcases effect with ⟨configEq, _⟩ | ⟨sampledReady, sampledAction, sampledMember, _⟩
          · exact stutter configEq
          · cases step_completion_unique sampledMember member
            cases view : nodeView (graph setup) event with
            | sample _ _ outputEq codeEq =>
                rw [nodeView_sample_actor outputEq codeEq] at acts
                cases acts
            | bind _ _ _ _ =>
                rw [environmentStep_executeSample_of_nonsample (runtime setup) _ event ready
                  (fun _ _ _ _ same => by rw [view] at same; cases same),
                  PMF.mem_support_pure_iff] at changed
                exact stutter (congrArg (fun state => state.config) changed)
            | resolve _ _ _ _ _ _ =>
                rw [environmentStep_executeSample_of_nonsample (runtime setup) _ event ready
                  (fun _ _ _ _ same => by rw [view] at same; cases same),
                  PMF.mem_support_pure_iff] at changed
                exact stutter (congrArg (fun state => state.config) changed)
      | expire expired =>
          obtain ⟨_, effect⟩ := environmentStep_expire_config_activated (runtime setup)
            execution.application next.application expired changed
          rcases effect with ⟨configEq, _⟩ | ⟨expiredReady, expiredAction, expiredMember, _⟩
          · exact (stutter configEq).elim
          · cases step_completion_unique expiredMember member
            have timed : ∃ entered, execution.application.activatedAt event = some entered ∧
                (runtime setup).deadline event ≤ execution.application.clock - entered := by
              cases activated : execution.application.activatedAt event with
              | none =>
                  rw [environmentStep_expire_of_not_activated (runtime setup) _ event ready
                    activated, PMF.mem_support_pure_iff] at changed
                  exact (stutter (congrArg (fun state => state.config) changed)).elim
              | some entered =>
                  by_cases due : (runtime setup).deadline event ≤
                      execution.application.clock - entered
                  · exact ⟨entered, rfl, due⟩
                  · rw [environmentStep_expire_of_not_due (runtime setup) _ event ready entered
                      activated due, PMF.mem_support_pure_iff] at changed
                    exact (stutter (congrArg (fun state => state.config) changed)).elim
            obtain ⟨entered, activated, due⟩ := timed
            have actionOf : ∀ {output : EventGraph.EventField Player L}
                (outputEq : (graph setup).outputLayout event = output) (value : output.Value)
                (choice : output.Action),
                next.application = execution.application.complete event ready
                  (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
                  (cast (congrArg EventGraph.EventField.Value outputEq.symm) value) →
                action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice := by
              intro output outputEq value choice completed
              have history := execution.application.config.step_history event ready action _
                member
              rw [completed] at history
              change execution.application.config.history ++ [⟨event, _⟩] = _ at history
              exact (eq_of_heq (EventGraph.Completion.mk.inj
                (List.singleton_injective (List.append_cancel_left history))).2).symm
            cases view : nodeView (graph setup) event with
            | sample _ _ outputEq codeEq =>
                rw [nodeView_sample_actor outputEq codeEq] at acts
                cases acts
            | bind owner payload outputEq codeEq =>
                rw [environmentStep_expire_bind_eq (runtime setup) _ event ready entered activated
                  due owner payload outputEq codeEq view, PMF.mem_support_pure_iff] at changed
                rw [actionOf outputEq _ _ changed]
                exact decodeEventAction_failing_binding setup.program event.val event.isLt
                  outputEq
            | resolve owner payload binding checks outputEq codeEq =>
                rw [environmentStep_expire_resolve_eq (runtime setup) _ event ready entered
                  activated due owner payload binding checks outputEq codeEq view,
                  PMF.mem_support_pure_iff] at changed
                rw [actionOf outputEq _ _ changed]
                exact decodeEventAction_failing_publication setup.program event.val event.isLt
                  outputEq

end Vegas
