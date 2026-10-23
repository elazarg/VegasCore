/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketActorRecord
import Vegas.Pending.ReactiveAcceptedOutput

/-! # The content of a completing packet

**Call content.** The *content* of a call at a contract state is the source
action it decodes to there: for a commitment, the commitment of the value its
handle binds, at any slot; for an opening, the disclosure; nothing for a
malformed call (`Vegas.callContent`). The source action a response transmits,
read when it is sent, is the content of its call at the state after the
submission (`Vegas.sentSourceAction_eq_callContent`). The content of a call
stays the same while the meaning of its handle is fixed
(`Vegas.callContent_keep`).

**Completion content.** A scheduler round completing an event with an actor by
a decoded action that is not failing includes an accepted packet of that actor
naming the event; the decoded action is the content of the packet's call at the
state it is included at, and a commitment's handle belongs to the actor
(`Vegas.completion_content`). Intended actions are never failing
(`Vegas.SourceProgram.ProtocolView.not_failing_of_intendedAvailable`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolView

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **Intended actions are not failing.** An intended commitment commits a
value, and an intended reveal discloses. -/
theorem not_failing_of_intendedAvailable (who : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (view : ProtocolView who program) → (action : OwnAction Player L) →
    action ∈ intendedAvailable who program view → ¬ Failing (some action)
  | _, _, .ret _, _, _, impossible => impossible.elim
  | _, _, .sample _ _ _ next, view, action, member => by
      cases view with
      | inl _ => exact member.elim
      | inr later => exact not_failing_of_intendedAvailable who next later action member
  | _, _, .commit _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          obtain ⟨value, _, rfl⟩ := member
          intro failing
          cases failing.1 _ _ _ _ rfl
      | inr later => exact not_failing_of_intendedAvailable who next later action member
  | _, _, .reveal _ _ _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          rw [Set.mem_singleton_iff.mp member]
          intro failing
          cases failing.2
      | inr later => exact not_failing_of_intendedAvailable who next later action member

end Vegas.SourceProgram.ProtocolView

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- **The content of a call** at a contract state: at a binding event, the
commitment of the value its handle binds there; at a resolve event, the
disclosure; nothing otherwise. -/
def callContent (state : EventGraphRuntime.State (graph setup))
    (call : Payload (graph setup)) : Option (OwnAction Player L) :=
  match call with
  | .commitment event handle =>
      match nodeView (graph setup) event with
      | .bind _ payload outputEq _ =>
          decodeEventAction setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (state.bindingResult handle payload))
      | _ => none
  | .opening event _ _ =>
      match nodeView (graph setup) event with
      | .resolve _ _ _ _ outputEq _ =>
          decodeEventAction setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      | _ => none
  | .malformed _ => none

variable {setup}

/-- The source action a transmission decodes to is the content of its call at
the state after the submission. -/
theorem sentSourceAction_eq_callContent
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (after : (application setup leaks).Execution)
    (material : (application setup leaks).Submission) :
    sentSourceAction setup leaks after ⟨some material⟩ =
      callContent setup after.application material.call.packet := by
  unfold sentSourceAction callContent
  rfl

/-- **Content stays while meanings stay.** If a later state keeps every fixed
meaning, and a commitment's handle has a fixed meaning, the content of the
call is the same at both states. -/
theorem callContent_keep {before after : EventGraphRuntime.State (graph setup)}
    (kept : KeepsFixedCandidates before after) (call : Payload (graph setup))
    (fixed : ∀ event handle, call = .commitment event handle →
      before.candidates.lookup handle ≠ .fresh) :
    callContent setup after call = callContent setup before call := by
  cases call with
  | commitment event handle =>
      have same : after.bindingResult handle = before.bindingResult handle := by
        funext payload
        unfold State.bindingResult
        rw [kept handle (fixed event handle rfl)]
      simp only [callContent, same]
  | opening => rfl
  | malformed => rfl

/-- An accepted commitment completes its event with the binding result of its
handle at the state it is included at, and its handle belongs to its sender. -/
theorem handle_commitment_action (state next : EventGraphRuntime.State (graph setup))
    (id : MessageId Player) (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (accepted : handle (runtime setup) state ⟨id, .commitment event candidate⟩ = some next) :
    candidate.1 = id.1 ∧ ∃ (ready : state.config.cut.Ready event) (owner : Player)
      (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding owner payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .bind owner payload),
      nodeView (graph setup) event = .bind owner payload outputEq codeEq ∧
      next.config = state.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (state.bindingResult candidate payload))
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (state.bindingResult candidate payload)) := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline (runtime setup) event
    · cases view : nodeView (graph setup) event with
      | resolve | sample => simp [handle, ready, timely, view] at accepted
      | bind owner payload outputEq codeEq =>
          simp only [handle, dite_eq_left ready, dite_eq_left timely, view] at accepted
          split at accepted
          · rename_i sender
            split at accepted
            · rename_i handleOwner
              split at accepted
              · split at accepted
                · cases accepted
                  exact ⟨handleOwner.trans sender.symm, ready, owner, payload, outputEq, codeEq,
                    rfl, rfl⟩
                · cases accepted
              · cases accepted
            · cases accepted
          · cases accepted
    · simp [handle, ready, timely] at accepted
  · simp [handle, ready] at accepted

/-- **Completion content.** A scheduler round completing an event with an
actor by a decoded action that is not failing includes an accepted packet of
the actor naming the event. The decoded action is the content of the packet's
call at the state it is included at, and a commitment's handle belongs to the
actor. -/
theorem completion_content
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support)
    {actor : Player} (acts : (graph setup).actor? event = some actor)
    (notFailing : ¬ Failing (decodeEventAction setup.program event action)) :
    ∃ message ∈ next.network.ledger, message.sender = actor ∧
      message.payload.call.event? (graph setup) = some event ∧
      decodeEventAction setup.program event action =
        callContent setup execution.application message.payload.call ∧
      ∀ named candidate, message.payload.call = .commitment named candidate →
        candidate.1 = actor := by
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
                  refine ⟨message, onLedger, Option.some.inj (sender.symm.trans acts),
                    by rw [packet]; rfl, ?_, fun named' candidate' same => ?_⟩
                  · rw [packet]
                    simp only [callContent, view]
                  · rw [packet] at same
                    cases same
                    exact owned.trans (Option.some.inj (sender.symm.trans acts))
              | opening other candidate raw =>
                  rw [packet] at call
                  obtain ⟨otherReady, otherAction, otherMember, _, _, owner, payload, binding,
                    checks, outputEq, codeEq, view, actionEq⟩ :=
                    handle_opening_config_step (runtime setup) execution.application after
                      message.id other candidate raw call
                  cases step_completion_unique otherMember member
                  rw [packet] at named
                  cases Option.some.inj named
                  refine ⟨message, onLedger, Option.some.inj (sender.symm.trans acts),
                    by rw [packet]; rfl, ?_, fun _ _ same => by rw [packet] at same; cases same⟩
                  rw [actionEq, packet]
                  simp only [callContent, view]
  | application command =>
      obtain ⟨changed, _⟩ := applicationStep_facts execution next command reached
      exfalso
      cases command with
      | advanceClock =>
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
                exact (stutter (congrArg (fun state => state.config) changed)).elim
            | resolve _ _ _ _ _ _ =>
                rw [environmentStep_executeSample_of_nonsample (runtime setup) _ event ready
                  (fun _ _ _ _ same => by rw [view] at same; cases same),
                  PMF.mem_support_pure_iff] at changed
                exact (stutter (congrArg (fun state => state.config) changed)).elim
      | expire expired =>
          obtain ⟨_, effect⟩ := environmentStep_expire_config_activated (runtime setup)
            execution.application next.application expired changed
          rcases effect with ⟨configEq, _⟩ | ⟨expiredReady, expiredAction, expiredMember, _⟩
          · exact stutter configEq
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
                rw [actionOf outputEq _ _ changed] at notFailing
                exact notFailing (decodeEventAction_failing_binding setup.program event.val
                  event.isLt outputEq)
            | resolve owner payload binding checks outputEq codeEq =>
                rw [environmentStep_expire_resolve_eq (runtime setup) _ event ready entered
                  activated due owner payload binding checks outputEq codeEq view,
                  PMF.mem_support_pure_iff] at changed
                rw [actionOf outputEq _ _ changed] at notFailing
                exact notFailing (decodeEventAction_failing_publication setup.program event.val
                  event.isLt outputEq)

end Vegas
