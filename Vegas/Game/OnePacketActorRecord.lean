/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFreshSlots

/-! # Completed events with an actor and the silence of other players

**Failing completions owe a failure.** A source action that commits a failed
binding or withholds a disclosure is *failing* (`Vegas.SourceProgram.Failing`).
The decoded action of a binding event completed with failure, or of a
publication event completed with withholding, is failing
(`Vegas.SourceProgram.decodeEventAction_failing_binding`,
`Vegas.SourceProgram.decodeEventAction_failing_publication`). Stepping a decoded
point with a failing action at the event of a player makes that player owe a
failure (`Vegas.SourceProgram.ProtocolState.owesFailure_of_decode_failing`).

**The actor record.** A scheduler command completes an event with an actor
either by including an accepted packet of that actor naming it, or with a
failing decoded action, as at an expiry (`Vegas.actor_completion_cause`). So at
every legal history of the default runtime, under arbitrary responses and
every scheduler, every completed event with an actor was completed by an
accepted packet of its actor, or that actor owes a failure at the decoded point
(`Vegas.actorRecord_history`).

**Silence of the others.** Hence, at a history of the one-packet game in a
forced state of an event's actor, while that event is ready, every one-packet
response of another player keeps silence (`Vegas.onePacket_silent_of_pending`):
a packet for a later event has no readiness token, and a packet for one of the
player's own completed events is a second packet for it.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source action that commits a failed binding or does not disclose. -/
def Failing (choice : Option (OwnAction Player L)) : Prop :=
  (∀ owner name payload result, choice = some (.commit owner name payload result) →
    result = .failure) ∧ OwnAction.disclosure choice = false

/-- The decoded action of a binding event completed with a failed binding is
failing. -/
theorem decodeEventAction_failing_binding {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (bound : count < eventCount program) {owner : Player} {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .binding owner payload),
      Failing (decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))) := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound owner payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | commit name commitOwner fresh guard next ih =>
      intro count bound owner payload outputEq
      cases count with
      | zero =>
          change EventGraph.EventField.binding commitOwner _ = _ at outputEq
          obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj outputEq
          refine ⟨fun actor actorName actorPayload result chosen => ?_, rfl⟩
          cases chosen
          rfl
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound owner payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq

/-- The decoded action of a publication event completed with withholding is
failing. -/
theorem decodeEventAction_failing_publication {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (bound : count < eventCount program) {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .publication payload),
      Failing (decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)) := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | commit name commitOwner fresh guard next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound payload outputEq
      cases count with
      | zero =>
          refine ⟨fun actor actorName actorPayload result chosen => ?_, rfl⟩
          cases Option.some.inj chosen
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq

namespace ProtocolState

/-- **A failing completion makes its actor owe a failure.** At a point decoded
after `count` events, stepping with a failing action at the event of index
`count`, owned by `who`, makes `who` owe a failure. -/
theorem owesFailure_of_decode_failing {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    (Γ.map Prod.fst).Nodup → ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) (who : Player)
      (choice : Option (OwnAction Player L)) (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
          some state →
      eventOwner? program ⟨count, bound⟩ = some who → Failing choice →
      target ∈ (step program state (fun _ => choice)).support →
      OwesFailure who program target := by
  induction program with
  | ret _ =>
      intro _ count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro unique count refs registry revelations outputs store history state bound who choice
        target decoded owned failing reached
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history rest
            (Nat.lt_of_succ_lt_succ bound) who choice after read owned failing supported
  | @commit commitCtx commitNames name owner payload fresh guard next ih =>
      intro unique count refs registry revelations outputs store history state bound who choice
        target decoded owned failing reached
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          have failed : OwnAction.binding owner name payload choice = .failure := by
            unfold OwnAction.binding
            split
            · rename_i found
              exact failing.1 _ _ _ _ found.choose_spec
            · rfl
          refine Or.inr ?_
          change FailedBinding owner next (entry next _)
          rw [failed]
          exact failedBinding_entry next _
            (Config.failedBinding_commit _ unique fresh guard commitNames)
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history rest
            (Nat.lt_of_succ_lt_succ bound) who choice after read owned failing supported
  | reveal published owner name fresh source unresolved next ih =>
      intro unique count refs registry revelations outputs store history state bound who choice
        target decoded owned failing reached
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same : target = Sum.inr (entry next (revealSuccessor published source
              ⟨cells, registry, revelations, history⟩ (OwnAction.disclosure choice))) :=
            (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          refine Or.inl (Or.inl ⟨rfl, ?_⟩)
          rw [base_entry, failing.2]
          exact disclosureResult_false published source _
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history rest
            (Nat.lt_of_succ_lt_succ bound) who choice after read owned failing supported with
            indebted | failed
          · exact Or.inl (Or.inr indebted)
          · exact Or.inr (Or.inr failed)

end ProtocolState

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **How an event with an actor completes.** When a scheduler command completes
an event with an actor, either an included packet of that actor naming the
event was accepted, or the decoded action of the completion is failing, as at an
expired binding or reveal. -/
theorem actor_completion_cause (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support)
    {actor : Player} (acts : (graph setup).actor? event = some actor) :
    (∃ message ∈ next.network.ledger, (message.id, true) ∈ next.receipts ∧
        message.payload.call.event? (graph setup) = some event ∧ message.sender = actor) ∨
      Failing (decodeEventAction setup.program event action) := by
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
      left
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change (execution.includePending (application setup leaks) id).application.config ∈ _
        at member
      change ∃ message ∈ (execution.includePending (application setup leaks) id).network.ledger,
        (message.id, true) ∈ (execution.includePending (application setup leaks) id).receipts ∧ _
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
              have receiptsEq : (execution.includePending (application setup leaks) id).receipts =
                  execution.receipts ++ [(id, true)] := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.isSome_some]
              have networkEq : (execution.includePending (application setup leaks) id).network =
                  (execution.network.includePending id).2 :=
                (application setup leaks).includePending_network execution id
              obtain ⟨_, namedEvent, named, _, _, sender⟩ :=
                accepted_inclusion execution.application after message accepted
              obtain ⟨other, otherNamed, _, _, otherMember⟩ :=
                handle_config_mem_step (runtime setup) execution.application after _
                  (reactiveHandle_call accepted)
              have sameNamed : other = namedEvent := Option.some.inj (otherNamed.symm.trans named)
              subst sameNamed
              rw [applicationEq] at member
              cases step_completion_unique otherMember member
              refine ⟨message, ?_, ?_, named, Option.some.inj (sender.symm.trans acts)⟩
              · rw [networkEq, ledgerEq]
                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
              · rw [receiptsEq, identified]
                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  | application command =>
      obtain ⟨changed, _⟩ := applicationStep_facts execution next command reached
      right
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

/-- **The actor record.** The configuration decodes at a prefix, and every
completed event with an actor was completed by an accepted packet of that actor
naming it, or that actor owes a failure at the decoded point. -/
def ActorRecord (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    ∀ event ∈ execution.application.config.cut.completed, ∀ actor,
      (graph setup).actor? event = some actor →
        (∃ message ∈ execution.network.ledger, (message.id, true) ∈ execution.receipts ∧
          message.payload.call.event? (graph setup) = some event ∧ message.sender = actor) ∨
        DecodedHolds (ProtocolState.OwesFailure actor setup.program) rank
          execution.application.config

/-- The actor record holds at every legal history of the default runtime, under
arbitrary responses and every scheduler. -/
theorem actorRecord_serviceInvariant (profile : BehavioralProfile setup.program)
    (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler (ActorRecord profile) where
  respond execution who action valid := by
    have configEq := ((runtime setup).reactive_respond_application leaks execution who action).1
    have ledgerEq := (application setup leaks).respond_ledger execution who action
    have receiptsEq := (application setup leaks).respond_receipts execution who action
    unfold ActorRecord at valid ⊢
    rw [configEq, ledgerEq, receiptsEq]
    exact valid
  environment execution next command valid _ reached := by
    obtain ⟨rank, ⟨residual⟩, record⟩ := valid
    have grows := environment_ledger_receipts_grow execution next command reached
    rcases environmentStep_configStep setup leaks execution next command reached with
      same | ⟨event, ready, action, member⟩
    · refine ⟨rank, ?_, fun other completed actor acts => ?_⟩
      · rw [same]
        exact ⟨residual⟩
      · rw [same] at completed ⊢
        rcases record other completed actor acts with
          ⟨message, present, receipt, named, sender⟩ | owed
        · exact Or.inl ⟨message, grows.1 message present, grows.2 _ receipt, named, sender⟩
        · exact Or.inr owed
    · have rankEq : event.val = rank :=
        (ready_iff_rank setup _ rank residual.checkpoint.ordered event).mp ready
      obtain ⟨successor, reachedPoint⟩ := residual.step event ready action _ member
      have advanced : next.application.config.cut.IsPrefix (rank + 1) := by
        rw [execution.application.config.step_cut event ready action _ member]
        exact residual.checkpoint.ordered.complete_at event ready rankEq
      refine ⟨rank + 1, ⟨successor⟩, fun other completed actor acts => ?_⟩
      rw [execution.application.config.step_cut event ready action _ member,
        EventOrder.Cut.mem_complete] at completed
      rcases completed with rfl | earlier
      · rcases actor_completion_cause execution next command reached ready action member acts with
          accepted | failing
        · exact Or.inl accepted
        · right
          intro state decoded
          rw [successor.decode] at decoded
          obtain rfl := Option.some.inj decoded
          have decodedBefore := residual.decode
          generalize residual.lift (ProtocolState.entry residual.program residual.source) =
            point at decodedBefore reachedPoint
          rw [← rankEq] at decodedBefore
          have owned : eventOwner? setup.program ⟨other.val, other.isLt⟩ = some actor := by
            rw [eventOwner?_eq_actor]
            exact acts
          exact ProtocolState.owesFailure_of_decode_failing setup.program setup.namesNodup
            other.val _ _ _ _ _ _ point other.isLt actor _ _ decodedBefore owned failing
            reachedPoint
      · rcases record other earlier actor acts with
          ⟨message, present, receipt, named, sender⟩ | owed
        · exact Or.inl ⟨message, grows.1 message present, grows.2 _ receipt, named, sender⟩
        · exact Or.inr (residual.decodedHolds_configStep (fun state joint target owing reached =>
            ProtocolState.owesFailure_step actor setup.program state joint target owing reached)
            owed
            (Or.inr ⟨event, ready, action, member⟩) advanced)

/-- The actor record holds at every legal history of the default runtime from
its initial law. -/
theorem actorRecord_history (profile : BehavioralProfile setup.program) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    ActorRecord profile control.execution :=
  (actorRecord_serviceInvariant profile scheduler).history (initialLaw setup) horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      let residual := SourceResidual.initial setup profile initial
      refine ⟨0, ⟨residual⟩, fun event completed => ?_⟩
      have below := (residual.checkpoint.ordered.2 event).mp completed
      exact absurd below (Nat.not_lt_zero _)) trace

/-- The event a permitted call names has its sender as actor. -/
theorem countCallCorrect_actor (earlier : Message Player (WitnessedPacket (graph setup)) → Prop)
    (message : Message Player (WitnessedPacket (graph setup)))
    (correct : CountCallCorrect earlier message) {event : (graph setup).EventId}
    (named : message.payload.call.event? (graph setup) = some event) :
    (graph setup).actor? event = some message.sender := by
  unfold CountCallCorrect at correct
  cases call : message.payload.call with
  | malformed raw =>
      rw [call] at named
      cases named
  | commitment named' handle =>
      rw [call] at named correct
      cases named
      have owned := correct.1
      unfold bindingOwnedBy at owned
      cases view : nodeView (graph setup) event with
      | bind owner payload outputEq codeEq =>
          rw [outputEq] at owned
          have same : owner = message.sender := of_decide_eq_true owned
          rw [← same]
          exact nodeView_bind_actor outputEq codeEq
      | resolve owner payload binding checks outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
      | sample payload law outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
  | opening named' handle raw =>
      rw [call] at named correct
      cases named
      obtain ⟨_, owned⟩ := correct
      cases view : nodeView (graph setup) event with
      | resolve owner payload binding checks outputEq codeEq =>
          rw [view] at owned
          rw [owned.1]
          exact nodeView_resolve_actor outputEq codeEq
      | bind _ _ _ _ =>
          rw [view] at owned
          exact owned.elim
      | sample _ _ _ _ =>
          rw [view] at owned
          exact owned.elim

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **Other players are silent while an event is pending.** At a history of the
one-packet game in a forced state of `owner`, while an event of `owner` is
ready, every one-packet response of another player keeps silence. A packet for
a later event has no readiness token, and a packet for one of the player's own
completed events is a second packet for it: on a forced history its event was
completed by an accepted packet of the player, since otherwise it would owe a
failure. -/
theorem onePacket_silent_of_pending (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (owner : Player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (forced : ForcedState setup leaks owner history.state)
    {control : (application setup leaks).Control} (current : history.state = some control)
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner) (other : Player) (different : other ≠ owner)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks other
      (control.execution.recall other)
      (control.execution.observe (application setup leaks) other)) :
    response.transmission = none := by
  let app := application setup leaks
  rcases ((bounds.mem_onePacketActions (runtime setup) leaks other _ _ response).mp member).2 with
    silent | ⟨material, _, permitted⟩
  · exact silent
  exfalso
  have trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
    current ▸ (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.trace
  rw [current] at forced
  obtain ⟨rank, point, ordered, decoded, forcedPoint⟩ := forced
  obtain ⟨inputRecall, serialRecall, _⟩ := (runtime setup).countRecall_history leaks trace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
  obtain ⟨recordRank, ⟨residual⟩, record⟩ :=
    actorRecord_history (failureProfile setup.program) horizon scheduler trace
  have sameRank := isPrefix_unique ordered residual.checkpoint.ordered
  subst sameRank
  set envelope := (runtime setup).localEnvelope leaks other (control.execution.recall other)
    (control.execution.observe app other) material with envelopeEq
  obtain ⟨tokenValid, correct, first⟩ := (countPermits_eq_true_iff _ _).mp permitted
  obtain ⟨named, namedEvent, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp tokenValid
  have sender : envelope.sender = other := rfl
  have actor := countCallCorrect_actor _ envelope correct namedEvent
  rw [sender] at actor
  have issued : ∀ predecessor ∈ (graph setup).order.predecessors named,
      predecessor ∈ control.execution.application.config.cut.completed := by
    have token : control.execution.application.publicView.tokenFor envelope.payload.call =
        some ⟨named⟩ := tokenEq
    unfold PublicView.tokenFor at token
    rw [namedEvent, Option.bind_some] at token
    obtain ⟨_, complete⟩ := (PublicView.readinessToken?_eq_some_iff _ named ⟨named⟩).mp token
    intro predecessor member
    exact (control.execution.application.config.history_exact predecessor).mp
      (complete predecessor member)
  have completed : named ∈ control.execution.application.config.cut.completed := by
    by_contra open_
    have same := ready_unique (setup := setup) _ ⟨open_, fun predecessor member =>
      issued predecessor member⟩ ready
    subst same
    exact different (Option.some.inj (actor.symm.trans owned))
  rcases record named completed other actor with
    ⟨message, onLedger, _, messageNamed, messageSender⟩ | owed
  · have emitted : message ∈ control.execution.network.inputs :=
      facts.carried.ledger message onLedger
    have recalled : message ∈ app.outputs (control.execution.recall other) := by
      rw [← inputRecall other]
      exact List.mem_filter.mpr ⟨emitted, by simp [messageSender]⟩
    have lower : message.id.2 < envelope.id.2 := by
      have bound := facts.serials.inputs message emitted
      change message.id.2 < control.execution.network.nextSerial message.sender at bound
      rw [messageSender, serialRecall other] at bound
      exact bound
    exact first message ⟨recalled, messageSender.trans sender.symm, lower⟩
      (messageNamed.trans namedEvent.symm)
  · exact ((forcedPoint.2 other different).2) (owed point decoded)

end Vegas
