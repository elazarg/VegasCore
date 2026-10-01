/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterAsync
import Vegas.Pending.ReactiveEntryStability
import Vegas.Pending.ReactiveFreshCallAcceptance
import Interaction.ReactiveMessageIdentity

/-! # An acceptable fresh call settles in time under the asynchronous contract

An owner emits a fresh call for its ready event within `delay` slots of the
event becoming ready, acceptable on the view it saw (the handler's part of the
audit's public conformance rule), and emits no other identifier for the
event. Under the asynchronous contract with `delay + bound < deadline`, that
call is accepted, and the event completes only through it: it is never
rejected and the event never expires first (`Vegas.prescribed_packet_settles`).

The proof is one invariant over every legal history, for every scheduler and
arbitrary responses of everyone else. While the event is unfinished no event
completes on the sequentialized graph, so the public view the owner saw stays
current. An inclusion before `sent + bound` is then within the deadline and is
accepted. An expiry or a late inclusion needs a clock past `sent + bound`,
where protected inclusion has already produced a receipt.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Handle

variable {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)

/-- An accepted packet is authored by its event's actor. -/
theorem handle_sender_actor (state next : EventGraphRuntime.State graph)
    (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) (event : graph.EventId)
    (named : Payload.event? graph message.payload = some event) :
    graph.actor? event = some message.sender := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              by_cases sender : id.1 = owner
              · exact (nodeView_bind_actor outputEq codeEq).trans (congrArg some sender.symm)
              · simp [handle, ready, timely, view, Message.sender, sender] at accepted
          | resolve owner payload binding checks outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | opening actual candidate raw =>
      change some actual = some event at named
      cases Option.some.inj named
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | resolve owner payload binding checks outputEq codeEq =>
              by_cases sender : id.1 = owner
              · exact (nodeView_resolve_actor outputEq codeEq).trans (congrArg some sender.symm)
              · simp [handle, ready, timely, view, Message.sender, sender] at accepted
          | bind owner payload outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | withhold actual =>
      change some actual = some event at named
      cases Option.some.inj named
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | resolve owner payload binding checks outputEq codeEq =>
              by_cases sender : id.1 = owner
              · exact (nodeView_resolve_actor outputEq codeEq).trans (congrArg some sender.symm)
              · simp [handle, ready, timely, view, Message.sender, sender] at accepted
          | bind owner payload outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted

end Handle

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- A fresh call the handler accepts when included in time: the acceptance part
of the audit's public conformance rule, evaluated on the view its author saw
when emitting it. -/
def AcceptableFreshCall (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) : Prop :=
  (runtime setup).freshServiceAcceptable entry.beforeView.application.publicView message

/-- One recorded fresh call of `owner` for `event`: a fresh submission, sent
while the event was ready and at most `delay event` slots after it became
ready, and acceptable on the view its author saw. -/
structure FreshCall (owner : Player) (event : (graph setup).EventId)
    (delay : (graph setup).EventId → Nat) (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) : Prop where
  fresh : ∃ material, entry.action.transmission = some (.submit material)
  emitted : entry.emitted = some message
  authored : message.sender = owner
  addressed : message.payload.call.event? (graph setup) = some event
  ready : entry.beforeView.application.publicView.EventReady event
  early : ∃ entered, entry.beforeView.application.publicView.activatedAt event = some entered ∧
    entry.beforeView.application.publicView.clock ≤ entered + delay event
  conforming : AcceptableFreshCall setup leaks entry message

/-- An event completes only together with an accepting receipt for `id`, and
every receipt for `id` is accompanied by an accepting one. -/
def Settled (event : (graph setup).EventId) (id : MessageId Player)
    (execution : (application setup leaks).Execution) : Prop :=
  (event ∈ execution.application.config.cut.completed → (id, true) ∈ execution.receipts) ∧
    (∀ accepted, (id, accepted) ∈ execution.receipts → (id, true) ∈ execution.receipts) ∧
    ((id, true) ∈ execution.receipts → event ∈ execution.application.config.cut.completed)

/-- Every recorded fresh call of `owner` for `event`, with no other identifier
emitted by `owner` for the event, is settled. -/
def SettlesFreshCalls (owner : Player) (event : (graph setup).EventId)
    (delay : (graph setup).EventId → Nat) (execution : (application setup leaks).Execution) :
    Prop :=
  ∀ earlier entry later message, execution.recall owner = earlier ++ entry :: later →
    FreshCall setup leaks owner event delay entry message →
    (∀ other ∈ earlier ++ later, ¬ EmitsOtherFor (runtime setup) leaks other event message.id) →
    Settled setup leaks event message.id execution

/-- On the sequentialized graph, a view that saw `event` ready agrees on the
completion order with any later state where `event` is still unfinished. -/
theorem sequential_order_eq (view : PublicView (graph setup))
    (state : EventGraphRuntime.State (graph setup)) (event : (graph setup).EventId)
    (ready : view.EventReady event)
    (prefixOf : view.observation.completionOrder <+: state.publicView.observation.completionOrder)
    (unfinished : event ∉ state.config.cut.completed) :
    view.observation.completionOrder = state.publicView.observation.completionOrder := by
  obtain ⟨rest, split⟩ := prefixOf
  cases rest with
  | nil => simpa using split
  | cons extra rest =>
      exfalso
      have orderEq : state.publicView.observation.completionOrder =
          state.config.history.map EventGraph.Completion.event := rfl
      have member : extra ∈ state.config.history.map EventGraph.Completion.event := by
        rw [← orderEq, ← split]
        simp
      have completed := (state.config.history_exact extra).mp member
      rcases lt_trichotomy extra.val event.val with earlier | same | later
      · have seen : extra ∈ view.observation.completionOrder :=
          ready.2 extra (Finset.mem_filter.mpr ⟨Finset.mem_univ _, earlier⟩)
        have nodup := state.config.history_nodup
        rw [← orderEq, ← split] at nodup
        exact (List.nodup_append.mp nodup).2.2 extra seen extra (List.mem_cons_self) rfl
      · exact unfinished (Fin.ext same ▸ completed)
      · exact unfinished (state.config.cut.predecessor_closed completed
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, later⟩))

/-- A recorded response that saw `event` ready, at a state where `event` is
still unfinished, saw the current public observation, accepted handles and
activation times. -/
theorem entry_view_current (execution : (application setup leaks).Execution)
    (stable : EntryStable (runtime setup) leaks execution) (who : Player)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ execution.recall who)
    (event : (graph setup).EventId)
    (ready : entry.beforeView.application.publicView.EventReady event)
    (unfinished : event ∉ execution.application.config.cut.completed) :
    entry.beforeView.application.publicView.observation =
        execution.application.publicView.observation ∧
      entry.beforeView.application.publicView.accepted = execution.application.accepted ∧
      entry.beforeView.application.publicView.activatedAt = execution.application.activatedAt := by
  obtain ⟨prefixOf, current⟩ := stable who entry member
  exact current (sequential_order_eq setup _ execution.application event ready prefixOf unfinished)

omit [DecidableEq Player] in
private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ R left right →
      ∀ b ∈ right, ∃ a ∈ left, R a b
  | [], [], .nil, _, member => by simp at member
  | a :: left, b :: right, .cons head tail, x, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨a, List.mem_cons_self, head⟩
      · obtain ⟨y, inside, related⟩ := forall₂_mem_right tail x member
        exact ⟨y, List.mem_cons_of_mem _ inside, related⟩

/-- No receipt names an identifier not yet allocated. -/
theorem no_receipt_next (execution : (application setup leaks).Execution)
    (sound : execution.ReceiptsSound (application setup leaks) (fun _ => True))
    (serials : execution.network.SerialsBeforeNext) (who : Player) (accepted : Bool) :
    ((who, execution.network.nextSerial who), accepted) ∉ execution.receipts := by
  intro member
  obtain ⟨message, published, same, _⟩ := forall₂_mem_right sound _ member
  have bound := serials.ledger message published
  rw [← same] at bound
  exact Nat.lt_irrefl _ bound

/-- The entry a response appends to its author's recall. A fresh submission
emits the author's next identifier. -/
theorem respond_recall_self (execution : (application setup leaks).Execution) (who : Player)
    (action : (application setup leaks).Action) :
    ∃ emitted, (execution.respond (application setup leaks) who action).recall who =
        execution.recall who ++
          [⟨execution.observe (application setup leaks) who, action, emitted⟩] ∧
      ∀ material, action.transmission = some (.submit material) → ∀ message,
        emitted = some message → message.id = (who, execution.network.nextSerial who) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      exact ⟨none, by simp [ReactiveApplication.Execution.respond], by simp⟩
  | some transmission =>
      cases transmission with
      | submit material =>
          refine ⟨some (execution.network.submit who ((application setup leaks).packet
            ((application setup leaks).submit execution.application who material) who
            (execution.network.known who) material)).1,
            by simp only [ReactiveApplication.Execution.respond, ↓reduceIte], ?_⟩
          rintro _ ⟨⟩ message ⟨⟩
          rfl
      | replay id =>
          exact ⟨(execution.network.replay who id).1,
            by simp only [ReactiveApplication.Execution.respond, ↓reduceIte], by simp⟩

/-- Completed events stay completed across a public step. -/
theorem PublicStep.completed_mono {before after : EventGraphRuntime.State (graph setup)}
    (step : PublicStep before after) :
    before.config.cut.completed ⊆ after.config.cut.completed := by
  intro event member
  rcases step with ⟨configEq, _, _⟩ | ⟨completion, historyEq⟩
  · rw [configEq]
    exact member
  · apply (after.config.history_exact event).mp
    rw [historyEq, List.map_append]
    exact List.mem_append_left _ ((before.config.history_exact event).mpr member)

/-- The facts at a legal history that the settlement invariant uses. -/
structure LegalFacts (execution : (application setup leaks).Execution) : Prop where
  stable : EntryStable (runtime setup) leaks execution
  binding : execution.application.BindingInvariant
  evidence : ((runtime setup).packetEvidence leaks).Sound execution
  receipts : execution.ReceiptsSound (application setup leaks) (fun _ => True)
  serials : execution.network.SerialsBeforeNext
  unique : execution.network.UniqueIds
  provenance : execution.Provenance (application setup leaks)
  inputs : execution.InputRecall (application setup leaks)

theorem legalFacts (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    LegalFacts setup leaks control.execution := by
  obtain ⟨_, provenance, inputs, _, receipts⟩ :=
    roster_trace_facts setup leaks horizon scheduler trace
  exact {
    stable := entryStable_history (runtime setup) leaks (initialLaw setup) horizon scheduler trace
    binding := ((runtime setup).reactiveBindingInvariant leaks).history (initialLaw setup) horizon
      scheduler (fun state member => by
        obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
        exact State.initial_bindingInvariant _) trace
    evidence := ((runtime setup).packetEvidence leaks).history_sound (initialLaw setup) horizon
      scheduler trace
    receipts := receipts
    serials := (application setup leaks).serialsBeforeNext_history scheduler (initialLaw setup)
      horizon trace
    unique := (application setup leaks).uniqueIds_history scheduler (initialLaw setup) horizon
      control trace
    provenance := provenance
    inputs := inputs }

private theorem settled_congr {event : (graph setup).EventId} {id : MessageId Player}
    {before after : (application setup leaks).Execution}
    (configEq : after.application.config = before.application.config)
    (receiptsEq : after.receipts = before.receipts)
    (settled : Settled setup leaks event id before) : Settled setup leaks event id after := by
  unfold Settled
  rw [configEq, receiptsEq]
  exact settled

/-- A response preserves the settlement invariant. -/
theorem settlesFreshCalls_respond (owner : Player) (event : (graph setup).EventId)
    (delay : (graph setup).EventId → Nat) (execution : (application setup leaks).Execution)
    (facts : LegalFacts setup leaks execution) (who : Player)
    (action : (application setup leaks).Action)
    (valid : SettlesFreshCalls setup leaks owner event delay execution) :
    SettlesFreshCalls setup leaks owner event delay
      (execution.respond (application setup leaks) who action) := by
  let app := application setup leaks
  have configEq := ((runtime setup).reactive_respond_application leaks execution who action).1
  have receiptsEq := app.respond_receipts execution who action
  intro earlier entry later message split call sole
  apply settled_congr setup leaks configEq receiptsEq
  by_cases same : who = owner
  · subst who
    obtain ⟨emitted, recallEq, idOf⟩ := respond_recall_self setup leaks execution owner action
    rw [recallEq] at split
    rcases List.eq_nil_or_concat later with rfl | ⟨init, last, rfl⟩
    · obtain ⟨_, entryEq⟩ := List.append_inj' split rfl
      have newEntry := (List.singleton_inj.mp entryEq).symm
      subst newEntry
      obtain ⟨material, submitted⟩ := call.fresh
      have idEq := idOf material submitted message call.emitted
      have readyNow : execution.application.config.cut.Ready event :=
        (execution.application.publicView_eventReady event).mp call.ready
      refine ⟨fun finished => (readyNow.1 finished).elim, fun accepted member => ?_,
        fun member => ?_⟩
      · rw [idEq] at member
        exact (no_receipt_next setup leaks execution facts.receipts facts.serials owner accepted
          member).elim
      · rw [idEq] at member
        exact (no_receipt_next setup leaks execution facts.receipts facts.serials owner true
          member).elim
    · simp only [List.concat_eq_append] at split sole
      have reassociated : earlier ++ entry :: (init ++ [last]) =
          (earlier ++ entry :: init) ++ [last] := by simp
      rw [reassociated] at split
      obtain ⟨older, _⟩ := List.append_inj' split rfl
      exact valid earlier entry init message older call fun other member =>
        sole other (by
          rcases List.mem_append.mp member with inside | inside
          · exact List.mem_append_left _ inside
          · exact List.mem_append_right _ (List.mem_append_left _ inside))
  · rw [app.respond_recall_other execution who owner (Ne.symm same) action] at split
    exact valid earlier entry later message split call sole

/-- A scheduler command preserves the settlement invariant under the contract. -/
theorem settlesFreshCalls_environment {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (prior : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (valid : SettlesFreshCalls setup leaks owner event delay execution)
    (command : (application setup leaks).Command) (next : (application setup leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    SettlesFreshCalls setup leaks owner event delay next := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler _ prior
  have recallEq := app.environmentStep_recall execution next command reached
  have publicStep := publicStep_reactive_environmentStep (runtime setup) leaks execution next
    command reached
  have mono := PublicStep.completed_mono setup publicStep
  intro earlier entry later message split call sole
  rw [recallEq] at split
  have before := valid earlier entry later message split call sole
  have member : entry ∈ execution.recall owner := by rw [split]; simp
  obtain ⟨entered, activated, early⟩ := call.early
  have bounded := timely event (by rw [owned]; rfl)
  -- Before the bound has passed the event is still timely; after it, a receipt exists.
  have notLate (unfinished : event ∉ execution.application.config.cut.completed) :
      execution.application.clock ≤
        entry.beforeView.application.publicView.clock + bound event := by
    by_contra late
    obtain ⟨accepted, receipt⟩ := contract.inclusion ⟨remaining + 1, none, execution⟩ prior event
      owner owned earlier later entry message split call.emitted call.authored call.addressed
      call.ready sole unfinished (by change _ < execution.application.clock; omega)
    exact unfinished (before.2.2 (before.2.1 accepted receipt))
  have current (unfinished : event ∉ execution.application.config.cut.completed) :=
    entry_view_current setup leaks execution facts.stable owner entry member event call.ready
      unfinished
  have activatedNow (unfinished : event ∉ execution.application.config.cut.completed) :
      execution.application.activatedAt event = some entered := by
    rw [← (current unfinished).2.2]
    exact activated
  have withinDeadline (unfinished : event ∉ execution.application.config.cut.completed) :
      execution.application.WithinDeadline (runtime setup) event := by
    have clockBound := notLate unfinished
    unfold State.WithinDeadline
    rw [activatedNow unfinished]
    change execution.application.clock - entered < (runtime setup).deadline event
    omega
  -- The settlement facts carry over whenever receipts only grow by unrelated or
  -- accepting entries and the event is not newly completed without acceptance.
  by_cases finished : event ∈ execution.application.config.cut.completed
  · have accepted := before.1 finished
    unfold ReactiveApplication.Execution.environmentStep at reached
    rw [PMF.support_map] at reached
    obtain ⟨updated, supported, rfl⟩ := reached
    have kept : (message.id, true) ∈ updated.receipts := by
      cases command with
      | activate who =>
          rw [PMF.support_map] at supported
          obtain ⟨_, _, rfl⟩ := supported
          exact accepted
      | wait =>
          cases (PMF.mem_support_pure_iff _ _).mp supported
          exact accepted
      | «include» id =>
          cases (PMF.mem_support_pure_iff _ _).mp supported
          unfold ReactiveApplication.Execution.includePending
          cases execution.network.includePending id with
          | mk envelope network =>
              cases envelope with
              | none => exact accepted
              | some envelope => exact List.mem_append_left _ accepted
      | application command =>
          rw [PMF.support_map] at supported
          obtain ⟨_, _, rfl⟩ := supported
          exact accepted
    exact ⟨fun _ => kept, fun _ _ => kept, fun _ => mono finished⟩
  · -- The event is unfinished before the command.
    have viewObservation := (current finished).1
    have viewAccepted := (current finished).2.1
    unfold ReactiveApplication.Execution.environmentStep at reached
    rw [PMF.support_map] at reached
    obtain ⟨updated, supported, rfl⟩ := reached
    cases command with
    | activate who =>
        rw [PMF.support_map] at supported
        obtain ⟨_, _, rfl⟩ := supported
        exact before
    | wait =>
        cases (PMF.mem_support_pure_iff _ _).mp supported
        exact before
    | «include» id =>
        cases (PMF.mem_support_pure_iff _ _).mp supported
        change Settled setup leaks event message.id
          { (execution.includePending app id) with
            environmentRecall := execution.environmentRecall ++
              [⟨execution.observeEnvironment app, .include id⟩] }
        unfold Settled ReactiveApplication.Execution.includePending
        unfold MessageNetwork.includePending
        cases found : execution.network.lookup id with
        | none => exact before
        | some envelope =>
            have pending : envelope ∈ execution.network.pending :=
              List.mem_of_find?_eq_some found
            have envelopeId : envelope.id = id := by
              simpa using List.find?_some found
            dsimp only
            by_cases sameId : id = message.id
            · -- The included envelope is the owner's fresh call itself.
              have output : message ∈ app.outputs (execution.recall owner) :=
                List.mem_filterMap.mpr ⟨entry, member, call.emitted⟩
              rw [← facts.inputs owner] at output
              obtain ⟨input, inputMember, inputEq⟩ := List.mem_filterMap.mp output
              have envelopeEq : envelope = message := by
                by_cases broadcaster : input.broadcaster = owner
                · simp only [broadcaster, ↓reduceIte, Option.some.injEq] at inputEq
                  have unique := facts.unique.inputs input inputMember
                  rw [inputEq] at unique
                  exact unique.pending envelope pending (envelopeId.trans sameId)
                · simp [broadcaster] at inputEq
              subst envelopeEq
              obtain ⟨accepted, handled⟩ := freshServiceAcceptable_accepted (runtime setup)
                execution.application entry.beforeView.application.publicView envelope
                call.conforming viewObservation viewAccepted
                event call.addressed (withinDeadline finished)
                (fun fact fact_member => facts.evidence.pending envelope pending fact fact_member)
                facts.binding
              change app.handle execution.application envelope = some accepted at handled
              rw [handled]
              obtain ⟨named, namedEq, ready, action, stepped⟩ :=
                handle_config_mem_step (runtime setup) _ _ _ handled
              have namedIs : named = event := Option.some.inj (namedEq.symm.trans call.addressed)
              subst namedIs
              have completed : named ∈ accepted.config.cut.completed := by
                rw [execution.application.config.step_cut named ready action _ stepped]
                exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
              rw [← sameId]
              have receipt : (id, true) ∈ execution.receipts ++
                  [(id, (some accepted).isSome)] :=
                List.mem_append_right _ (List.mem_singleton_self _)
              exact ⟨fun _ => receipt, fun _ _ => receipt, fun _ => completed⟩
            · -- Another envelope cannot complete the event, and leaves our receipts alone.
              have otherReceipt (accepted : Bool)
                  (receipt : (message.id, accepted) ∈ execution.receipts ++
                    [(id, (app.handle execution.application envelope).isSome)]) :
                  (message.id, accepted) ∈ execution.receipts := by
                rcases List.mem_append.mp receipt with old | new
                · exact old
                · exact (sameId (Prod.mk.inj (List.mem_singleton.mp new)).1.symm).elim
              have notCompleted : event ∉ ((app.handle execution.application envelope).getD
                  execution.application).config.cut.completed := by
                cases handled : app.handle execution.application envelope with
                | none => exact finished
                | some accepted =>
                    intro completedNow
                    obtain ⟨named, namedEq, ready, action, stepped⟩ :=
                      handle_config_mem_step (runtime setup) _ _ _ handled
                    have afterCut := execution.application.config.step_cut named ready action _
                      stepped
                    change event ∈ accepted.config.cut.completed at completedNow
                    rw [afterCut, EventOrder.Cut.mem_complete] at completedNow
                    rcases completedNow with rfl | old
                    · have sender := handle_sender_actor (runtime setup) _ _ _ handled event
                        namedEq
                      rw [owned] at sender
                      have senderEq : envelope.sender = owner := (Option.some.inj sender).symm
                      obtain ⟨issuer, issuerMember, material, submitted, issued, _⟩ :=
                        facts.provenance.pending envelope pending
                      rw [senderEq, split] at issuerMember
                      have different : issuer ≠ entry := by
                        rintro rfl
                        rw [call.emitted] at issued
                        exact sameId ((Option.some.inj issued) ▸ envelopeId).symm
                      have elsewhere : issuer ∈ earlier ++ later := by
                        rcases List.mem_append.mp issuerMember with inside | inside
                        · exact List.mem_append_left _ inside
                        · rcases List.mem_cons.mp inside with rfl | inside
                          · exact (different rfl).elim
                          · exact List.mem_append_right _ inside
                      exact sole issuer elsewhere ⟨envelope, issued, namedEq,
                        fun equal => sameId (envelopeId.symm.trans equal)⟩
                    · exact finished old
              exact ⟨fun completedNow => (notCompleted completedNow).elim,
                fun accepted receipt => List.mem_append_left _
                  (before.2.1 accepted (otherReceipt accepted receipt)),
                fun receipt => (finished (before.2.2 (otherReceipt true receipt))).elim⟩
    | application command =>
        rw [PMF.support_map] at supported
        obtain ⟨state, changed, rfl⟩ := supported
        change Settled setup leaks event message.id
          { execution with
            application := state
            environmentRecall := execution.environmentRecall ++
              [⟨execution.observeEnvironment app, .application command⟩] }
        change state ∈ (environmentStep (runtime setup) execution.application command).support
          at changed
        have notCompleted : event ∉ state.config.cut.completed := by
          intro completedNow
          cases command with
          | advanceClock =>
              simp only [environmentStep, PMF.mem_support_pure_iff] at changed
              subst changed
              exact finished completedNow
          | executeSample sampled =>
              rcases (environmentStep_executeSample_config_activated (runtime setup) _ _ sampled
                  changed).2 with ⟨configEq, _⟩ | ⟨ready, action, stepped, _⟩
              · rw [configEq] at completedNow
                exact finished completedNow
              · rw [execution.application.config.step_cut sampled ready action _ stepped,
                  EventOrder.Cut.mem_complete] at completedNow
                rcases completedNow with rfl | old
                · rw [environmentStep_executeSample_of_nonsample (runtime setup) _ event ready
                    (fun payload law outputEq codeEq view => by
                      rw [nodeView_sample_actor outputEq codeEq] at owned
                      cases owned)] at changed
                  cases (PMF.mem_support_pure_iff _ _).mp changed
                  exact finished (execution.application.config.step_cut event ready action _
                    stepped ▸ (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl))
                · exact finished old
          | expire expired =>
              rcases (environmentStep_expire_config_activated (runtime setup) _ _ expired
                  changed).2 with ⟨configEq, _⟩ | ⟨ready, action, stepped, _⟩
              · rw [configEq] at completedNow
                exact finished completedNow
              · have completedAfter := completedNow
                rw [execution.application.config.step_cut expired ready action _ stepped,
                  EventOrder.Cut.mem_complete] at completedNow
                rcases completedNow with rfl | old
                · have clockBound := notLate finished
                  by_cases due : (runtime setup).deadline event ≤
                      execution.application.clock - entered
                  · omega
                  · rw [environmentStep_expire_of_not_due (runtime setup) _ event ready entered
                      (activatedNow finished) due] at changed
                    cases (PMF.mem_support_pure_iff _ _).mp changed
                    exact finished completedAfter
                · exact finished old
        exact ⟨fun completedNow => (notCompleted completedNow).elim, before.2.1,
          fun receipt => (finished (before.2.2 receipt)).elim⟩

/-- The settlement invariant holds at every legal history. -/
theorem settlesFreshCalls_history {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    ∀ {state} (_trace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace state),
      ReactiveApplication.serviceInvariant (SettlesFreshCalls setup leaks owner event delay) state
  | _, .start => trivial
  | _, .extend (source := before) prior joint _ reached => by
      have valid := settlesFreshCalls_history contract timely owner event owned prior
      cases before with
      | none =>
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro earlier entry later message split
          simp [ReactiveApplication.Execution.initial] at split
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact settlesFreshCalls_respond setup leaks owner event delay execution
                (legalFacts setup leaks horizon scheduler _ prior) who _ valid
          | none =>
              cases remaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  exact settlesFreshCalls_environment setup leaks contract timely owner event
                    owned remaining execution prior valid command next supported

/-- **Timeliness of an acceptable fresh call.** Under the asynchronous contract
with `delay + bound < deadline`, an owner's fresh call for its ready event,
sent within `delay` slots of readiness and acceptable on the view it saw, with
no other identifier emitted by the owner for the event, is accepted once the
bound has passed; and the event completes only through it, so it is neither
rejected nor preceded by expiry. -/
theorem prescribed_packet_settles {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (earlier later : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event delay entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event message.id) :
    (entry.beforeView.application.publicView.clock + bound event <
        control.execution.application.clock →
      (message.id, true) ∈ control.execution.receipts) ∧
      (event ∈ control.execution.application.config.cut.completed →
        (message.id, true) ∈ control.execution.receipts) := by
  have settled := settlesFreshCalls_history setup leaks contract timely owner event owned trace
    earlier entry later message split call sole
  refine ⟨fun late => ?_, settled.1⟩
  by_cases finished : event ∈ control.execution.application.config.cut.completed
  · exact settled.1 finished
  · obtain ⟨accepted, receipt⟩ := contract.inclusion control trace event owner owned earlier
      later entry message split call.emitted call.authored call.addressed call.ready sole
      finished late
    exact settled.2.1 accepted receipt

end Vegas
