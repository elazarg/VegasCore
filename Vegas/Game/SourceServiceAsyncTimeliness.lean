/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterAsync
import Vegas.Game.ServiceSettledEvidence
import Vegas.Pending.ReactiveEntryStability
import Vegas.Pending.ReactiveEventStability
import Vegas.Pending.ReactiveFreshCallAcceptance
import Vegas.Pending.ReactiveCanonicalDecision
import Interaction.ReactiveMessageIdentity

/-! # An acceptable fresh call settles in time under the asynchronous contract

An owner emits a fresh call for its ready event early enough that an inclusion
within `bound` slots still lands before the deadline, acceptable on the view it
saw (the handler's part of the audit's public conformance rule), and emits no
other identifier of its own for the event. Under the contract's protected
inclusion that call is accepted, and the event completes only through it: it is never
rejected and the event never expires first (`Vegas.prescribed_packet_settles`).

The proof is one invariant over every legal history, for every scheduler and
arbitrary responses of everyone else, on the service graph of every dependency
mode. While the event is unfinished, every event that completes was ready
together with it, so it belongs to another owner, and its output is not read by
the event's guards; the event's activation time is unchanged and the call stays
acceptable. An inclusion before `sent + bound` is
then within the deadline and is accepted. An expiry or a late inclusion needs a
clock past `sent + bound`, where protected inclusion has already produced a
receipt.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]


variable (setup : Setup (Player := Player) (L := L))
  {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- A fresh call the handler accepts when included in time: the acceptance part
of the audit's public conformance rule, evaluated on the view its author saw
when emitting it. -/
def AcceptableFreshCall (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  (serviceRuntime setup mode deadline).freshServiceAcceptable
  entry.beforeView.application.publicView message

/-- One recorded fresh call of `owner` for `event`: a fresh submission, sent
while the event was ready and early enough that an inclusion within
`bound event` slots lands before the deadline, and acceptable on the view its
author saw. -/
structure FreshCall (owner : Player) (event : (serviceGraph setup mode).EventId)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop where
  fresh : ∃ material, entry.action.transmission = some material
  emitted : entry.emitted = some message
  authored : message.sender = owner
  addressed : message.payload.call.event? (serviceGraph setup mode) = some event
  ready : entry.beforeView.application.publicView.EventReady event
  fits : entry.beforeView.application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound event
  conforming : AcceptableFreshCall setup leaks entry message

/-- An event completes only together with an accepting receipt for `id`, and
every receipt for `id` is accompanied by an accepting one. -/
def Settled (event : (serviceGraph setup mode).EventId) (id : MessageId Player)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop :=
  (event ∈ execution.application.config.cut.completed → (id, true) ∈ execution.receipts) ∧
    (∀ accepted, (id, accepted) ∈ execution.receipts → (id, true) ∈ execution.receipts) ∧
    ((id, true) ∈ execution.receipts → event ∈ execution.application.config.cut.completed)

/-- Every recorded fresh call of `owner` for `event`, with no other identifier
emitted by `owner` for the event, is settled. -/
def SettlesFreshCalls (owner : Player) (event : (serviceGraph setup mode).EventId)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop :=
  ∀ earlier entry later message, execution.recall owner = earlier ++ entry :: later →
    FreshCall setup leaks owner event bound entry message →
    (∀ other ∈ earlier ++ later, ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other
        event message.id) →
    Settled setup leaks event message.id execution

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
theorem no_receipt_next (execution : (serviceApplication setup mode deadline leaks).Execution)
    (sound : execution.ReceiptsSound (serviceApplication setup mode deadline leaks) (fun _ => True))
    (serials : execution.network.SerialsBeforeNext) (who : Player) (accepted : Bool) :
    ((who, execution.network.nextSerial who), accepted) ∉ execution.receipts := by
  intro member
  obtain ⟨message, published, same, _⟩ := forall₂_mem_right sound _ member
  have bound := serials.ledger message published
  rw [← same] at bound
  exact Nat.lt_irrefl _ bound

/-- The entry a response appends to its author's recall. A fresh submission
emits the author's next identifier. -/
theorem respond_recall_self (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) (action : (serviceApplication setup mode deadline leaks).Action) : ∃ emitted,
    (execution.respond (serviceApplication setup mode deadline leaks) who action).recall who =
    execution.recall who ++
    [⟨execution.observe (serviceApplication setup mode deadline leaks) who, action, emitted⟩] ∧ ∀
    material, action.transmission = some material → ∀ message,
        emitted = some message → message.id = (who, execution.network.nextSerial who) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      exact ⟨none, by simp [ReactiveApplication.Execution.respond], by simp⟩
  | some material =>
      refine
          ⟨some (execution.network.submit who
              ((serviceApplication setup mode deadline leaks).packet
              ((serviceApplication setup mode deadline leaks).submit execution.application who
              material) who (execution.network.known who) material)).1, by simp only
              [ReactiveApplication.Execution.respond, ↓reduceIte], ?_⟩
      rintro _ ⟨⟩ message ⟨⟩
      rfl

/-- Completed events stay completed across a public step. -/
theorem PublicStep.completed_mono {before after : EventGraphRuntime.State (serviceGraph setup mode)}
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
structure LegalFacts (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop where
  stable : EntryStable (serviceRuntime setup mode deadline) leaks execution
  eventStable : EntryEventStable (serviceRuntime setup mode deadline) leaks execution
  storeStable : EntryStoreStable (serviceRuntime setup mode deadline) leaks execution
  binding : execution.application.BindingInvariant
  evidence : ((serviceRuntime setup mode deadline).packetEvidence leaks).Sound execution
  receipts : execution.ReceiptsSound (serviceApplication setup mode deadline leaks) (fun _ => True)
  serials : execution.network.SerialsBeforeNext
  unique : execution.network.UniqueIds
  provenance : execution.Provenance (serviceApplication setup mode deadline leaks)
  inputs : execution.InputRecall (serviceApplication setup mode deadline leaks)

theorem legalFacts (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some control)) :
    LegalFacts setup leaks control.execution := by
  obtain ⟨_, provenance, inputs, _, receipts⟩ :=
    roster_trace_facts setup leaks horizon scheduler trace
  exact {
    stable := entryStable_history (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler trace
    eventStable := entryEventStable_history (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler trace
    storeStable := entryStoreStable_history (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler trace
    binding := ((serviceRuntime setup mode deadline).reactiveBindingInvariant leaks).history
        (serviceInitialLaw setup mode) horizon
      scheduler (fun state member => by
        obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
        exact State.initial_bindingInvariant _) trace
    evidence := ((serviceRuntime setup mode deadline).packetEvidence leaks).history_sound
        (serviceInitialLaw setup mode) horizon scheduler trace
    receipts := receipts
    serials := (serviceApplication setup mode deadline leaks).serialsBeforeNext_history scheduler
        (serviceInitialLaw setup mode) horizon trace
    unique := (serviceApplication setup mode deadline leaks).uniqueIds_history scheduler
        (serviceInitialLaw setup mode) horizon control trace
    provenance := provenance
    inputs := inputs }

private theorem settled_congr {event : (serviceGraph setup mode).EventId} {id : MessageId Player}
    {before after : (serviceApplication setup mode deadline leaks).Execution}
    (configEq : after.application.config = before.application.config)
    (receiptsEq : after.receipts = before.receipts)
    (settled : Settled setup leaks event id before) : Settled setup leaks event id after := by
  unfold Settled
  rw [configEq, receiptsEq]
  exact settled

/-- A response preserves the settlement invariant. -/
theorem settlesFreshCalls_respond (owner : Player) (event : (serviceGraph setup mode).EventId)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (facts : LegalFacts setup leaks execution) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action)
    (valid : SettlesFreshCalls setup leaks owner event bound execution) :
    SettlesFreshCalls setup leaks owner event bound
      (execution.respond (serviceApplication setup mode deadline leaks) who action) := by
  let app := serviceApplication setup mode deadline leaks
  have configEq :=
      ((serviceRuntime setup mode deadline).reactive_respond_application leaks execution who
          action).1
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

/-- A scheduler command preserves the settlement invariant under protected
inclusion. -/
theorem settlesFreshCalls_environment
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler bound)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (remaining : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (prior :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (valid : SettlesFreshCalls setup leaks owner event bound execution)
    (command : (serviceApplication setup mode deadline leaks).Command)
    (next : (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈
        (execution.environmentStep (serviceApplication setup mode deadline leaks)
        command).support) :
    SettlesFreshCalls setup leaks owner event bound next := by
  let app := serviceApplication setup mode deadline leaks
  have facts := legalFacts setup leaks horizon scheduler _ prior
  have recallEq := app.environmentStep_recall execution next command reached
  have publicStep := publicStep_reactive_environmentStep (serviceRuntime setup mode deadline) leaks
      execution next command reached
  have mono := PublicStep.completed_mono setup publicStep
  intro earlier entry later message split call sole
  rw [recallEq] at split
  have before := valid earlier entry later message split call sole
  have member : entry ∈ execution.recall owner := by rw [split]; simp
  obtain ⟨entered, activated, early⟩ := call.fits.exists
  -- Before the bound has passed the event is still timely; after it, a receipt exists.
  have notLate (unfinished : event ∉ execution.application.config.cut.completed) :
      execution.application.clock ≤
        entry.beforeView.application.publicView.clock + bound event := by
    by_contra late
    obtain ⟨accepted, receipt⟩ := inclusion ⟨remaining + 1, none, execution⟩ prior event
      owner owned earlier later entry message split call.emitted call.authored call.addressed
      call.ready sole unfinished (by change _ < execution.application.clock; omega)
    exact unfinished (before.2.2 (before.2.1 accepted receipt))
  have stableAt (unfinished : event ∉ execution.application.config.cut.completed) :=
    facts.eventStable owner entry member event call.ready unfinished
  have activatedNow (unfinished : event ∉ execution.application.config.cut.completed) :
      execution.application.activatedAt event = some entered := by
    obtain ⟨_, _, _, kept, _⟩ := stableAt unfinished
    exact kept owner owned entered activated
  have withinDeadline (unfinished : event ∉ execution.application.config.cut.completed) :
      execution.application.WithinDeadline (serviceRuntime setup mode deadline) event := by
    have clockBound := notLate unfinished
    unfold State.WithinDeadline
    rw [activatedNow unfinished]
    change execution.application.clock - entered <
        (serviceRuntime setup mode deadline).deadline event
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
    obtain ⟨extra, order, together, _, acceptedChanged⟩ := stableAt finished
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
              have inputMember := (List.mem_filter.mp output).1
              have envelopeEq : envelope = message := by
                exact (facts.unique.inputs message inputMember).pending envelope pending
                  (envelopeId.trans sameId)
              subst envelopeEq
              obtain ⟨accepted, handled⟩ := freshServiceAcceptable_accepted_of_extends
                  (serviceRuntime setup mode deadline) (serviceGraph_revealRelaxedOrdered setup
                    mode) execution.application entry.beforeView.application.publicView
                  envelope call.conforming event call.addressed order together acceptedChanged
                  (facts.storeStable owner entry member).2 finished
                  (withinDeadline finished)
                  (fun fact fact_member => facts.evidence.pending envelope pending fact fact_member)
                  facts.binding
              have reactiveHandled : app.handle execution.application envelope = some accepted :=
                (reactiveApplication_handle_of_tokenValid (serviceRuntime setup mode deadline) leaks
                    _ envelope
                    (EventGraphRuntime.freshServiceAcceptable.tokenValid
                    (serviceRuntime setup mode deadline) call.conforming)).trans handled
              rw [reactiveHandled]
              obtain ⟨named, namedEq, ready, action, stepped⟩ :=
                handle_config_mem_step (serviceRuntime setup mode deadline) _ _ _ handled
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
                      handle_config_mem_step (serviceRuntime setup mode deadline) _ _ _
                          (reactiveHandle_call handled)
                    have afterCut := execution.application.config.step_cut named ready action _
                      stepped
                    change event ∈ accepted.config.cut.completed at completedNow
                    rw [afterCut, EventOrder.Cut.mem_complete] at completedNow
                    rcases completedNow with rfl | old
                    · have sender := handle_sender_actor (serviceRuntime setup mode deadline) _ _ _
                        (reactiveHandle_call handled) event namedEq
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
                      exact sole issuer elsewhere ⟨envelope, issued,
                        senderEq.trans call.authored.symm, namedEq,
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
        change state ∈
            (environmentStep (serviceRuntime setup mode deadline) execution.application
                command).support at changed
        have notCompleted : event ∉ state.config.cut.completed := by
          intro completedNow
          cases command with
          | advanceClock =>
              simp only [environmentStep, PMF.mem_support_pure_iff] at changed
              subst changed
              exact finished completedNow
          | executeSample sampled =>
              rcases
                  (environmentStep_executeSample_config_activated
                      (serviceRuntime setup mode deadline) _ _ sampled changed).2 with
                  ⟨configEq, _⟩ | ⟨ready, action, stepped, _⟩
              · rw [configEq] at completedNow
                exact finished completedNow
              · rw [execution.application.config.step_cut sampled ready action _ stepped,
                  EventOrder.Cut.mem_complete] at completedNow
                rcases completedNow with rfl | old
                · rw [environmentStep_executeSample_of_nonsample
                          (serviceRuntime setup mode deadline) _ event ready
                    (fun payload law outputEq codeEq view => by
                      rw [nodeView_sample_actor outputEq codeEq] at owned
                      cases owned)] at changed
                  cases (PMF.mem_support_pure_iff _ _).mp changed
                  exact finished (execution.application.config.step_cut event ready action _
                    stepped ▸ (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl))
                · exact finished old
          | expire expired =>
              rcases
                  (environmentStep_expire_config_activated (serviceRuntime setup mode deadline) _ _
                      expired changed).2 with ⟨configEq, _⟩ | ⟨ready, action, stepped, _⟩
              · rw [configEq] at completedNow
                exact finished completedNow
              · have completedAfter := completedNow
                rw [execution.application.config.step_cut expired ready action _ stepped,
                  EventOrder.Cut.mem_complete] at completedNow
                rcases completedNow with rfl | old
                · have clockBound := notLate finished
                  by_cases due : (serviceRuntime setup mode deadline).deadline event ≤
                      execution.application.clock - entered
                  · omega
                  · rw [environmentStep_expire_of_not_due (serviceRuntime setup mode deadline) _
                            event ready entered (activatedNow finished) due] at changed
                    cases (PMF.mem_support_pure_iff _ _).mp changed
                    exact finished completedAfter
                · exact finished old
        exact ⟨fun completedNow => (notCompleted completedNow).elim, before.2.1,
          fun receipt => (finished (before.2.2 receipt)).elim⟩

/-- The settlement invariant holds at every legal history. -/
theorem settlesFreshCalls_history {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler bound)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner) :
    ∀ {state}
        (_trace :
            ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
            horizon scheduler).Trace state), ReactiveApplication.serviceInvariant
        (SettlesFreshCalls setup leaks owner event bound) state
  | _, .start => trivial
  | _, .extend (source := before) prior joint _ reached => by
      have valid := settlesFreshCalls_history inclusion owner event owned prior
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
              exact settlesFreshCalls_respond setup leaks owner event bound execution
                (legalFacts setup leaks horizon scheduler _ prior) who _ valid
          | none =>
              cases remaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  exact settlesFreshCalls_environment setup leaks inclusion owner
                    event
                    owned remaining execution prior valid command next supported

/-- **Timeliness of an acceptable fresh call.** Under the contract's protected
inclusion an owner's fresh call for its ready event, sent while an inclusion within
`bound` slots lands before the deadline and acceptable on the view it saw,
with no other identifier of its own emitted by the owner for the event, is accepted once the
bound has passed; and the event completes only through it, so it is neither
rejected nor preceded by expiry. -/
theorem prescribed_packet_settles {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler bound)
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some control))
    (event : (serviceGraph setup mode).EventId) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (earlier later : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other event message.id) :
    (entry.beforeView.application.publicView.clock + bound event <
        control.execution.application.clock →
      (message.id, true) ∈ control.execution.receipts) ∧
      (event ∈ control.execution.application.config.cut.completed →
        (message.id, true) ∈ control.execution.receipts) := by
  have settled := settlesFreshCalls_history setup leaks inclusion owner event owned
    trace
    earlier entry later message split call sole
  refine ⟨fun late => ?_, settled.1⟩
  by_cases finished : event ∈ control.execution.application.config.cut.completed
  · exact settled.1 finished
  · obtain ⟨accepted, receipt⟩ := inclusion control trace event owner owned earlier
      later entry message split call.emitted call.authored call.addressed call.ready sole
      finished late
    exact settled.2.1 accepted receipt

/-- A recorded response that saw `event` ready, where no other event is ever
ready together with `event`, saw the current public observation, accepted
handles and activation times while `event` is unfinished. -/
theorem entry_view_current_of_alone
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (stable : EntryStable (serviceRuntime setup mode deadline) leaks execution)
    (eventStable : EntryEventStable (serviceRuntime setup mode deadline) leaks execution)
    (who : Player) (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (member : entry ∈ execution.recall who) (event : (serviceGraph setup mode).EventId)
    (alone : ∀ other, (serviceGraph setup mode).ReadyTogether other event → other = event)
    (ready : entry.beforeView.application.publicView.EventReady event)
    (unfinished : event ∉ execution.application.config.cut.completed) :
    entry.beforeView.application.publicView.observation =
        execution.application.publicView.observation ∧
      entry.beforeView.application.publicView.accepted = execution.application.accepted ∧
      entry.beforeView.application.publicView.activatedAt = execution.application.activatedAt := by
  obtain ⟨extra, order, together, _, _⟩ := eventStable who entry member event ready unfinished
  have empty : extra = [] := by
    rcases extra with _ | ⟨other, rest⟩
    · rfl
    · exfalso
      have same := alone other (together other List.mem_cons_self)
      subst same
      apply unfinished
      apply (execution.application.config.history_exact other).mp
      change other ∈ execution.application.publicView.observation.completionOrder
      rw [order]
      exact List.mem_append_right _ List.mem_cons_self
  subst empty
  exact (stable who entry member).2 (by rw [order, List.append_nil])

/-- A recorded response that saw an owner's event ready, which is still
ready, saw it as the owner's turn: every other event of the owner that the
response saw ready is either still ready or has completed while ready together
with this one, and an owner has at most one ready event. -/
theorem ownTurn?_of_entry_ready
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (eventStable : EntryEventStable (serviceRuntime setup mode deadline) leaks execution)
    (who : Player) (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (member : entry ∈ execution.recall who) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (seen : entry.beforeView.application.publicView.EventReady event)
    (ready : execution.application.config.cut.Ready event) :
    entry.beforeView.application.publicView.ownTurn? who = some event := by
  have relaxed := serviceGraph_revealRelaxedOrdered setup mode
  obtain ⟨extra, order, together, _, _⟩ := eventStable who entry member event seen ready.1
  apply PublicView.ownTurn?_of_ownTurn
  refine ⟨seen, owned, fun other otherSeen otherOwned => ?_⟩
  by_cases done : other ∈ execution.application.config.cut.completed
  · have inExtra : other ∈ extra := by
      have inOrder : other ∈ execution.application.publicView.observation.completionOrder :=
        (execution.application.config.history_exact other).mpr done
      rw [order] at inOrder
      rcases List.mem_append.mp inOrder with old | new
      · exact (otherSeen.1 old).elim
      · exact new
    obtain ⟨cut, otherReady, eventReady⟩ := together other inExtra
    exact relaxed.ready_actor_unique cut eventReady otherReady owned otherOwned
  · exact relaxed.ready_actor_unique execution.application.config.cut ready
      (ready_of_eventReady_extends order otherSeen done) owned otherOwned

end Vegas
