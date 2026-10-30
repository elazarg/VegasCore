/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceSettledEvidence
import Vegas.Game.SourceServiceFreshCall
import Vegas.Game.SourceServiceFacts
import Vegas.Pending.ReactiveCanonicalDecision
import Vegas.Pending.ReactiveServiceConditions
import Interaction.ReactivePacketEvidence
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactivePacketEvidence

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

/-- A scheduler command preserves the settlement invariant under protected
inclusion. -/
theorem settlesFreshCalls_environment
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (remaining : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (inclusion : ProtectedInclusionAt (serviceRuntime setup mode deadline) leaks execution bound)
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
    obtain ⟨accepted, receipt⟩ := inclusion event owner owned earlier later entry message
      split call.emitted call.authored call.addressed call.ready sole unfinished
      (by change _ < execution.application.clock; omega)
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
                  exact settlesFreshCalls_environment setup leaks owner event owned remaining
                    execution (inclusion ⟨remaining + 1, none, execution⟩ prior) prior valid command
                    next supported

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
