/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFacts
import Vegas.Game.SourceServiceFreshCall
import Vegas.Pending.ReactiveServiceConditions
import Vegas.Pending.ReactiveGraphSteps
import Vegas.Pending.EventCommandFrame
import Interaction.ReactiveReceipts

/-! # Protected-call settlement in the sequential native runtime

The compiler's graph has a unique ready event. While a protected call is pending,
foreign inclusions cannot execute that event, and its protected inclusion window
prevents expiry. Automatic completion is quiescent until the call itself resolves;
authentic guard rejection still produces an accepting receipt.
-/

noncomputable section

namespace Vegas
open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {deadline : (graph setup).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- A sequential native command preserves protected fresh-call settlement. -/
theorem SettlesFreshCalls.environment
    {horizon : Nat}
    {scheduler : (serviceApplication setup .sequential deadline leaks).Scheduler}
    {bound : (graph setup).EventId → Nat}
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (remaining : Nat)
    (execution : (serviceApplication setup .sequential deadline leaks).Execution)
    (inclusion : ProtectedInclusionAt (serviceRuntime setup .sequential deadline)
      leaks execution bound)
    (prior : ((serviceApplication setup .sequential deadline leaks).protocol
      (serviceInitialLaw setup .sequential) horizon scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (valid : SettlesFreshCalls setup leaks owner event bound execution)
    (command : (serviceApplication setup .sequential deadline leaks).Command)
    (next : (serviceApplication setup .sequential deadline leaks).Execution)
    (reached : next ∈ (execution.environmentStep
      (serviceApplication setup .sequential deadline leaks) command).support) :
    SettlesFreshCalls setup leaks owner event bound next := by
  let runtime := serviceRuntime setup .sequential deadline
  let app := serviceApplication setup .sequential deadline leaks
  have facts := legalFacts setup leaks horizon scheduler _ prior
  have recallEq := app.environmentStep_recall execution next command reached
  have mono := CompletionStep.completed_mono_path
    (completionPath_reactive_environmentStep runtime leaks execution next command reached)
  intro earlier entry later message split call sole
  rw [recallEq] at split
  have before := valid earlier entry later message split call sole
  have member : entry ∈ execution.recall owner := by rw [split]; simp
  obtain ⟨entered, activated, early⟩ := call.fits.exists
  change entry.beforeView.application.publicView.clock - entered + bound event <
    deadline event at early
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
      execution.application.WithinDeadline runtime event := by
    have clockBound := notLate unfinished
    unfold State.WithinDeadline
    rw [activatedNow unfinished]
    change execution.application.clock - entered < deadline event
    omega
  by_cases finished : event ∈ execution.application.config.cut.completed
  · have accepted := before.1 finished
    have kept := (app.environmentStep_receipts_prefix execution next command reached).subset
      accepted
    exact ⟨fun _ => kept, fun _ _ => kept, fun _ => mono finished⟩
  · obtain ⟨extra, order, together, _, acceptedChanged⟩ := stableAt finished
    have readyNow := ready_of_eventReady_extends order call.ready finished
    have quiescentOfConfig (state : EventGraphRuntime.State (graph setup))
        (same : state.config = execution.application.config) :
        state.drain = state := by
      apply state.drain_eq_of_clear
      intro other eligible
      apply facts.quiescent other
      simpa only [State.AutomaticReady, same] using eligible
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
        unfold Settled ReactiveApplication.Execution.includePending MessageNetwork.includePending
        cases found : execution.network.lookup id with
        | none => exact before
        | some envelope =>
            have pending : envelope ∈ execution.network.pending :=
              List.mem_of_find?_eq_some found
            have envelopeId : envelope.id = id := by simpa using List.find?_some found
            dsimp only
            by_cases sameId : id = message.id
            · have output : message ∈ app.outputs (execution.recall owner) :=
                List.mem_filterMap.mpr ⟨entry, member, call.emitted⟩
              rw [← facts.inputs owner] at output
              have inputMember := (List.mem_filter.mp output).1
              have envelopeEq : envelope = message :=
                (facts.unique.inputs message inputMember).pending envelope pending
                  (envelopeId.trans sameId)
              subst envelopeEq
              obtain ⟨accepted, handled⟩ := freshServiceAcceptable_accepted_of_extends runtime
                (serviceGraph_revealRelaxedOrdered setup .sequential) execution.application
                entry.beforeView.application.publicView envelope call.conforming event
                call.addressed order together acceptedChanged finished (withinDeadline finished)
                (fun fact inside => facts.evidence.pending envelope pending fact inside)
                facts.quiescent facts.binding
              have reactiveHandled : app.handle execution.application envelope =
                  some accepted.drain := by
                rw [reactiveApplication_handle_of_tokenValid runtime leaks _ envelope
                  (freshServiceAcceptable.tokenValid runtime call.conforming), handled]
                rfl
              rw [reactiveHandled]
              obtain ⟨named, namedEq, ready, action, stepped⟩ :=
                handle_config_mem_step runtime _ _ _ handled
              have namedIs : named = event := Option.some.inj (namedEq.symm.trans call.addressed)
              subst namedIs
              have completed : named ∈ accepted.drain.config.cut.completed := by
                apply CompletionStep.completed_mono_path accepted.drain_completionPath
                rw [execution.application.config.step_cut named ready action _ stepped]
                exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
              rw [← sameId]
              have receipt : (id, true) ∈ execution.receipts ++
                  [(id, (some accepted.drain).isSome)] :=
                List.mem_append_right _ (List.mem_singleton_self _)
              exact ⟨fun _ => receipt, fun _ _ => receipt, fun _ => completed⟩
            · have rejected : app.handle execution.application envelope = none := by
                cases handled : app.handle execution.application envelope with
                | none => rfl
                | some accepted =>
                    obtain ⟨native, rawHandled, _⟩ := reactiveHandle_call handled
                    obtain ⟨named, namedEq, ready, _, _⟩ :=
                      handle_config_mem_step runtime _ _ _ rawHandled
                    have same := setup.eventGraph.sequentialize_ready_unique
                      execution.application.config.cut readyNow ready
                    subst named
                    have sender := handle_sender_actor runtime _ _ _ rawHandled event namedEq
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
                    exact (sole issuer elsewhere ⟨envelope, issued,
                      senderEq.trans call.authored.symm, namedEq,
                      fun equal => sameId (envelopeId.symm.trans equal)⟩).elim
              rw [rejected]
              have otherReceipt (accepted : Bool)
                  (receipt : (message.id, accepted) ∈ execution.receipts ++ [(id, false)]) :
                  (message.id, accepted) ∈ execution.receipts := by
                rcases List.mem_append.mp receipt with old | new
                · exact old
                · exact (sameId (Prod.mk.inj (List.mem_singleton.mp new)).1.symm).elim
              exact ⟨fun completed => (finished completed).elim,
                fun accepted receipt => List.mem_append_left _
                  (before.2.1 accepted (otherReceipt accepted receipt)),
                fun receipt => (finished (before.2.2 (otherReceipt true receipt))).elim⟩
    | application command =>
        rw [PMF.support_map] at supported
        obtain ⟨state, changed, rfl⟩ := supported
        change state ∈ ((environmentStep runtime execution.application command).map
          State.drain).support at changed
        obtain ⟨native, rawChanged, rfl⟩ := PMF.support_map .. ▸ changed
        have configEq : native.config = execution.application.config := by
          cases command with
          | advanceClock =>
              cases (PMF.mem_support_pure_iff _ _).mp rawChanged
              rfl
          | executeSample sampled =>
              rcases (environmentStep_executeSample_config_activated runtime _ _ sampled
                rawChanged).2 with ⟨same, _⟩ | ⟨ready, _, _, _⟩
              · exact same
              · have same := setup.eventGraph.sequentialize_ready_unique
                  execution.application.config.cut readyNow ready
                subst sampled
                rw [environmentStep_executeSample_of_owned runtime _ event owner owned]
                  at rawChanged
                cases (PMF.mem_support_pure_iff _ _).mp rawChanged
                rfl
          | expire expired =>
              rcases (environmentStep_expire_config_activated runtime _ _ expired rawChanged).2
                with ⟨same, _⟩ | ⟨ready, _, _, _⟩
              · exact same
              · have same := setup.eventGraph.sequentialize_ready_unique
                  execution.application.config.cut readyNow ready
                subst expired
                have due : ¬ deadline event ≤ execution.application.clock - entered := by
                  have clockBound := notLate finished
                  omega
                rw [environmentStep_expire_of_not_due runtime _ event ready entered
                  (activatedNow finished) due] at rawChanged
                cases (PMF.mem_support_pure_iff _ _).mp rawChanged
                rfl
        rw [quiescentOfConfig native configEq]
        change Settled setup leaks event message.id
          { execution with
            application := native
            environmentRecall := execution.environmentRecall ++
              [⟨execution.observeEnvironment app, .application command⟩] }
        unfold Settled
        dsimp only
        rw [configEq]
        exact before

end Vegas
