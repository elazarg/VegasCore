module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceFacts
public import Vegas.Game.SourceServiceFreshCall
public import Vegas.Pending.ReactiveServiceConditions
public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.Pending.EventCommandFrame
public import Vegas.Pending.ExclusionInvariant
public import Vegas.Pending.PublicFailureEvidence
public import Interaction.ReactiveReceipts

@[expose] public section

/-! # Protected-call settlement in the native runtime

An acceptable call sent within its protected inclusion window is accepted
when its owner emits no other packet for the event. The event cannot expire
or complete through a different packet first.
Authentic guard rejection produces an accepting receipt and the source's
declared failure result. Other commands may advance independent owners and
drain automatic events. Same-owner readiness and active-owner preservation
keep the protected event unfinished until its own inclusion.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- **A settled protected call keeps its event within the deadline.** While the
event of a recorded settled fresh call is unfinished, protected inclusion has
not yet run out, so the event has not passed its deadline. -/
theorem FreshCall.withinDeadline
    {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    {control : (serviceApplication setup mode duration leaks).Control}
    (trace : ((serviceApplication setup mode duration leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (inclusion : ProtectedInclusionAt (serviceTimeouts setup mode duration)
      leaks control.execution bound)
    (earlier : List (serviceApplication setup mode duration leaks).PlayerEntry)
    (entry : (serviceApplication setup mode duration leaks).PlayerEntry)
    (later : List (serviceApplication setup mode duration leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (split : control.execution.logs owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later, ¬ EmitsOtherFor (serviceTimeouts setup mode duration) leaks
      other event message.id)
    (settled : Settled setup leaks event message.id control.execution)
    (unfinished : event ∉ control.execution.application.config.cut.completed) :
    control.execution.application.WithinDeadline (serviceTimeouts setup mode duration) event := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have member : entry ∈ control.execution.logs owner := by rw [split]; simp
  obtain ⟨entered, activated, early⟩ := call.fits.exists
  change entry.beforeView.application.publicView.clock - entered + bound event <
    duration event at early
  have notLate : control.execution.application.clock ≤
      entry.beforeView.application.publicView.clock + bound event := by
    by_contra late
    obtain ⟨accepted, receipt⟩ := inclusion event owner owned earlier later entry message
      split call.emitted call.authored call.addressed call.ready sole unfinished
      (by change _ < control.execution.application.clock; omega)
    exact unfinished (settled.2.2 (settled.2.1 accepted receipt))
  obtain ⟨_, _, _, kept, _⟩ := facts.eventStable owner entry member event call.ready unfinished
  have activatedNow : control.execution.application.activatedAt event = some entered :=
    kept owner owned entered activated
  unfold State.WithinDeadline
  rw [activatedNow]
  change control.execution.application.clock - entered < duration event
  omega

/-- A native command preserves protected fresh-call settlement. -/
theorem SettlesFreshCalls.environment
    {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (remaining : Nat)
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (inclusion : ProtectedInclusionAt (serviceTimeouts setup mode duration)
      leaks execution bound)
    (prior : ((serviceApplication setup mode duration leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (valid : SettlesFreshCalls setup leaks owner event bound execution)
    (command : (serviceApplication setup mode duration leaks).Command)
    (next : (serviceApplication setup mode duration leaks).Execution)
    (reached : next ∈ (execution.environmentStep
      (serviceApplication setup mode duration leaks) command).support) :
    SettlesFreshCalls setup leaks owner event bound next := by
  let timeouts := serviceTimeouts setup mode duration
  let app := serviceApplication setup mode duration leaks
  have facts := legalFacts setup leaks horizon scheduler _ prior
  have recallEq := app.environmentStep_recall execution next command reached
  have mono := CompletionStep.completed_mono_path
    (completionPath_reactive_environmentStep timeouts leaks execution next command reached)
  intro earlier entry later message split call sole
  rw [recallEq] at split
  have before := valid earlier entry later message split call sole
  have member : entry ∈ execution.logs owner := by rw [split]; simp
  obtain ⟨entered, activated, early⟩ := call.fits.exists
  change entry.beforeView.application.publicView.clock - entered + bound event <
    duration event at early
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
      execution.application.WithinDeadline timeouts event := by
    have clockBound := notLate unfinished
    unfold State.WithinDeadline
    rw [activatedNow unfinished]
    change execution.application.clock - entered < duration event
    omega
  by_cases finished : event ∈ execution.application.config.cut.completed
  · have accepted := before.1 finished
    have kept := (app.environmentStep_receipts_prefix execution next command reached).subset
      accepted
    exact ⟨fun _ => kept, fun _ _ => kept, fun _ => mono finished⟩
  · obtain ⟨extra, order, together, _, acceptedChanged⟩ := stableAt finished
    have readyNow := ready_of_eventReady_extends order call.ready finished
    have readyActive := execution.application.active_of_ready_owned facts.quiescent readyNow owned
    have afterActive (native : EventGraphRuntime.State (serviceGraph setup mode))
        (unfinished : event ∉ native.config.cut.completed)
        (footprint : CompletionStep execution.application native) :
        owner ∉ native.config.defaulted := by
      intro excluded
      rcases footprint with ⟨same, _accepted, _activated⟩ |
          ⟨named, ready, action, moved, _activated, _accepted⟩
      · exact readyActive (same ▸ excluded)
      · have acting := EventGraph.Config.step_new_default_actor
          execution.application.config native.config named ready action moved owner readyActive
          excluded
        have same := (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
          execution.application.config.cut readyNow ready owned acting
        subst named
        apply unfinished
        rw [execution.application.config.step_cut event ready action _ moved]
        exact Finset.mem_insert_self _ _
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
            · have output : message ∈ app.outputs (execution.logs owner) :=
                List.mem_filterMap.mpr ⟨entry, member, call.emitted⟩
              rw [← facts.inputs owner] at output
              have inputMember := (List.mem_filter.mp output).1
              have envelopeEq : envelope = message :=
                (facts.unique.inputs message inputMember).pending envelope pending
                  (envelopeId.trans sameId)
              subst envelopeEq
              obtain ⟨accepted, handled⟩ := freshServiceAcceptable_accepted_of_extends timeouts
                (serviceGraph_revealRelaxedOrdered setup mode) execution.application
                entry.beforeView.application.publicView envelope call.conforming event
                call.addressed order together acceptedChanged finished (withinDeadline finished)
                (fun fact inside => facts.evidence.pending envelope pending fact inside)
                facts.quiescent facts.binding
              have reactiveHandled : app.handle execution.application envelope =
                  some accepted.drain := by
                rw [reactiveApplication_handle_of_tokenValid timeouts leaks _ envelope
                  (freshServiceAcceptable.tokenValid timeouts call.conforming), handled]
                rfl
              rw [reactiveHandled]
              obtain ⟨named, namedEq, ready, action, stepped⟩ :=
                handle_config_mem_step timeouts _ _ _ handled
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
            · have otherReceipt (accepted : Bool)
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
                    obtain ⟨native, rawHandled, drained⟩ := reactiveHandle_call handled
                    obtain ⟨named, namedEq, ready, action, moved⟩ :=
                      handle_config_mem_step timeouts _ _ _ rawHandled
                    have different : named ≠ event := by
                      intro same
                      subst named
                      have sender := handle_sender_actor timeouts _ _ _ rawHandled event namedEq
                      rw [owned] at sender
                      have senderEq : envelope.sender = owner := (Option.some.inj sender).symm
                      obtain ⟨issuer, issuerMember, material, submitted, issued, _⟩ :=
                        facts.provenance.pending envelope pending
                      rw [senderEq, split] at issuerMember
                      have differentEntry : issuer ≠ entry := by
                        rintro rfl
                        rw [call.emitted] at issued
                        exact sameId ((Option.some.inj issued) ▸ envelopeId).symm
                      have elsewhere : issuer ∈ earlier ++ later := by
                        rcases List.mem_append.mp issuerMember with inside | inside
                        · exact List.mem_append_left _ inside
                        · rcases List.mem_cons.mp inside with rfl | inside
                          · exact (differentEntry rfl).elim
                          · exact List.mem_append_right _ inside
                      exact sole issuer elsewhere ⟨envelope, issued,
                        senderEq.trans call.authored.symm, namedEq,
                        fun equal => sameId (envelopeId.symm.trans equal)⟩
                    have unfinished : event ∉ native.config.cut.completed := by
                      rw [execution.application.config.step_cut named ready action _ moved,
                        EventOrder.Cut.mem_complete]
                      exact not_or_intro (Ne.symm different) finished
                    have active := afterActive native unfinished
                      (completionStep_handle timeouts _ _ _ rawHandled)
                    change event ∉ accepted.config.cut.completed
                    rw [← drained]
                    exact fun completed => unfinished
                      ((native.drain_completed_iff_of_active event owner owned active).mp
                        completed)
              exact ⟨fun completedNow => (notCompleted completedNow).elim,
                fun accepted receipt => List.mem_append_left _
                  (before.2.1 accepted (otherReceipt accepted receipt)),
                fun receipt => (finished (before.2.2 (otherReceipt true receipt))).elim⟩
    | application command =>
        rw [PMF.support_map] at supported
        obtain ⟨state, changed, rfl⟩ := supported
        change state ∈ ((environmentStep timeouts execution.application command).map
          State.drain).support at changed
        obtain ⟨native, rawChanged, rfl⟩ := PMF.support_map .. ▸ changed
        have unfinished : event ∉ native.config.cut.completed := by
          intro completedNow
          cases command with
          | advanceClock =>
              simp only [environmentStep, PMF.mem_support_pure_iff] at rawChanged
              subst rawChanged
              exact finished completedNow
          | executeSample sampled =>
              rcases
                  (environmentStep_executeSample_config_activated
                      timeouts _ _ sampled rawChanged).2 with
                  ⟨configEq, _⟩ | ⟨ready, action, stepped, _⟩
              · rw [configEq] at completedNow
                exact finished completedNow
              · rw [execution.application.config.step_cut sampled ready action _ stepped,
                  EventOrder.Cut.mem_complete] at completedNow
                rcases completedNow with rfl | old
                · rw [environmentStep_executeSample_of_nonsample
                          timeouts _ event ready
                    (fun payload law outputEq codeEq view => by
                      rw [nodeView_sample_actor outputEq codeEq] at owned
                      cases owned)] at rawChanged
                  cases (PMF.mem_support_pure_iff _ _).mp rawChanged
                  exact finished (execution.application.config.step_cut event ready action _
                    stepped ▸ (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl))
                · exact finished old
          | expire expired =>
              rcases
                  (environmentStep_expire_config_activated timeouts _ _
                      expired rawChanged).2 with ⟨configEq, _⟩ | ⟨ready, action, stepped, _⟩
              · rw [configEq] at completedNow
                exact finished completedNow
              · have completedAfter := completedNow
                rw [execution.application.config.step_cut expired ready action _ stepped,
                  EventOrder.Cut.mem_complete] at completedNow
                rcases completedNow with rfl | old
                · have clockBound := notLate finished
                  by_cases due : timeouts.duration event ≤
                      execution.application.clock - entered
                  · change duration event ≤ execution.application.clock - entered at due
                    omega
                  · rw [environmentStep_expire_of_not_due timeouts _
                            event ready entered (activatedNow finished) due] at rawChanged
                    cases (PMF.mem_support_pure_iff _ _).mp rawChanged
                    exact finished completedAfter
                · exact finished old
        have active := afterActive native unfinished
          (completionStep_environmentStep timeouts _ _ command rawChanged)
        have notCompleted : event ∉ native.drain.config.cut.completed := fun completed =>
          unfinished ((native.drain_completed_iff_of_active event owner owned active).mp
            completed)
        change Settled setup leaks event message.id
          { execution with
            application := native.drain
            environmentRecall := execution.environmentRecall ++
              [⟨execution.observeEnvironment app, .application command⟩] }
        exact ⟨fun completedNow => (notCompleted completedNow).elim, before.2.1,
          fun receipt => (finished (before.2.2 receipt)).elim⟩


/-- The settlement invariant holds at every legal history. -/
theorem settlesFreshCalls_history {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler bound)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner) :
    ∀ {state}
        (_trace :
            ((serviceApplication setup mode duration leaks).protocol (serviceInitialLaw setup mode)
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
                  exact SettlesFreshCalls.environment setup leaks owner event owned remaining
                    execution (inclusion ⟨remaining + 1, none, execution⟩ prior) prior valid command
                    next supported

/-- **Timeliness of an acceptable fresh call.** Under the contract's protected
inclusion an owner's fresh call for its ready event, sent while an inclusion within
`bound` slots lands before the deadline and acceptable on the view it saw,
with no other identifier of its own emitted by the owner for the event, is accepted once the
bound has passed; and the event completes only through it, so it is neither
rejected nor preceded by expiry. -/
theorem prescribed_packet_settles {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler bound)
    {control : (serviceApplication setup mode duration leaks).Control}
    (trace :
        ((serviceApplication setup mode duration leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some control))
    (event : (serviceGraph setup mode).EventId) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (earlier later : List (serviceApplication setup mode duration leaks).PlayerEntry)
    (entry : (serviceApplication setup mode duration leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (split : control.execution.logs owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (serviceTimeouts setup mode duration) leaks other event message.id) :
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


end Vegas
