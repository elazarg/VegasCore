/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAdmission
import Vegas.Pending.ReactiveServiceSelection
import Vegas.Pending.EventOpponentFrame
import Interaction.ReactiveSubmissionRounds

/-! # Binding packets throughout the actual reactive wire block

The service may include a prescribed binding during an intervening wire turn.
If it has not done so, the original unspent envelope remains eligible for the
reserved inclusion. These facts concern the actual response/inclusion protocol;
no dependency monitor or replacement scheduler is introduced.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private def BindingStatus (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (value : (graph.outputLayout event).Value)
    (message : Message Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  execution.application.config.outputs event = some value ∨
    (execution.application.config.cut.Ready event ∧
      execution.application.WithinDeadline runtime event ∧
      message ∈ execution.network.pending ∧
      (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
        (runtime.reactiveApplication leaks) message.id)

private theorem bindingStatus_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (value : (graph.outputLayout event).Value)
    (message : Message Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action)
    (status : BindingStatus runtime leaks event value message execution) :
    BindingStatus runtime leaks event value message
      (execution.respond (runtime.reactiveApplication leaks) who action) := by
  have same := runtime.reactive_respond_application leaks execution who action
  rcases status with done | ⟨ready, timely, pending, unpublished⟩
  · exact Or.inl (by rw [same.1]; exact done)
  · refine Or.inr ⟨by rwa [same.1], ?_, ?_, ?_⟩
    · have clock := congrArg PublicView.clock same.2
      have activated := congrArg PublicView.activatedAt same.2
      change (execution.respond (runtime.reactiveApplication leaks) who action).application.clock =
        execution.application.clock at clock
      change (execution.respond (runtime.reactiveApplication leaks) who
        action).application.activatedAt = execution.application.activatedAt at activated
      rw [State.WithinDeadline, clock, activated]
      exact timely
    · rcases action with ⟨transmission⟩
      cases transmission with
      | none => exact pending
      | some transmission =>
          cases transmission with
          | submit material => exact List.mem_append_left _ pending
          | replay id =>
              cases found : (execution.network.known who).find?
                  (fun envelope => envelope.id = id) <;>
                simp [ReactiveApplication.Execution.respond, MessageNetwork.replay, found, pending]
    · change message.id ∉ (execution.respond (runtime.reactiveApplication leaks) who
        action).network.ledger.map Message.id
      change message.id ∉ execution.network.ledger.map Message.id at unpublished
      rcases action with ⟨transmission⟩
      cases transmission with
      | none => exact unpublished
      | some transmission =>
          cases transmission with
          | submit material => exact unpublished
          | replay id =>
              cases found : (execution.network.known who).find?
                  (fun envelope => envelope.id = id) <;>
                simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
                  using unpublished

private theorem include_other_binding_output (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (integrity : runtime.ReactivePacketIntegrity leaks owner execution)
    (original : Message Player (WitnessedPacket graph))
    (emitted : original ∈ (runtime.reactiveApplication leaks).outputs (execution.recall owner))
    (addressed : original.payload.call.event? graph = some event)
    (selected : MessageId Player) (different : selected ≠ original.id) :
    (State.config (execution.includePending (runtime.reactiveApplication leaks)
      selected).application).outputs event = execution.application.config.outputs event := by
  cases found : execution.network.lookup selected with
  | none => simp only [ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, found]
  | some message =>
      cases accepted : handle runtime execution.application ⟨message.id, message.payload.call⟩ with
      | none => simp only [ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found, reactiveApplication, accepted, Option.getD_none]
      | some state =>
          have unique := integrity.retained runtime leaks owner execution original event emitted
            addressed
          obtain ⟨actual, atEvent, ready, action, supported⟩ := handle_config_mem_step runtime
            execution.application state ⟨message.id, message.payload.call⟩ accepted
          have distinct : event ≠ actual := by
            intro equal
            subst actual
            obtain ⟨address, addressedAgain, authored⟩ := handle_event_actor runtime
              execution.application state ⟨message.id, message.payload.call⟩ accepted
            have sameAddress := Option.some.inj (atEvent.symm.trans addressedAgain)
            subst address
            have actor : graph.actor? event = some owner := by
              have same := congrArg EventCode.actor codeEq
              rw [EventCode.actor_cast outputEq (graph.nodes event)] at same
              exact same
            have sender : message.sender = owner := Option.some.inj (authored.symm.trans actor)
            have same := unique.lookup selected message found sender atEvent
            have selectedId : message.id = selected := by
              simpa only [MessageNetwork.lookup, decide_eq_true_eq] using List.find?_some found
            exact different (selectedId.symm.trans (congrArg Message.id same))
          have unchanged : state.config.outputs event = execution.application.config.outputs
              event := by
            rw [Config.step, FinDist.support_map] at supported
            obtain ⟨value, _, equal⟩ := supported
            rw [← equal]
            exact execution.application.config.complete_output_of_ne actual event ready action
              value distinct
          simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found, reactiveApplication, accepted, Option.getD_some] using unchanged

private theorem bindingStatus_include (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.Invariant inputs)
    (associated : execution.application.BindingInvariant)
    (integrity : runtime.ReactivePacketIntegrity leaks owner execution)
    (protection : runtime.ReactiveCandidateProtection leaks owner event
      (owner, .prepared serial) execution)
    (meaning : execution.application.bindingResult (owner, .prepared serial) payload = result)
    (audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
      ReactivePlayerView.publicView)
    (emitted : (⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩ :
      Message Player (WitnessedPacket graph)) ∈
        (runtime.reactiveApplication leaks).outputs (execution.recall owner))
    (status : BindingStatus runtime leaks event
      (cast (congrArg EventField.Value outputEq.symm) result)
      ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩ execution)
    (selected : MessageId Player) :
    BindingStatus runtime leaks event
      (cast (congrArg EventField.Value outputEq.symm) result)
      ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩
      (execution.includePending (runtime.reactiveApplication leaks) selected) := by
  let app := runtime.reactiveApplication leaks
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩
  rcases status with done | ⟨ready, timely, pending, unpublished⟩
  · apply Or.inl
    have preserved := (runtime.reactiveStoreInvariant leaks (.inr event)
      (cast (congrArg EventField.Value outputEq.symm) result)).includePending
        execution selected done
    exact preserved
  · change message.id ∉ execution.network.ledger.map Message.id at unpublished
    by_cases same : selected = message.id
    · subst selected
      have found := audit.lookup_of_mem app ReactivePlayerView.publicView execution message pending
      have vacant : execution.application.accepted (.inr event) = none := by
        cases cell : execution.application.accepted (.inr event) with
        | none => rfl
        | some candidate => exact False.elim (ready.1
            (associated.toAssociationInvariant.accepted_complete event candidate cell))
      have handled := runtime.handle_commitment_eq execution.application message.id event
        (owner, .prepared serial) owner payload outputEq codeEq node ready timely rfl rfl vacant
        (protection.unused ready.1)
      dsimp only [message] at found handled
      apply Or.inl
      change (execution.includePending app (owner, nonce)).application.config.outputs event = _
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, app, reactiveApplication, handled, Option.getD_some, State.complete, meaning,
        Config.complete_output_same]
    · have outputSame := include_other_binding_output runtime leaks owner event payload outputEq
        codeEq execution integrity message emitted rfl selected same
      have progress := runtime.reactive_include_progress leaks inputs execution selected valid
      have notDone : event ∉ (execution.includePending app
          selected).application.config.cut.completed := by
          intro completed
          have present := ((execution.includePending app
            selected).application.config.output_available event).mpr completed
          rw [outputSame] at present
          exact ready.1 ((execution.application.config.output_available event).mp present)
      obtain ⟨stillReady, stillTimely⟩ :=
        (progress.ready_timely_or_completed runtime event ready timely).resolve_left notDone
      refine Or.inr ⟨stillReady, stillTimely, ?_, ?_⟩
      · rcases app.includePending_retained_or_selected execution selected message pending with
          retained | found
        · exact retained
        · have identified : message.id = selected := by
            simpa only [MessageNetwork.lookup, decide_eq_true_eq] using List.find?_some found
          exact False.elim (same identified.symm)
      · change message.id ∉ (execution.includePending app selected).network.ledger.map Message.id
        rw [app.includePending_network]
        cases found : execution.network.lookup selected with
        | none => simpa only [MessageNetwork.includePending, found] using unpublished
        | some included =>
            have identified : included.id = selected := by
              simpa only [MessageNetwork.lookup, decide_eq_true_eq] using List.find?_some found
            simpa only [MessageNetwork.includePending, found, List.map_append, List.map_cons,
              List.map_nil, List.mem_append, List.mem_singleton, identified, not_or]
              using And.intro unpublished (Ne.symm same)

private structure BindingWireFacts (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop where
  valid : execution.application.Invariant inputs
  associated : execution.application.BindingInvariant
  integrity : runtime.ReactivePacketIntegrity leaks owner execution
  protection : runtime.ReactiveCandidateProtection leaks owner event
    (owner, .prepared serial) execution
  meaning : execution.application.bindingResult (owner, .prepared serial) payload = result
  audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
    ReactivePlayerView.publicView
  recall : execution.InputRecall (runtime.reactiveApplication leaks)
  serials : execution.network.SerialsBeforeNext
  emitted : (⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩ :
    Message Player (WitnessedPacket graph)) ∈
      (runtime.reactiveApplication leaks).outputs (execution.recall owner)
  status : BindingStatus runtime leaks event
    (cast (congrArg EventField.Value outputEq.symm) result)
    ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩ execution

private theorem bindingWireFacts_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (network : runtime.NetworkPolicy leaks)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (facts : BindingWireFacts runtime leaks inputs owner event payload result serial nonce
      outputEq execution)
    (reached : next ∈ (runtime.interactionStep leaks players network .wire execution).support) :
    BindingWireFacts runtime leaks inputs owner event payload result serial nonce
      outputEq next := by
  let app := runtime.reactiveApplication leaks
  let candidate : Handle graph := (owner, .prepared serial)
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, nonce), ⟨.commitment event candidate, none⟩⟩
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have audited := app.submissionAudit_dispatch ReactivePlayerView.publicView (by intros; rfl)
    players command execution next facts.audit facts.recall facts.serials dispatched
  have remembered : app.PolicyInvariant players
      (fun current => message ∈ app.outputs (current.recall owner)) := {
    respond := by
      intro current who action present _
      obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp present
      exact List.mem_filterMap.mpr ⟨entry,
        app.respond_recall_mono current who owner action member, emitted⟩
    environment := by
      intro current after cmd present moved
      rw [app.environmentStep_recall current after cmd moved]
      exact present }
  have immutable : app.Invariant (fun state => state.candidates.lookup candidate =
      execution.application.candidates.lookup candidate) := {
    submit := by
      intro state who material same
      exact (runtime.reactive_respond_candidate_fixed leaks (.initial app state) who
        ⟨some (.submit material)⟩ candidate (by
          change state.candidates.lookup candidate ≠ .fresh
          rw [same]
          exact facts.protection.fixed)).trans same
    handle := by
      intro state packet after same accepted
      exact (handle_lookup_of_not_fresh runtime state after ⟨packet.id, packet.payload.call⟩
        candidate (by rw [same]; exact facts.protection.fixed) accepted).trans same
    environment := by
      intro state cmd after same moved
      rw [(environmentStep_tables runtime state after cmd moved).2]
      exact same }
  have unchanged := (ReactiveApplication.Invariant.policyInvariant app immutable players).dispatch
    command execution next rfl dispatched
  refine ⟨(ReactiveApplication.Invariant.policyInvariant app
      (runtime.reactiveStateInvariant leaks inputs) players).dispatch command execution next
        facts.valid dispatched,
    (ReactiveApplication.Invariant.policyInvariant app (runtime.reactiveBindingInvariant leaks)
      players).dispatch command execution next facts.associated dispatched,
    (runtime.reactivePacketIntegrity_policy leaks owner policy players prescribed).dispatch
      command execution next facts.integrity dispatched,
    (runtime.reactiveCandidateProtection_policy leaks owner event candidate rfl policy players
      prescribed).dispatch command execution next facts.protection dispatched,
    ?_, audited.1, audited.2.1, audited.2.2,
    remembered.dispatch command execution next facts.emitted dispatched, ?_⟩
  · change next.application.candidates.lookup candidate =
      execution.application.candidates.lookup candidate at unchanged
    rw [State.bindingResult, unchanged]
    exact facts.meaning
  · obtain ⟨choice, _, equal⟩ := FinDist.support_map .. ▸ selected
    subst command
    cases choice with
    | wait =>
        simp only [NetworkChoice.command, ReactiveApplication.atMostOnceCommand,
          ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
          FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
          ReactiveApplication.resume] at dispatched
        cases FinDist.mem_support_pure.mp dispatched
        exact facts.status
    | activate who =>
        obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp
          (FinDist.support_bind .. ▸ dispatched)
        obtain ⟨updated, leaked, rfl⟩ := FinDist.support_map .. ▸ moved
        obtain ⟨observations, _, rfl⟩ := FinDist.support_map .. ▸ leaked
        obtain ⟨action, _, rfl⟩ := FinDist.support_map .. ▸ resumed
        exact bindingStatus_respond runtime leaks event _ message _ who action facts.status
    | «include» id =>
        dsimp only [NetworkChoice.command, ReactiveApplication.atMostOnceCommand] at dispatched
        split at dispatched
        · simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
            FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
            ReactiveApplication.resume] at dispatched
          cases FinDist.mem_support_pure.mp dispatched
          exact bindingStatus_include runtime leaks inputs owner event payload outputEq codeEq node
            result serial nonce execution facts.valid facts.associated facts.integrity
            facts.protection facts.meaning facts.audit facts.emitted facts.status id
        · simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
            FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
            ReactiveApplication.resume] at dispatched
          cases FinDist.mem_support_pure.mp dispatched
          exact facts.status

private theorem bindingWireFacts_rounds (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (network : runtime.NetworkPolicy leaks) (rounds : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (facts : BindingWireFacts runtime leaks inputs owner event payload result serial nonce
      outputEq execution)
    (reached : next ∈ (runtime.runInteractionPlan leaks players network
      (List.replicate rounds .wire) execution).support) :
    BindingWireFacts runtime leaks inputs owner event payload result serial nonce
      outputEq next := by
  induction rounds generalizing execution with
  | zero => cases FinDist.mem_support_pure.mp reached; exact facts
  | succ rounds ih =>
      rw [List.replicate_succ, runInteractionPlan] at reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      exact ih middle (bindingWireFacts_step runtime leaks inputs owner event payload outputEq
        codeEq node result serial nonce policy players prescribed network execution middle facts
          moved) rest

/-- Once the prescribed binding envelope has been submitted at a usable
opportunity, arbitrary intervening wire turns and the actual reserved inclusion
store its fixed selected result. The premises are post-response invariants;
opponent policies and the passive leak rule are unrestricted. -/
theorem reactive_binding_wire_block (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (network : runtime.NetworkPolicy leaks) (rounds : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.Invariant inputs)
    (associated : execution.application.BindingInvariant)
    (integrity : runtime.ReactivePacketIntegrity leaks owner execution)
    (protection : runtime.ReactiveCandidateProtection leaks owner event
      (owner, .prepared serial) execution)
    (meaning : execution.application.bindingResult (owner, .prepared serial) payload = result)
    (audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
      ReactivePlayerView.publicView)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (emitted : (⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩ :
      Message Player (WitnessedPacket graph)) ∈
        (runtime.reactiveApplication leaks).outputs (execution.recall owner))
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (pending : (⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩ :
      Message Player (WitnessedPacket graph)) ∈ execution.network.pending)
    (unpublished : (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
      (runtime.reactiveApplication leaks) (owner, nonce))
    (reached : next ∈ (runtime.runInteractionPlan leaks players network
      (List.replicate rounds .wire ++ [.includeLatest event owner]) execution).support) :
    next.application.config.outputs event =
      some (cast (congrArg EventField.Value outputEq.symm) result) := by
  let app := runtime.reactiveApplication leaks
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨middle, segment, endpoint⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have facts := bindingWireFacts_rounds runtime leaks inputs owner event payload outputEq codeEq
    node result serial nonce policy players prescribed network rounds execution middle
    ⟨valid, associated, integrity, protection, meaning, audit, recall, serials, emitted,
      Or.inr ⟨ready, timely, pending, unpublished⟩⟩ segment
  simp only [runInteractionPlan, FinDist.bind_pure] at endpoint
  rcases facts.status with done | ⟨middleReady, middleTimely, retained, unspent⟩
  · obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ endpoint)
    exact (ReactiveApplication.Invariant.policyInvariant app
      (runtime.reactiveStoreInvariant leaks (.inr event)
        (cast (congrArg EventField.Value outputEq.symm) result)) players).dispatch
          command middle next done moved
  · have selected := runtime.reactiveLatest_prescribed leaks owner event middle facts.integrity
      message facts.emitted rfl rfl retained unspent
    simp only [interactionStep, interactionInstruction, selected, FinDist.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      FinDist.map_pure, ReactiveApplication.Command.actor?, ReactiveApplication.resume] at endpoint
    cases FinDist.mem_support_pure.mp endpoint
    have found := facts.audit.lookup_of_mem app ReactivePlayerView.publicView middle message
      retained
    have vacant : middle.application.accepted (.inr event) = none := by
      cases cell : middle.application.accepted (.inr event) with
      | none => rfl
      | some candidate => exact False.elim (middleReady.1
          (facts.associated.toAssociationInvariant.accepted_complete event candidate cell))
    have handled := runtime.handle_commitment_eq middle.application message.id event
      (owner, .prepared serial) owner payload outputEq codeEq node middleReady middleTimely
      rfl rfl vacant (facts.protection.unused middleReady.1)
    change (middle.includePending app (owner, nonce)).application.config.outputs event = _
    dsimp only [message] at found handled
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, app, reactiveApplication, handled, Option.getD_some, State.complete, facts.meaning,
      Config.complete_output_same]

/-- The actual compiled binding response survives every wire reaction and is
realized by the ensuing reserved inclusion. Fresh allocation and the activation
stamp are explicit prefix obligations, not assumptions about later traffic. -/
theorem reactiveDecision_binding_service (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (serial : Nat)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (network : runtime.NetworkPolicy leaks) (rounds : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.Invariant inputs)
    (associated : execution.application.BindingInvariant)
    (integrity : runtime.ReactivePacketIntegrity leaks owner execution)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
      ReactivePlayerView.publicView)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (activated : (runtime.reactiveApplication leaks).submissionObservation?
        execution.environmentRecall (owner, execution.network.nextSerial owner) =
      some execution.application.publicView)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (allocated : reactiveFreshSlot
      ((runtime.reactiveApplication leaks).observePlayer execution.application owner) = some serial)
    (supported : runtime.reactiveDecision leaks owner event action
        ((runtime.reactiveApplication leaks).observePlayer execution.application owner) ∈
      (runtime.prescribedReactivePolicy leaks owner policy (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner)).support)
    (reached : next ∈ (runtime.runInteractionPlan leaks players network
      (List.replicate rounds .wire ++ [.includeLatest event owner])
        (execution.respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveDecision leaks owner event action
            ((runtime.reactiveApplication leaks).observePlayer
              execution.application owner)))).support) :
    next.application.config.outputs event = some
      (cast (congrArg EventField.Value outputEq.symm)
        (cast (congrArg EventField.Action outputEq) action)) := by
  let app := runtime.reactiveApplication leaks
  let result : PublicationResult (L.Val payload) :=
    cast (congrArg EventField.Action outputEq) action
  let response := runtime.reactiveBinding leaks owner event payload result serial
  let submitted := execution.respond app owner response
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner),
      ⟨.commitment event (owner, .prepared serial), none⟩⟩
  have responseEq := runtime.reactiveDecision_binding_eq leaks owner owner event payload outputEq
    codeEq node action _ serial allocated
  rw [responseEq] at reached supported
  have fresh := reactiveFreshSlot_spec
    ((runtime.reactiveApplication leaks).observePlayer execution.application owner) serial allocated
  have unused : execution.application.HandleUnused (owner, .prepared serial) :=
    fun field cell => associated.accepted_fixed field _ cell fresh
  have same := runtime.reactive_respond_application leaks execution owner response
  have newlyIssued : message.id ∉ execution.network.ledger.map Message.id := by
    rintro member
    obtain ⟨previous, prior, equal⟩ := List.mem_map.mp member
    have earlier := serials.ledger previous prior
    change previous.id.2 < execution.network.nextSerial previous.id.1 at earlier
    rw [equal] at earlier
    exact Nat.lt_irrefl _ earlier
  have output : message ∈ app.outputs (submitted.recall owner) := by
    change message ∈ app.outputs ((execution.respond app owner response).recall owner)
    simp only [response, reactiveBinding, ReactiveApplication.Execution.respond,
      MessageNetwork.submit, ↓reduceIte, ReactiveApplication.outputs, List.filterMap_append,
      List.filterMap_cons, List.filterMap_nil]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have retained : message ∈ submitted.network.pending :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have afterReady : submitted.application.config.cut.Ready event := by
    change (execution.respond app owner response).application.config.cut.Ready event
    rwa [same.1]
  have afterTimely : submitted.application.WithinDeadline runtime event := by
    have progress := runtime.reactive_respond_progress leaks inputs execution owner response valid
    exact ((progress.ready_timely_or_completed runtime event ready timely).resolve_left
      afterReady.1).2
  apply runtime.reactive_binding_wire_block leaks inputs owner event payload outputEq codeEq node
    result serial (execution.network.nextSerial owner) policy players prescribed network rounds
    submitted next
    ((runtime.reactiveStateInvariant leaks inputs).respond execution owner response valid)
    ((runtime.reactiveBindingInvariant leaks).respond execution owner response associated)
    ((runtime.reactivePacketIntegrity_policy leaks owner policy players prescribed).respond
      execution owner response integrity (by rw [prescribed]; exact supported))
    (runtime.reactiveBinding_protection leaks owner event payload result serial execution fixed
      fresh unused)
    (runtime.reactiveBinding_result leaks owner event payload result serial execution fresh)
    (app.submissionAudit_respond ReactivePlayerView.publicView (by intros; rfl)
      execution owner response audit (app.submissionOrigin_next_none execution owner recall serials)
        activated)
    (app.respond_inputRecall execution owner response recall)
    ((app.serialsBeforeNextInvariant (fun _ _ => FinDist.pure .wait)).respond
      execution owner response serials) output afterReady afterTimely retained newlyIssued reached

end Vegas.EventGraphRuntime
