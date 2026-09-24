/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactivePendingRetention
import Vegas.Pending.ReactiveServiceSelection
import Vegas.Pending.EventOpponentFrame
import Interaction.ReactiveSubmissionRounds

/-! # Realizing an owned event packet through the actual wire block

A stable application realization obligation supplies the event-specific proof.
The shared induction handles arbitrary wire reactions, packet identity, early
inclusion, retention, deadlines, and the actual reserved selector.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private def PacketStatus (runtime : EventGraphRuntime graph)
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

private theorem packetStatus_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (value : (graph.outputLayout event).Value)
    (message : Message Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action)
    (status : PacketStatus runtime leaks event value message execution) :
    PacketStatus runtime leaks event value message
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

private theorem include_other_event_output (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (actor : graph.actor? event = some owner)
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

private theorem packetStatus_include (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId)
    (actor : graph.actor? event = some owner) (value : (graph.outputLayout event).Value)
    (message : Message Player (WitnessedPacket graph))
    (addressed : message.payload.call.event? graph = some event)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.Invariant inputs)
    (integrity : runtime.ReactivePacketIntegrity leaks owner execution)
    (realizes : execution.application.config.cut.Ready event →
      execution.application.WithinDeadline runtime event →
      ∃ state, handle runtime execution.application ⟨message.id, message.payload.call⟩ =
        some state ∧ state.config.outputs event = some value)
    (audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
      ReactivePlayerView.publicView)
    (emitted : message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall owner))
    (status : PacketStatus runtime leaks event value message execution)
    (selected : MessageId Player) :
    PacketStatus runtime leaks event value message
      (execution.includePending (runtime.reactiveApplication leaks) selected) := by
  let app := runtime.reactiveApplication leaks
  rcases status with done | ⟨ready, timely, pending, unpublished⟩
  · exact Or.inl ((runtime.reactiveStoreInvariant leaks (.inr event) value).includePending
      execution selected done)
  · change message.id ∉ execution.network.ledger.map Message.id at unpublished
    by_cases same : selected = message.id
    · subst selected
      have found := audit.lookup_of_mem app ReactivePlayerView.publicView execution message pending
      obtain ⟨state, handled, output⟩ := realizes ready timely
      apply Or.inl
      simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, reactiveApplication, handled, Option.getD_some] using output
    · have outputSame := include_other_event_output runtime leaks owner event actor execution
        integrity message emitted addressed selected same
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

private structure PacketWireFacts (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId)
    (value : (graph.outputLayout event).Value) (message : Message Player (WitnessedPacket graph))
    (resources : (runtime.reactiveApplication leaks).Execution → Prop)
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop where
  resources : resources execution
  valid : execution.application.Invariant inputs
  integrity : runtime.ReactivePacketIntegrity leaks owner execution
  audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
    ReactivePlayerView.publicView
  recall : execution.InputRecall (runtime.reactiveApplication leaks)
  serials : execution.network.SerialsBeforeNext
  emitted : message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall owner)
  status : PacketStatus runtime leaks event value message execution

private theorem packetWireFacts_step (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId)
    (actor : graph.actor? event = some owner) (value : (graph.outputLayout event).Value)
    (message : Message Player (WitnessedPacket graph))
    (addressed : message.payload.call.event? graph = some event)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (resources : (runtime.reactiveApplication leaks).Execution → Prop)
    (preserved : (runtime.reactiveApplication leaks).PolicyInvariant players resources)
    (unique : (runtime.reactiveApplication leaks).PolicyInvariant players
      (runtime.ReactivePacketIntegrity leaks owner))
    (realizes : ∀ execution, resources execution → execution.application.config.cut.Ready event →
      execution.application.WithinDeadline runtime event →
      ∃ state, handle runtime execution.application ⟨message.id, message.payload.call⟩ =
        some state ∧ state.config.outputs event = some value)
    (network : runtime.NetworkPolicy leaks)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (facts : PacketWireFacts runtime leaks inputs owner event value message resources execution)
    (reached : next ∈ (runtime.interactionStep leaks players network .wire execution).support) :
    PacketWireFacts runtime leaks inputs owner event value message resources next := by
  let app := runtime.reactiveApplication leaks
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
  refine ⟨preserved.dispatch command execution next facts.resources dispatched,
    (ReactiveApplication.Invariant.policyInvariant app (runtime.reactiveStateInvariant leaks inputs)
      players).dispatch command execution next facts.valid dispatched,
    unique.dispatch command execution next facts.integrity dispatched,
    audited.1, audited.2.1, audited.2.2,
    remembered.dispatch command execution next facts.emitted dispatched, ?_⟩
  obtain ⟨choice, _, equal⟩ := FinDist.support_map .. ▸ selected
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
      exact packetStatus_respond runtime leaks event value message _ who action facts.status
  | «include» id =>
      dsimp only [NetworkChoice.command, ReactiveApplication.atMostOnceCommand] at dispatched
      split at dispatched
      · simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
          FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
          ReactiveApplication.resume] at dispatched
        cases FinDist.mem_support_pure.mp dispatched
        exact packetStatus_include runtime leaks inputs owner event actor value message addressed
          execution facts.valid facts.integrity (realizes execution facts.resources) facts.audit
          facts.emitted facts.status id
      · simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
          FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
          ReactiveApplication.resume] at dispatched
        cases FinDist.mem_support_pure.mp dispatched
        exact facts.status

/-- Event-specific stable realization is sufficient for the actual reserved
service. The packet-integrity invariant describes the prescribed owner's scope;
all wire choices, foreign responses, and passive observations remain available. -/
theorem reactive_packet_wire_block (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId)
    (actor : graph.actor? event = some owner) (value : (graph.outputLayout event).Value)
    (message : Message Player (WitnessedPacket graph)) (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (resources : (runtime.reactiveApplication leaks).Execution → Prop)
    (preserved : (runtime.reactiveApplication leaks).PolicyInvariant players resources)
    (unique : (runtime.reactiveApplication leaks).PolicyInvariant players
      (runtime.ReactivePacketIntegrity leaks owner))
    (realizes : ∀ execution, resources execution → execution.application.config.cut.Ready event →
      execution.application.WithinDeadline runtime event →
      ∃ state, handle runtime execution.application ⟨message.id, message.payload.call⟩ =
        some state ∧ state.config.outputs event = some value)
    (network : runtime.NetworkPolicy leaks) (rounds : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (resourced : resources execution) (valid : execution.application.Invariant inputs)
    (integrity : runtime.ReactivePacketIntegrity leaks owner execution)
    (audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
      ReactivePlayerView.publicView)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (emitted : message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall owner))
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (pending : message ∈ execution.network.pending)
    (unpublished : (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
      (runtime.reactiveApplication leaks) message.id)
    (reached : next ∈ (runtime.runInteractionPlan leaks players network
      (List.replicate rounds .wire ++ [.includeLatest event owner]) execution).support) :
    next.application.config.outputs event = some value := by
  let app := runtime.reactiveApplication leaks
  have segment : ∀ count before after,
      PacketWireFacts runtime leaks inputs owner event value message resources before →
      after ∈ (runtime.runInteractionPlan leaks players network
        (List.replicate count .wire) before).support →
      PacketWireFacts runtime leaks inputs owner event value message resources after := by
    intro count
    induction count with
    | zero =>
        intro before after facts reached
        cases FinDist.mem_support_pure.mp reached
        exact facts
    | succ count ih =>
        intro before after facts reached
        rw [List.replicate_succ, runInteractionPlan] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
        exact ih middle after (packetWireFacts_step runtime leaks inputs owner event actor value
          message addressed players resources preserved unique realizes network before middle facts
            moved) rest
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨middle, moved, endpoint⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have facts := segment rounds execution middle
    ⟨resourced, valid, integrity, audit, recall, serials, emitted,
      Or.inr ⟨ready, timely, pending, unpublished⟩⟩ moved
  simp only [runInteractionPlan, FinDist.bind_pure] at endpoint
  rcases facts.status with done | ⟨middleReady, middleTimely, retained, unspent⟩
  · obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ endpoint)
    exact (ReactiveApplication.Invariant.policyInvariant app
      (runtime.reactiveStoreInvariant leaks (.inr event) value) players).dispatch
        command middle next done dispatched
  · have selected := runtime.reactiveLatest_prescribed leaks owner event middle facts.integrity
      message facts.emitted authored addressed retained unspent
    simp only [interactionStep, interactionInstruction, selected, FinDist.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      FinDist.map_pure, ReactiveApplication.Command.actor?, ReactiveApplication.resume] at endpoint
    cases FinDist.mem_support_pure.mp endpoint
    have found := facts.audit.lookup_of_mem app ReactivePlayerView.publicView middle message
      retained
    obtain ⟨state, handled, output⟩ := realizes middle facts.resources middleReady middleTimely
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, reactiveApplication, handled, Option.getD_some] using output

end Vegas.EventGraphRuntime
