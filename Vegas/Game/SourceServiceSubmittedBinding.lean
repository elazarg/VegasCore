/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionSupport
import Vegas.Pending.ReactiveBindingFirstSubmission

/-! # Submitted binding provenance at actual retained information sites

Every recorded binding at a legal retained decision descends from one actual
typed submission at a clean boundary application. Its remaining roster and
current passive sample are retained explicitly, so later comparisons can use
the real pending-envelope and private-candidate provenance.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The first submitted commitment underlying any actual recorded decision
has a fresh, unused canonical handle and a real retained continuation witness. -/
theorem sourceService_submitted_binding
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (granted : control.execution.application.serviceGrant = some event)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (recorded : (runtime setup).eventRecorded leaks (control.execution.recall owner) event = true) :
    ∃ before : (application setup leaks).Execution, ∃ value ∈ bounds.typedValues payload,
      ∃ (serial : Nat) (remaining : List Player) (prior : (application setup leaks).Execution)
        (sample : Finset (MessageId Player)),
        serial = control.execution.application.publicView.bindingCount owner ∧
        serial < bounds.candidateCount ∧
        before.application.publicView = control.execution.application.publicView ∧
        before.application.candidates.lookup (owner, .prepared serial) = .fresh ∧
        before.application.HandleUnused (owner, .prepared serial) ∧
        before.application.accepted (.inr event) = none ∧
        before.network.SerialsBeforeNext ∧
        (∀ player, before.network.nextSerial player =
          before.network.ledger.countP (fun message => message.sender = player)) ∧
        before.network.Satisfies (fun message =>
          message.id ∈ before.network.ledger.map Message.id) ∧
        prior ∈ ((runtime setup).runInteractionPlan leaks
          (sourceServiceMenu setup leaks bounds rosters).uniformResponses network
          (remaining.map ServiceInstruction.player)
          (before.respond (application setup leaks) owner
            ((runtime setup).reactiveBinding leaks owner event payload
              (.success value) serial))).support ∧
        control.execution = prior.sampledActivation (application setup leaks) who sample := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨selectedEvent, slot, initial, _, _, Γ, names, program, programProfile, source,
      refs, embedding, refsBefore, _, _, _, boundary, prior, sample, checkpoint, grant, reached,
      _, sampled, _, publicEq, _, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) who control trace active
  have eventEq : selectedEvent = event := Option.some.inj
    (((congrArg PublicView.serviceGrant publicEq).trans grant).symm.trans granted)
  subst selectedEvent
  let serial := boundary.application.publicView.bindingCount owner
  obtain ⟨selected, fresh, unused, vacant⟩ := checkpoint.binding_resources event rfl owner
  have priorRecorded : (runtime setup).eventRecorded leaks (prior.recall owner) event = true := by
    rw [sampled] at recorded
    exact recorded
  obtain ⟨before, value, admitted, remaining, beforeApp, ledger, _, counters,
      beforeSerials, packets, tail⟩ :=
    (runtime setup).compiled_binding_first_submission leaks bounds menu.uniformResponses
      (fun player past view response supported =>
        sourceServiceMenu_in_compiled setup leaks bounds rosters player past view
          ((menu.uniformResponses_support player past view response).mp supported))
      network owner event payload outputEq codeEq node owned serial ((rosters event).take slot)
        boundary prior (soleReady_of_ready setup boundary.application (checkpoint.ready event rfl))
        (checkpoint.ready event rfl) selected fresh checkpoint.published
          checkpoint.serials (checkpoint.unsent owner event (Nat.le_refl _)) reached priorRecorded
  refine ⟨before, value, admitted, serial, remaining, prior, sample, ?_,
    checkpoint.binding_capacity bounds capacity event rfl owner, ?_, ?_, ?_, ?_, beforeSerials,
    ?_, packets, tail, sampled⟩
  · exact (congrArg (fun view : PublicView (graph setup) => view.bindingCount owner) publicEq).symm
  · rw [beforeApp, publicEq]
  · rw [beforeApp]
    exact fresh
  · rw [beforeApp]
    exact unused
  · rw [beforeApp]
    exact vacant
  · intro player
    rw [counters, ledger]
    exact checkpoint.accounted player

/-- At a recorded retained binding site, the exact pending envelope and its
private typed candidate are still present. Repeated visits and passive samples
cannot redirect protected inclusion or allocate a second binding. -/
theorem sourceService_recorded_binding_resources
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (granted : control.execution.application.serviceGrant = some event)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (recorded : (runtime setup).eventRecorded leaks (control.execution.recall owner) event = true) :
    let serial := control.execution.application.publicView.bindingCount owner
    let id : MessageId Player := (owner,
      control.execution.network.ledger.countP (fun message => message.sender = owner))
    let message : Message Player (WitnessedPacket (graph setup)) :=
      ⟨id, ⟨.commitment event (owner, .prepared serial), none⟩⟩
    ∃ value ∈ bounds.typedValues payload,
      serial < bounds.candidateCount ∧
      control.execution.application.candidates.lookup (owner, .prepared serial) =
        .openable ⟨payload, value⟩ ∧
      control.execution.application.accepted (.inr event) = none ∧
      control.execution.network.nextSerial owner = id.2 + 1 ∧
      message ∈ control.execution.network.pending ∧
      control.execution.network.Satisfies (fun candidate =>
        candidate.id ∈ control.execution.network.ledger.map Message.id ∨ candidate = message) ∧
      control.execution.network.lookup id = some message ∧
      (runtime setup).reactiveLatest leaks event owner
        (control.execution.observeEnvironment (application setup leaks)) = .include id := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨before, value, admitted, serial, remaining, prior, sample, serialEq, capacityBound,
      beforePublic, fresh, _, vacant, beforeSerials, accounted, published, tail, sampled⟩ :=
    sourceService_submitted_binding setup leaks bounds values capacity rosters opportunities
      network who control trace active event granted owner payload outputEq codeEq node
        owned recorded
  have currentReady := (sourceService_binding_decision_resources setup leaks bounds values
    capacity rosters opportunities network who control trace active event granted owner
      payload outputEq codeEq node owned).1
  have beforeReady : before.application.config.cut.Ready event := by
    apply (before.application.publicView_eventReady event).mp
    rw [beforePublic]
    exact (control.execution.application.publicView_eventReady event).mpr currentReady
  let response := (runtime setup).reactiveBinding leaks owner event payload (.success value) serial
  let submitted := before.respond app owner response
  let packet : WitnessedPacket (graph setup) :=
    ⟨.commitment event (owner, .prepared serial), none⟩
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, before.network.nextSerial owner), packet⟩
  have application := (runtime setup).reactive_respond_application leaks before owner response
  have submittedReady : submitted.application.config.cut.Ready event := by
    rw [application.1]
    exact beforeReady
  have submittedRecorded : (runtime setup).eventRecorded leaks (submitted.recall owner)
      event = true :=
    (runtime setup).eventRecorded_respond leaks before owner response event rfl
  have transport := fun current player action same recalled supported =>
    (runtime setup).compiled_binding_tail_transport leaks bounds menu.uniformResponses
      (fun player past view action member => sourceServiceMenu_in_compiled setup leaks bounds
        rosters player past view
          ((menu.uniformResponses_support player past view action).mp member))
      submitted owner event payload outputEq codeEq node
      (soleReady_of_ready setup submitted.application submittedReady) owned submittedReady
        submittedRecorded current same recalled player action supported
  have networkEq : submitted.network = (before.network.submit owner packet).2 := rfl
  have packets : submitted.network.Satisfies fun candidate =>
      candidate.id ∈ submitted.network.ledger.map Message.id ∨ candidate = message := by
    rw [networkEq]
    exact (published.mono (fun _ member => Or.inl member)).submit owner packet (Or.inr rfl)
  have pending : message ∈ submitted.network.pending :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have unpublished : message.id ∉ submitted.network.ledger.map Message.id :=
    beforeSerials.next_unpublished owner
  obtain ⟨sameApp, ledger, _, counters, safe, retained⟩ :=
    (runtime setup).replay_window_preserves leaks menu.uniformResponses network owner submitted
      transport _ packets remaining prior tail
  obtain ⟨selected, found⟩ := (runtime setup).replay_window_selection leaks menu.uniformResponses
    network owner submitted transport event message rfl rfl packets pending unpublished remaining
      prior tail
  have currentApp : control.execution.application = submitted.application := by
    rw [sampled]
    exact sameApp
  have currentLedger : control.execution.network.ledger = before.network.ledger := by
    rw [sampled]
    exact ledger
  have currentId : before.network.nextSerial owner =
      control.execution.network.ledger.countP (fun message => message.sender = owner) := by
    rw [currentLedger]
    exact accounted owner
  have candidate : submitted.application.candidates.lookup (owner, .prepared serial) =
      .openable ⟨payload, value⟩ := by
    let material : Submission (graph setup) :=
      ⟨.commitment event (owner, .prepared serial), some ⟨payload, value⟩⟩
    change (submitStep (material.register before.application owner) owner
      material.packet).candidates.lookup (owner, .prepared serial) = _
    rw [material.candidateAfter_eq]
    simp only [material, Submission.candidateAfter, and_self, ite_true, fresh]
  have currentSafe : control.execution.network.Satisfies fun candidate =>
      candidate.id ∈ control.execution.network.ledger.map Message.id ∨ candidate = message := by
    rw [sampled]
    change (prior.network.learn who sample).Satisfies (fun candidate =>
      candidate.id ∈ prior.network.ledger.map Message.id ∨ candidate = message)
    rw [ledger]
    exact safe.learn who sample
  have currentFound : control.execution.network.lookup message.id = some message := by
    rw [sampled]
    exact found
  have currentSelected : (runtime setup).reactiveLatest leaks event owner
      (control.execution.observeEnvironment app) = .include message.id := by
    rw [sampled]
    exact selected
  dsimp only
  refine ⟨value, admitted, serialEq ▸ capacityBound, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← serialEq, currentApp]
    exact candidate
  · exact (congrArg (fun view : PublicView (graph setup) => view.accepted (.inr event))
      beforePublic).symm.trans vacant
  · have next : control.execution.network.nextSerial owner =
        before.network.nextSerial owner + 1 := by
      rw [sampled]
      change prior.network.nextSerial owner = _
      rw [counters, networkEq]
      simp only [MessageNetwork.submit, ite_true]
    simpa only [currentId] using next
  · have present : message ∈ control.execution.network.pending := by
      rw [sampled]
      exact retained pending
    simpa only [message, packet, serialEq, currentId] using present
  · simpa only [message, packet, serialEq, currentId] using currentSafe
  · simpa only [message, packet, serialEq, currentId] using currentFound
  · simpa only [message, packet, serialEq, currentId] using currentSelected

end Vegas
