/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBoundary
import Vegas.Game.SourceServiceBindingSupport
import Vegas.Pending.ReactiveBindingWindowSupport
import Vegas.Pending.ReactiveServiceSoundness
import Vegas.Pending.ReactiveServiceTraffic
import Vegas.Pending.ReactiveServiceEvents
import Vegas.Pending.ReactiveRevealSettlement

/-! # Typed checkpoints for arbitrary permitted binding rosters

This constructs the next source configuration from every supported retained
binding execution. Choice timing, intervening passive observations and replay
copies are unrestricted within the fixed finite roster. The clock padding
after inclusion is separate from this typed and allocation checkpoint.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every permitted binding roster has an original value-only source
successor. Dynamic catalogues, public allocation accounting and published
traffic are derived from the actual first submission and its inclusion. -/
theorem ServiceBoundary.binding_inclusion
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (name : VarId) (owner : Player) (payload : L.Ty)
    (guard : SourceGuard L Γ owner name payload)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (beforeRefs : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : ∀ value : L.Val payload, decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.success value)) = some (.commit owner name payload (.success value)))
    (opportunity : owner ∈ rosters event)
    (capacity : execution.application.publicView.bindingCount owner < bounds.candidateCount)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner])
        execution).support) :
    final.application.CandidatesRepresented ∧ final.application.AcceptedRecorded ∧
      (∀ who, final.application.PreparedPrefix who) ∧
      (∀ who, final.network.nextSerial who =
        final.network.ledger.countP (fun message => message.sender = who)) ∧
      final.network.Satisfies (fun message => message.id ∈ final.network.ledger.map Message.id) ∧
      ∃ value ∈ bounds.typedValues payload,
        SourceCheckpoint setup (commitSuccessor name guard source (.success value))
          (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
          final.application.config := by
  let app := application setup leaks
  let serial := execution.application.publicView.bindingCount owner
  obtain ⟨selected, candidate, unused, vacant⟩ := boundary.binding_resources event atRank owner
  have ready := boundary.ready event atRank
  have timely := boundary.timely event atRank (by rw [owned]; rfl)
  have unsent := boundary.unsent owner event (by omega)
  have ends : (execution.recall owner).length + (rosters event).count owner =
      rosterOffset setup rosters owner event + (rosters event).count owner := by
    rw [boundary.response_offset event atRank owner]
  obtain ⟨before, immediate, value, admitted, beforeApp, beforeLedger, beforeReceipts,
    beforeCounters, beforeSerials, included, finalApp, finalLedger, finalReceipts,
    finalCounters, finalPublished⟩ := sourceService_binding_roster_support setup leaks bounds
      rosters covered players lawful network owner event payload outputEq codeEq node owned
        serial capacity (rosters event) execution final ready selected candidate
          boundary.published boundary.serials unsent opportunity ends reached
  have beforeReady : before.application.config.cut.Ready event := by rw [beforeApp]; exact ready
  have beforeTimely : before.application.WithinDeadline (runtime setup) event := by
    rw [beforeApp]; exact timely
  have beforeFresh : before.application.candidates.lookup (owner, .prepared serial) = .fresh := by
    rw [beforeApp]; exact candidate
  have beforeVacant : before.application.accepted (.inr event) = none := by
    rw [beforeApp]; exact vacant
  have beforeUnused : before.application.HandleUnused (owner, .prepared serial) := by
    rw [beforeApp]; exact unused
  have beforePrepared : ∀ who, before.application.PreparedPrefix who := by
    rw [beforeApp]; exact boundary.prepared
  have represented : before.application.CandidatesRepresented := by
    rw [beforeApp]; exact boundary.represented
  have recorded : before.application.AcceptedRecorded := by
    rw [beforeApp]; exact boundary.acceptedRecorded
  have beforeSerial : before.application.publicView.bindingCount owner = serial := by
    rw [beforeApp]
  have nextRepresented := (runtime setup).reactiveBinding_reserved_represented leaks before
    owner event payload outputEq codeEq node (.success value) serial represented beforeReady
      beforeTimely beforeFresh beforeVacant beforeUnused beforeSerials players network immediate
        included
  have canonicalIncluded := included
  rw [← beforeSerial] at canonicalIncluded
  have nextRecorded := (runtime setup).reactiveBinding_reserved_recorded leaks before owner event
    payload outputEq codeEq node (.success value) recorded beforeReady beforeTimely
      (by rw [beforeSerial]; exact beforeFresh) beforeVacant
      (by rw [beforeSerial]; exact beforeUnused) beforeSerials players network immediate
      canonicalIncluded
  have nextPrepared := (runtime setup).rawBinding_reserved_all_preparedPrefix leaks before owner
    event payload outputEq codeEq node (some ⟨payload, value⟩) beforePrepared beforeReady
      beforeTimely beforeVacant (by rw [beforeSerial]; exact beforeUnused) beforeSerials
        players network immediate canonicalIncluded
  have nextAccounted : ∀ who, immediate.network.nextSerial who =
      immediate.network.ledger.countP (fun message => message.sender = who) := by
    have settled : ∀ who, before.network.nextSerial who =
        before.network.ledger.countP (fun message => message.sender = who) := by
      rw [beforeCounters, beforeLedger]
      exact boundary.accounted
    have moved := included
    rw [(runtime setup).reactiveBinding_reserved_selection leaks before owner event payload
      (.success value) serial beforeSerials players network] at moved
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff _ _] at moved
    rw [moved]
    exact app.submit_include_serials_match_ledger before beforeSerials settled owner
      ⟨⟨.commitment event (owner, .prepared serial), some ⟨payload, value⟩⟩, .none⟩
  have config := ((runtime setup).reactiveBinding_reserved_state leaks before owner event payload
    outputEq codeEq node (.success value) serial beforeReady beforeTimely beforeFresh beforeVacant
      beforeUnused beforeSerials players network immediate included).1
  refine ⟨?_, ?_, ?_, ?_, finalPublished, value, admitted, ?_⟩
  · rw [finalApp]
    exact nextRepresented
  · rw [finalApp]
    exact nextRecorded
  · rw [finalApp]
    exact nextPrepared
  · rw [finalCounters, finalLedger]
    exact nextAccounted
  · rw [finalApp, config]
    have checkpoint : SourceCheckpoint setup source refs rank before.application.config := by
      rw [beforeApp]
      exact boundary.toSourceCheckpoint
    exact checkpoint.commit name guard event atRank beforeReady outputEq beforeRefs
      (.success value) (decoded value)

/-- Every intermediate binding opportunity has the actual readiness, deadline,
sole-readiness and communication invariants used by the service checker. Until the
owner submits, the complete allocator and public serial accounting remain
those of the preceding completed boundary. -/
theorem ServiceBoundary.binding_prefix_resources
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (visits : List Player) (current : (application setup leaks).Execution)
    (reached : current ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) execution).support) :
    current.application.config.cut.Ready event ∧
      current.application.WithinDeadline (runtime setup) event ∧
      current.application.publicView.SoleReady event ∧
      current.application.BindingInvariant ∧ current.InputRecall (application setup leaks) ∧
      current.SerialRecall (application setup leaks) ∧ current.network.SerialsBeforeNext ∧
      ((runtime setup).eventRecorded leaks (current.recall owner) event = false →
        current.application = execution.application ∧
        reactiveFreshSlot (current.observe (application setup leaks) owner).application =
          some (current.application.publicView.bindingCount owner) ∧
        (∀ who, current.network.nextSerial who =
          current.network.ledger.countP (fun message => message.sender = who)) ∧
        current.network.Satisfies
          (fun message => message.id ∈ current.network.ledger.map Message.id)) := by
  obtain ⟨config, publicEq⟩ := (runtime setup).player_window_application leaks players network
    visits execution current reached
  obtain ⟨_, binding, recalled, serialRecall, serials⟩ := boundary.run_core players network
    (visits.map ServiceInstruction.player) current reached
  have ready := boundary.ready event atRank
  have timely := boundary.timely event atRank (by rw [owned]; rfl)
  have clock := congrArg PublicView.clock publicEq
  have activation := congrArg PublicView.activatedAt publicEq
  have currentReady : current.application.config.cut.Ready event := by rw [config]; exact ready
  refine ⟨currentReady, ?_, soleReady_of_ready setup current.application currentReady,
    binding, recalled, serialRecall, serials, ?_⟩
  · unfold EventGraphRuntime.State.WithinDeadline at timely ⊢
    change current.application.clock = execution.application.clock at clock
    change current.application.activatedAt = execution.application.activatedAt at activation
    rw [activation, clock]
    exact timely
  · intro unsent
    obtain ⟨selected, candidate, _, _⟩ := boundary.binding_resources event atRank owner
    have ordinary : ∀ who past view response, response ∈ (players who past view).support →
        response ∈ bounds.compiledActions (runtime setup) leaks who past view :=
      fun who past view response member => sourceServiceMenu_in_compiled setup leaks bounds
        rosters who past view (lawful who past view response member)
    obtain ⟨application, ledger, _, counters, published⟩ :=
      (runtime setup).compiled_binding_unsubmitted_prefix leaks bounds players ordinary network
        owner event payload outputEq codeEq node owned
        (execution.application.publicView.bindingCount owner) visits execution current
        (soleReady_of_ready setup execution.application ready) ready selected candidate
        boundary.published reached unsent
    refine ⟨application, ?_, ?_, published⟩
    · change reactiveFreshSlot
        (((runtime setup).reactiveApplication leaks).observePlayer current.application owner) = _
      rw [application]
      exact selected
    · intro who
      rw [counters, ledger]
      exact boundary.accounted who

/-- Every envelope known or pending during an arbitrary permitted binding
roster passes the public phase checker, including copies replayed before the
protected inclusion. Earlier valid audit records remain valid at each actual
prefix, with the phase recorded when the envelope was transmitted. -/
theorem ServiceBoundary.binding_prefix_conformance
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (traffic : ∀ record ∈ (application setup leaks).executionTraffic execution,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true)
    (visits : List Player) (current : (application setup leaks).Execution)
    (reached : current ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) execution).support) :
    current.network.Satisfies (fun message => (runtime setup).permittedServiceEnvelope
      current.application.publicView current.network.ledger message = true) ∧
    (∀ record ∈ (application setup leaks).executionTraffic current,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true) := by
  let app := application setup leaks
  induction visits using List.reverseRecOn generalizing current with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨(runtime setup).service_published_conformance leaks execution boundary.published,
        traffic⟩
  | append_singleton visits actor ih =>
      rw [List.map_append, (runtime setup).runInteractionPlan_append] at reached
      obtain ⟨before, reachedBefore, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have prior := ih before reachedBefore
      simp only [List.map_cons, List.map_nil, runInteractionPlan, PMF.bind_pure,
        interactionStep, interactionInstruction, PMF.pure_bind] at reached
      change current ∈ ((before.environmentStep app (.activate actor)).bind
        (app.invoke players actor)).support at reached
      rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map] at reached
      obtain ⟨sample, selected, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ reached
      let activated := before.sampledActivation app actor sample
      have activation : activated ∈ (before.environmentStep app (.activate actor)).support := by
        rw [ReactiveApplication.Execution.activation_samples]
        exact PMF.support_map .. ▸ ⟨sample, selected, rfl⟩
      have sampled := (runtime setup).service_sampled_conformance leaks before actor sample prior.1
      obtain ⟨ready, timely, sole, binding, _, _, _, unsent⟩ :=
        boundary.binding_prefix_resources bounds players lawful network event atRank
          owner payload outputEq codeEq node owned visits before reachedBefore
      have member := sourceServiceMenu_in_compiled setup leaks bounds rosters actor
        (activated.recall actor) (activated.observe app actor) (lawful actor _ _ response chosen)
      have issued : ∀ record ∈ app.trafficStep (some ⟨0, some actor, activated⟩)
          (some ⟨0, none, activated.respond app actor response⟩),
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = true := by
        by_cases acting : actor = owner
        · subst actor
          exact bounds.compiled_binding_traffic (runtime setup) leaks activated binding 0
            owner event payload outputEq codeEq node (sole.ownTurn owned) ready timely
            (fun absent => (unsent absent).2.1)
            (fun absent => (unsent absent).2.2.1 owner)
            (sampled.known owner) response member
        · exact bounds.compiled_foreign_traffic (runtime setup) leaks activated 0 actor
            (sole.idle (by rw [owned]; exact fun equal => acting (Option.some.inj equal).symm))
            (sampled.known actor) response member
      refine ⟨(runtime setup).service_response_conformance leaks activated 0 actor response
        sampled issued, ?_⟩
      intro record included
      rw [app.executionTraffic_activated_response before activated actor response 0 activation,
        List.mem_append] at included
      exact included.elim (prior.2 record) (issued record)

/-- The complete binding service block preserves the operational boundary
under every permitted policy, including arbitrary early submission and later
replays. Its source successor is one of the original value-only choices. -/
theorem ServiceBoundary.binding_block
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (name : VarId) (owner : Player) (payload : L.Ty)
    (guard : SourceGuard L Γ owner name payload)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (beforeRefs : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : ∀ value : L.Val payload, decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.success value)) = some (.commit owner name payload (.success value)))
    (opportunity : owner ∈ rosters event)
    (capacity : execution.application.publicView.bindingCount owner < bounds.candidateCount)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution).support) :
    ∃ value ∈ bounds.typedValues payload,
      ServiceBoundary setup leaks rosters initial
        (commitSuccessor name guard source (.success value))
        (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) final := by
  let app := application setup leaks
  have phase := reached
  rw [rosterBlock_of_owner setup rosters event owner owned, List.append_assoc,
    (runtime setup).runInteractionPlan_append] at phase
  obtain ⟨included, inclusion, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ phase)
  obtain ⟨represented, acceptedRecorded, prepared, accounted, published,
    value, admitted, checkpoint⟩ := boundary.binding_inclusion bounds covered players lawful
      network event atRank name owner payload guard outputEq codeEq node owned
        beforeRefs decoded opportunity capacity included inclusion
  have settled : ¬included.application.config.cut.Ready event := by
    intro ready
    have next := (ready_iff_rank setup _ (rank + 1) checkpoint.ordered event).mp ready
    omega
  obtain ⟨after, exactTail, afterApp, afterNetwork, _, afterRecall⟩ :=
    (runtime setup).settled_reveal_expiry leaks players network included event settled
      (event.val + 1)
  rw [exactTail] at tail
  have finalEq := (PMF.mem_support_pure_iff _ _).mp tail
  subst final
  have finalCheckpoint : SourceCheckpoint setup (commitSuccessor name guard source (.success value))
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) after.application.config := by
    rw [afterApp]
    exact checkpoint
  obtain ⟨invariant, binding, recalled, serialRecall, serials⟩ := boundary.run_core players network
    (rosterBlock setup rosters event) after reached
  obtain ⟨clock, timely⟩ := boundary.roster_successor_timing players network event atRank after
    reached finalCheckpoint.ordered
  refine ⟨value, admitted, {
    toSourceCheckpoint := finalCheckpoint
    invariant := invariant
    binding := binding
    prepared := ?_
    represented := ?_
    acceptedRecorded := ?_
    «recall» := recalled
    serialRecall := serialRecall
    published := ?_
    serials := serials
    accounted := ?_
    counts := boundary.roster_counts players network event atRank after reached
    unsent := ?_
    clock := clock
    timely := timely }⟩
  · rw [afterApp]
    exact prepared
  · rw [afterApp]
    exact represented
  · rw [afterApp]
    exact acceptedRecorded
  · rw [afterNetwork]
    exact published
  · rw [afterNetwork]
    exact accounted
  · intro observer other future
    have otherEvent : other ≠ event := by intro equal; subst other; omega
    rw [(runtime setup).runInteractionPlan_append] at inclusion
    obtain ⟨visited, window, inclusion⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ inclusion)
    have includedRecall : included.recall observer = visited.recall observer := by
      have earlier := (runtime setup).runInteractionPlan_recall_prefix leaks players network
        [.includeLatest event owner] visited included inclusion observer
      have lengths := fixed_plan_response_counts setup leaks network players
        [.includeLatest event owner] (by simp) visited included inclusion observer
      apply (earlier.eq_of_length ?_).symm
      simpa only [List.filterMap_cons, instructionActor, List.filterMap_nil, List.count_nil,
        Nat.add_zero] using lengths.symm
    rw [afterRecall, includedRecall]
    have ordinary : ∀ who past view response, response ∈ (players who past view).support →
        response ∈ bounds.compiledActions (runtime setup) leaks who past view :=
      fun who past view response member => sourceServiceMenu_in_compiled setup leaks bounds
        rosters who past view (lawful who past view response member)
    rw [(runtime setup).compiled_window_other_events leaks bounds players ordinary network event
      (rosters event) execution visited
      (soleReady_of_ready setup execution.application (boundary.ready event atRank)) window
      observer other otherEvent]
    exact boundary.unsent observer other (by omega)

end Vegas
