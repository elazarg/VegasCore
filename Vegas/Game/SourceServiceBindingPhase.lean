/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceWaiting
import Vegas.Game.SourceServiceBindingRoster
import Vegas.Game.ServiceRosterCounts
import Vegas.Pending.ReactiveServiceRecall

/-! # A source binding across its complete finite response roster

The limiting compiler waits until the last owner opportunity. Every earlier
and later native activation remains present, with actual passive observations
and known-envelope replays. The eventual binding retains its original source
lottery. This is an execution theorem; a fully mixed timing sequence is still
required for sequential-equilibrium transport.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

variable [Finite Player]

/-- At the selected owner activation, the actual full source policy makes
the original binding choice and permits the whole foreign tail before inclusion. -/
theorem sourceServiceLastPolicy_commit_opportunity
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (serial : Nat)
    (selected : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (network : (runtime setup).NetworkPolicy leaks)
    (remaining : List Player) (absent : owner ∉ remaining) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (ready : execution.application.config.cut.Ready event)
      (_timely : execution.application.WithinDeadline (runtime setup) event)
      (_vacant : execution.application.accepted (.inr event) = none)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_last : (execution.recall owner).length + 1 =
        rosterOffset setup rosters owner event + (rosters event).count owner),
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      (.player owner :: remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
      execution).map (fun final => (final.application.config, final.receipts)) =
      (commitKernel profile (source.view owner)).map fun choice =>
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice),
          execution.receipts ++ [((owner, execution.network.nextSerial owner), true)]) := by
  let := Fintype.ofFinite Player
  dsimp only
  intro ready timely vacant unsent last
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
  let transport : Player → app.Policy := fun _ => app.silentPolicy
  let result (final : app.Execution) := (final.application.config, final.receipts)
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event index
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_bind _ _
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have step : (runtime setup).interactionStep leaks players network (.player owner) execution =
      (app.observePending owner execution.network.pending).bind (fun sample =>
        let activated := execution.sampledActivation app owner sample
        (players owner (activated.recall owner) (activated.observe app owner)).map
          (activated.respond app owner)) := by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      ReactiveApplication.invoke, ReactiveApplication.Execution.activation_samples,
      PMF.bind_map, Function.comp_def]
    rfl
  change ((runtime setup).runInteractionPlan leaks players network
    (.player owner :: remaining.map ServiceInstruction.player ++
      [.includeLatest event owner]) execution).map result = _
  rw [List.cons_append, runInteractionPlan, PMF.map_bind, step, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  let expected := (commitKernel profile (source.view owner)).map fun choice =>
    (execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice),
      execution.receipts ++ [((owner, execution.network.nextSerial owner), true)])
  trans (app.observePending owner execution.network.pending).bind (fun _ => expected)
  · apply bind_congr_on_support _
    intro sample _
    let activated := execution.sampledActivation app owner sample
    have sourceLaw := sourceServicePolicy_commit setup leaks fresh guard next wholeProfile profile
      refs source embedding refsBefore offset aligned activated agree history ready
    have submits : ∀ response ∈ (sourceServicePolicy setup leaks wholeProfile owner
        (activated.recall owner) (activated.observe app owner)).support,
        response.transmission ≠ none := by
      intro response supported
      rw [sourceLaw, PMF.support_map] at supported
      obtain ⟨choice, _, responseEq⟩ := supported
      have physical := serviceDecision_binding_fresh (runtime setup) leaks activated owner event
        payload outputEq codeEq node serial selected candidate choice
      have same : response = (runtime setup).reactiveBinding leaks owner event payload choice
          serial := responseEq.symm.trans physical
      rw [same]
      cases choice <;> exact Option.some_ne_none _
    have responseLaw : players owner (activated.recall owner) (activated.observe app owner) =
        sourceServicePolicy setup leaks wholeProfile owner (activated.recall owner)
          (activated.observe app owner) :=
      sourceServiceLastPolicy_submissions setup leaks rosters wholeProfile owner
        (activated.recall owner) (activated.observe app owner) event
          (ownTurn?_of_ready setup execution.application ready owned) owned unsent last submits
    change (players owner (activated.recall owner) (activated.observe app owner)).bind _ = _
    rw [responseLaw]
    have delayed := sourceServicePolicy_commit_delayed_service setup leaks fresh guard next
      wholeProfile profile refs source embedding refsBefore offset aligned activated agree history
        serial selected candidate unused (serials.learn owner sample) (published.learn owner sample)
        bounds transport (fun who past view response supported =>
          bounds.silent_compiled (runtime setup) leaks who past view response supported)
        network remaining ready timely vacant
    rw [PMF.map_bind] at delayed
    apply Eq.trans ?_ delayed
    apply bind_congr_on_support _
    intro response _
    apply congrArg (PMF.map result)
    apply sourceServiceLastPolicy_foreign_tail setup leaks rosters wholeProfile network event owner
      owned remaining absent
    rw [((runtime setup).reactive_respond_application leaks activated owner response).2]
    exact soleReady_of_ready setup execution.application ready
  · exact PMF.bind_const _ expected

/-- The complete actual roster, including every early owner and foreign
opportunity, implements the original typed source commitment lottery. -/
theorem sourceServiceLastPolicy_commit_roster
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (serial : Nat)
    (selected : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (network : (runtime setup).NetworkPolicy leaks)
    (visited remaining : List Player) (absent : owner ∉ remaining) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (_position : rosters event = visited ++ owner :: remaining)
      (ready : execution.application.config.cut.Ready event)
      (_timely : execution.application.WithinDeadline (runtime setup) event)
      (_vacant : execution.application.accepted (.inr event) = none)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length = rosterOffset setup rosters owner event),
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) execution).map
        (fun final => (final.application.config, final.receipts)) =
      (commitKernel profile (source.view owner)).map fun choice =>
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice),
          execution.receipts ++ [((owner, execution.network.nextSerial owner), true)]) := by
  dsimp only
  intro position ready timely vacant unsent counted
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
  let result (final : app.Execution) := (final.application.config, final.receipts)
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event index
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  let expected := (commitKernel profile (source.view owner)).map fun choice =>
    (execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice),
      execution.receipts ++ [((owner, execution.network.nextSerial owner), true)])
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have total : (rosters event).count owner = visited.count owner + 1 := by
    rw [position, List.count_append, List.count_cons_self, List.count_eq_zero.mpr absent]
  change (execution.recall owner).length = rosterOffset setup rosters owner event at counted
  have before : (execution.recall owner).length + visited.count owner <
      rosterOffset setup rosters owner event + (rosters event).count owner := by
    rw [counted, total]
    omega
  change ((runtime setup).runInteractionPlan leaks players network
    ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) execution).map
      result = expected
  rw [position, List.map_append, List.map_cons, List.append_assoc,
    (runtime setup).runInteractionPlan_append, PMF.map_bind]
  trans ((runtime setup).runInteractionPlan leaks players network
    (visited.map ServiceInstruction.player) execution).bind (fun _ => expected)
  · apply bind_congr_on_support _
    intro current reached
    obtain ⟨same, ledger, receipts, counters, packets, _⟩ :=
      sourceServiceLastPolicy_waiting_data setup leaks rosters wholeProfile network event owner
        owned visited execution current (soleReady_of_ready setup execution.application ready)
        before _ published reached
    have currentAgree : refs.Agrees source.state current.application.config.store := by
      rw [same]; exact agree
    have currentHistory : decodeHistory setup.program (current.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history := by
      rw [same]; exact history
    have currentSelected : reactiveFreshSlot (current.observe app owner).application =
        some serial := by
      change reactiveFreshSlot (app.observePlayer current.application owner) = _
      rw [same]
      exact selected
    have currentCandidate : current.application.candidates.lookup (owner, .prepared serial) =
        .fresh := by rw [same]; exact candidate
    have currentUnused : current.application.HandleUnused (owner, .prepared serial) := by
      rw [same]; exact unused
    have currentReady : current.application.config.cut.Ready event := by rw [same]; exact ready
    have currentTimely : current.application.WithinDeadline (runtime setup) event := by
      rw [same]; exact timely
    have currentVacant : current.application.accepted (.inr event) = none := by
      rw [same]; exact vacant
    have currentSerials := (runtime setup).runInteractionPlan_serials leaks players network
      (visited.map ServiceInstruction.player) execution current serials reached
    have currentPublished : current.network.Satisfies fun message =>
        message.id ∈ current.network.ledger.map Message.id := by rwa [ledger]
    have pureReplay := reached
    rw [sourceServiceLastPolicy_waiting_law setup leaks rosters wholeProfile network event owner
      owned visited execution (soleReady_of_ready setup execution.application ready) before]
      at pureReplay
    have currentUnsent := (silent_window_eventRecorded setup leaks network visited execution current
      pureReplay owner event).trans unsent
    have fixed : (ServiceInstruction.wire : ServiceInstruction (graph setup)) ∉
        visited.map ServiceInstruction.player := by simp
    have currentCount := fixed_plan_response_counts setup leaks network players
      (visited.map ServiceInstruction.player) fixed execution current reached owner
    simp only [List.filterMap_map, Function.comp_def, instructionActor,
      List.filterMap_some] at currentCount
    have last : (current.recall owner).length + 1 =
        rosterOffset setup rosters owner event + (rosters event).count owner := by
      rw [currentCount, counted, total]
      omega
    have completed := sourceServiceLastPolicy_commit_opportunity setup leaks bounds rosters
      fresh guard next wholeProfile profile refs source embedding refsBefore offset aligned
      current currentAgree currentHistory serial currentSelected currentCandidate currentUnused
        currentSerials currentPublished network remaining absent currentReady
          currentTimely currentVacant currentUnsent last
    simpa only [same, receipts, counters] using completed
  · exact PMF.bind_const _ expected

private theorem binding_opportunity_provenance
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (current : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (currentReady : current.application.config.cut.Ready event)
    (serial : Nat)
    (currentSelected : reactiveFreshSlot (current.observe
      (application setup leaks) owner).application = some serial)
    (currentCandidate : current.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (currentSerials : current.network.SerialsBeforeNext)
    (currentPublished : current.network.Satisfies fun message =>
      message.id ∈ current.network.ledger.map Message.id)
    (currentUnsent : (runtime setup).eventRecorded leaks (current.recall owner) event = false)
    (last : (current.recall owner).length + 1 =
      rosterOffset setup rosters owner event + (rosters event).count owner)
    (remaining : List Player) (absent : owner ∉ remaining)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters profile) network
      (.player owner :: remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
        current).support) :
    ∃ before immediate : (application setup leaks).Execution,
      before.application = current.application ∧ before.network.ledger = current.network.ledger ∧
      before.receipts = current.receipts ∧
      before.network.nextSerial = current.network.nextSerial ∧
      before.network.SerialsBeforeNext ∧
      immediate ∈ ((sourceServicePolicy setup leaks profile owner (before.recall owner)
        (before.observe (application setup leaks) owner)).bind fun response =>
          (runtime setup).interactionStep leaks
            (fun _ => (application setup leaks).silentPolicy) network (.includeLatest event owner)
            (before.respond (application setup leaks) owner response)).support ∧
      final.application = immediate.application ∧ final.network.ledger = immediate.network.ledger ∧
      final.receipts = immediate.receipts ∧
      final.network.nextSerial = immediate.network.nextSerial ∧
      final.network.Satisfies
        (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  let := Fintype.ofFinite Player
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters profile
  let transport : Player → app.Policy := fun _ => app.silentPolicy
  change final ∈ ((runtime setup).runInteractionPlan leaks players network
    (.player owner :: remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
      current).support at reached
  rw [List.cons_append] at reached
  simp only [runInteractionPlan, interactionStep, interactionInstruction, PMF.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
    ReactiveApplication.invoke, ReactiveApplication.Execution.activation_samples,
    PMF.bind_map, PMF.bind_bind, Function.comp_def] at reached
  obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  let activated := current.sampledActivation app owner sample
  have physical (response : app.Action)
      (supported : response ∈ (sourceServicePolicy setup leaks profile owner
        (activated.recall owner) (activated.observe app owner)).support) :
      ∃ choice : PublicationResult (L.Val payload), response =
        (runtime setup).reactiveBinding leaks owner event payload choice serial := by
    rw [sourceServicePolicy_at_event setup leaks profile owner activated event
      (ownTurn?_of_ready setup current.application currentReady owned) owned,
      PMF.support_map] at supported
    obtain ⟨choice, _, equal⟩ := supported
    refine ⟨cast (congrArg EventGraph.EventField.Action outputEq) choice, ?_⟩
    apply equal.symm.trans
    simpa only [cast_cast, cast_eq] using serviceDecision_binding_fresh (runtime setup) leaks
      activated owner event payload outputEq codeEq node serial currentSelected currentCandidate
        (cast (congrArg EventGraph.EventField.Action outputEq) choice)
  have responseLaw := sourceServiceLastPolicy_submissions setup leaks rosters profile owner
    (activated.recall owner) (activated.observe app owner) event
    (ownTurn?_of_ready setup current.application currentReady owned) owned currentUnsent
      last (fun response supported => by
        obtain ⟨choice, rfl⟩ := physical response supported
        cases choice <;> exact Option.some_ne_none _)
  change players owner (activated.recall owner) (activated.observe app owner) = _ at responseLaw
  rw [responseLaw] at reached
  obtain ⟨response, chosen, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have sourceChosen := chosen
  obtain ⟨choice, responseEq⟩ := physical response chosen
  have responseSole : (activated.respond app owner response).application.publicView.SoleReady
      event := by
    rw [((runtime setup).reactive_respond_application leaks activated owner response).2]
    exact soleReady_of_ready setup current.application currentReady
  rw [sourceServiceLastPolicy_foreign_tail setup leaks rosters profile network event owner owned
    remaining absent (activated.respond app owner response) responseSole, responseEq] at tail
  let readout (point : app.Execution) :=
    (point.application, point.network.ledger, point.receipts, point.network.nextSerial)
  have mapped : readout final ∈ (((runtime setup).runInteractionPlan leaks transport network
      (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
        (activated.respond app owner
          ((runtime setup).reactiveBinding leaks owner event payload choice serial))).map
            readout).support := PMF.support_map .. ▸ ⟨final, tail, rfl⟩
  have delayed (opening : Option (Raw L)) := (runtime setup).rawBinding_delayed_inclusion leaks
    bounds transport (fun who past view response supported =>
      bounds.silent_compiled (runtime setup) leaks who past view response supported) network
    activated owner event payload outputEq codeEq node
    (soleReady_of_ready setup current.application currentReady) owned currentReady
      (currentPublished.learn owner sample) (currentSerials.learn owner sample) serial opening
        remaining
  have delayedChoice : ((runtime setup).runInteractionPlan leaks transport network
      (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
        (activated.respond app owner
          ((runtime setup).reactiveBinding leaks owner event payload choice serial))).map readout =
      ((runtime setup).interactionStep leaks transport network (.includeLatest event owner)
        (activated.respond app owner
          ((runtime setup).reactiveBinding leaks owner event payload choice serial))).map
            readout := by
    cases choice with
    | failure => exact delayed none
    | success value => exact delayed (some ⟨payload, value⟩)
  rw [delayedChoice] at mapped
  obtain ⟨immediate, included, equal⟩ := PMF.support_map .. ▸ mapped
  have publishedFinal : final.network.Satisfies fun message =>
      message.id ∈ final.network.ledger.map Message.id := by
    have publish (submission : WitnessedSubmission (graph setup))
        (addressed : submission.call.packet.event? (graph setup) = some event)
        (supported : final ∈ ((runtime setup).runInteractionPlan leaks transport network
          (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
            (activated.respond app owner ⟨some submission⟩)).support) :=
      (runtime setup).submission_silent_settled_published leaks transport network owner activated
        submission event addressed (currentPublished.learn owner sample)
        (currentSerials.learn owner sample)
        (fun current who response _ _ chosen => app.silentPolicy_cases _ _ response chosen)
        remaining final supported
    cases choice with
    | failure => exact publish _ rfl tail
    | success value => exact publish _ rfl tail
  refine ⟨activated, immediate, rfl, rfl, rfl, rfl, currentSerials.learn owner sample, ?_,
    (congrArg Prod.fst equal).symm, (congrArg (fun value => value.2.1) equal).symm,
    (congrArg (fun value => value.2.2.1) equal).symm,
    (congrArg (fun value => value.2.2.2) equal).symm, publishedFinal⟩
  rw [PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨response, sourceChosen, ?_⟩
  rwa [responseEq]


/-- Every actual result of the complete binding roster has the same full
application and receipts as a supported immediate source binding at its last
sampled owner input. The sampled input itself has the original application and
allocation counters. This transports dynamic catalogue invariants without
assuming that the catalogue stayed equal to its initial value. -/
theorem sourceServiceLastPolicy_binding_provenance
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (initial : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (ready : initial.application.config.cut.Ready event)
    (serial : Nat)
    (selected : reactiveFreshSlot (initial.observe
      (application setup leaks) owner).application = some serial)
    (candidate : initial.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (visited remaining : List Player) (absent : owner ∉ remaining)
    (position : rosters event = visited ++ owner :: remaining)
    (counted : (initial.recall owner).length = rosterOffset setup rosters owner event)
    (unsent : (runtime setup).eventRecorded leaks (initial.recall owner) event = false)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters profile) network
      ((rosters event).map ServiceInstruction.player ++
        [.includeLatest event owner]) initial).support) :
    ∃ before immediate : (application setup leaks).Execution,
      before.application = initial.application ∧ before.network.ledger = initial.network.ledger ∧
      before.receipts = initial.receipts ∧
      before.network.nextSerial = initial.network.nextSerial ∧
      before.network.SerialsBeforeNext ∧
      immediate ∈ ((sourceServicePolicy setup leaks profile owner (before.recall owner)
        (before.observe (application setup leaks) owner)).bind fun response =>
          (runtime setup).interactionStep leaks
            (fun _ => (application setup leaks).silentPolicy) network (.includeLatest event owner)
            (before.respond (application setup leaks) owner response)).support ∧
      final.application = immediate.application ∧ final.network.ledger = immediate.network.ledger ∧
      final.receipts = immediate.receipts ∧
      final.network.nextSerial = immediate.network.nextSerial ∧
      final.network.Satisfies
        (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters profile
  have total : (rosters event).count owner = visited.count owner + 1 := by
    rw [position, List.count_append, List.count_cons_self, List.count_eq_zero.mpr absent]
  have waiting : (initial.recall owner).length + visited.count owner <
      rosterOffset setup rosters owner event + (rosters event).count owner := by
    rw [counted, total]
    omega
  rw [position, List.map_append, List.map_cons, List.append_assoc,
    (runtime setup).runInteractionPlan_append] at reached
  obtain ⟨current, priorSupport, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨same, ledger, receipts, counters, packets, _⟩ :=
    sourceServiceLastPolicy_waiting_data setup leaks rosters profile network event owner owned
      visited initial current (soleReady_of_ready setup initial.application ready) waiting _
      published priorSupport
  have currentReady : current.application.config.cut.Ready event := by rw [same]; exact ready
  have currentSelected : reactiveFreshSlot (current.observe app owner).application =
      some serial := by
    change reactiveFreshSlot (app.observePlayer current.application owner) = _
    rw [same]
    exact selected
  have currentCandidate : current.application.candidates.lookup (owner, .prepared serial) =
      .fresh := by rw [same]; exact candidate
  have currentSerials := (runtime setup).runInteractionPlan_serials leaks players network
    (visited.map ServiceInstruction.player) initial current serials priorSupport
  have currentPublished : current.network.Satisfies fun message =>
      message.id ∈ current.network.ledger.map Message.id := by rwa [ledger]
  have pureReplay := priorSupport
  rw [sourceServiceLastPolicy_waiting_law setup leaks rosters profile network event owner owned
    visited initial (soleReady_of_ready setup initial.application ready) waiting] at pureReplay
  have currentUnsent := (silent_window_eventRecorded setup leaks network visited initial current
    pureReplay owner event).trans unsent
  have fixed : (ServiceInstruction.wire : ServiceInstruction (graph setup)) ∉
      visited.map ServiceInstruction.player := by simp
  have currentCount := fixed_plan_response_counts setup leaks network players
    (visited.map ServiceInstruction.player) fixed initial current priorSupport owner
  simp only [List.filterMap_map, Function.comp_def, instructionActor,
    List.filterMap_some] at currentCount
  have last : (current.recall owner).length + 1 =
      rosterOffset setup rosters owner event + (rosters event).count owner := by
    rw [currentCount, counted, total]
    omega
  obtain ⟨before, immediate, applicationEq, ledgerEq, receiptEq, counterEq, nextSerials, supported,
    applicationFinal, ledgerFinal, receiptsFinal, countersFinal, publishedFinal⟩ :=
      binding_opportunity_provenance setup leaks bounds rosters
      profile network current event owner payload outputEq codeEq node owned
        currentReady serial currentSelected currentCandidate currentSerials currentPublished
          currentUnsent last remaining absent final reached
  exact ⟨before, immediate, applicationEq.trans same, ledgerEq.trans ledger,
    receiptEq.trans receipts,
    counterEq.trans counters, nextSerials, supported, applicationFinal, ledgerFinal, receiptsFinal,
    countersFinal, publishedFinal⟩

end Vegas
