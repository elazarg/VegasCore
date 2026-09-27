/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceWaiting
import Vegas.Game.SourceServiceBindingRoster
import Vegas.Game.RevealServiceRosterCounts
import Vegas.Pending.ReactiveServiceRecall

/-! # A source binding across its complete finite response roster

The limiting compiler waits until the last owner opportunity. Every earlier
and later native activation remains present, with actual passive observations
and known-envelope replays. The eventual binding retains its original source
lottery. This is an execution theorem; a fully mixed timing sequence is still
required for sequential-equilibrium transport.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem include_players_eq
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (first second : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (execution : (application setup leaks).Execution) :
    (runtime setup).interactionStep leaks first network (.includeLatest event owner) execution =
      (runtime setup).interactionStep leaks second network
        (.includeLatest event owner) execution := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind]
  unfold reactiveLatest
  split <;> rfl

private theorem foreign_tail_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (visits : List Player) (absent : owner ∉ visits)
    (initial : (application setup leaks).Execution)
    (granted : initial.application.serviceGrant = some event) :
    (runtime setup).runInteractionPlan leaks
        (sourceServiceLastPolicy setup leaks rosters profile) network
        (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) initial =
      (runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).replayPolicy)
        network (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) initial := by
  let app := application setup leaks
  induction visits generalizing initial with
  | nil =>
      simpa only [List.map_nil, List.nil_append, runInteractionPlan, FinDist.bind_pure] using
        include_players_eq setup leaks _ _ network event owner initial
  | cons who rest ih =>
      have foreign : who ≠ owner := fun same => absent (by simp only [same, List.mem_cons_self])
      have restAbsent : owner ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      simp only [List.map_cons, List.cons_append, runInteractionPlan, interactionStep,
        interactionInstruction, FinDist.pure_bind, ReactiveApplication.dispatch,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro sample _
      let activated := initial.sampledActivation app who sample
      have law := sourceServiceLastPolicy_wait setup leaks rosters profile who
        (activated.recall who) (activated.observe app who) event granted
          (Or.inl (fun equal => foreign (Option.some.inj (equal.symm.trans owned))))
      change (sourceServiceLastPolicy setup leaks rosters profile who
        (activated.recall who) (activated.observe app who)).bind _ =
        (app.replayPolicy (activated.recall who) (activated.observe app who)).bind _
      rw [law]
      apply FinDist.bind_congr
      intro response supported
      apply ih restAbsent
      rcases app.replayPolicy_cases _ _ response supported with rfl | ⟨id, rfl⟩ <;> exact granted

private theorem replay_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (fun _ => (application setup leaks).replayPolicy) network
        (visits.map ServiceInstruction.player) initial).support)
    (owner : Player) (event : (graph setup).EventId) :
    (runtime setup).eventRecorded leaks (final.recall owner) event =
      (runtime setup).eventRecorded leaks (initial.recall owner) event := by
  classical
  let app := application setup leaks
  induction visits generalizing initial with
  | nil => cases FinDist.mem_support_pure.mp reached; rfl
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map,
        FinDist.bind_bind] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨response, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      rw [ih _ reached]
      by_cases same : owner = who
      · subst who
        rcases app.replayPolicy_cases _ _ response supported with rfl | ⟨id, rfl⟩ <;>
          simp only [eventRecorded, ReactiveApplication.Execution.respond, ↓reduceIte,
            List.any_append, List.any_cons, List.any_nil, submittedEvent?, reduceCtorEq,
            decide_false, Bool.or_false] <;> rfl
      · rw [app.respond_recall_other _ who owner same]
        rfl

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
    ∀ (_granted : execution.application.serviceGrant = some event)
      (ready : execution.application.config.cut.Ready event)
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
  intro granted ready timely vacant unsent last
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
  let transport : Player → app.Policy := fun _ => app.replayPolicy
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
  have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq := by
    cases viewed : nodeView (graph setup) event with
    | sample otherPayload law kind code => cases kind.symm.trans outputEq
    | resolve other otherPayload binding checks kind code => cases kind.symm.trans outputEq
    | bind other otherPayload kind code =>
        obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj (kind.symm.trans outputEq)
        rfl
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have step : (runtime setup).interactionStep leaks players network (.player owner) execution =
      (app.observePending owner execution.network.pending).bind (fun sample =>
        let activated := execution.sampledActivation app owner sample
        (players owner (activated.recall owner) (activated.observe app owner)).map
          (activated.respond app owner)) := by
    simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      ReactiveApplication.invoke, ReactiveApplication.Execution.activation_samples,
      FinDist.bind_map]
    rfl
  change ((runtime setup).runInteractionPlan leaks players network
    (.player owner :: remaining.map ServiceInstruction.player ++
      [.includeLatest event owner]) execution).map result = _
  rw [List.cons_append, runInteractionPlan, FinDist.map_bind, step, FinDist.bind_bind]
  simp only [FinDist.bind_map]
  let expected := (commitKernel profile (source.view owner)).map fun choice =>
    (execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice),
      execution.receipts ++ [((owner, execution.network.nextSerial owner), true)])
  trans (app.observePending owner execution.network.pending).bind (fun _ => expected)
  · apply FinDist.bind_congr
    intro sample _
    let activated := execution.sampledActivation app owner sample
    have sourceLaw := sourceServicePolicy_commit setup leaks fresh guard next wholeProfile profile
      refs source embedding refsBefore offset aligned activated agree history granted
    have submits : ∀ response ∈ (sourceServicePolicy setup leaks wholeProfile owner
        (activated.recall owner) (activated.observe app owner)).support,
        response.transmission ≠ none := by
      intro response supported
      rw [sourceLaw, FinDist.support_map] at supported
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
        (activated.recall owner) (activated.observe app owner) event granted owned unsent last
          submits
    change (players owner (activated.recall owner) (activated.observe app owner)).bind _ = _
    rw [responseLaw]
    have delayed := sourceServicePolicy_commit_delayed_service setup leaks fresh guard next
      wholeProfile profile refs source embedding refsBefore offset aligned activated agree history
        serial selected candidate unused (serials.learn owner sample) (published.learn owner sample)
        bounds transport (fun who past view response supported =>
          bounds.replay_compiled (runtime setup) leaks who past view response supported)
        network remaining granted ready timely vacant
    rw [FinDist.map_bind] at delayed
    apply Eq.trans ?_ delayed
    apply FinDist.bind_congr
    intro response _
    apply congrArg (FinDist.map result)
    apply foreign_tail_law setup leaks rosters wholeProfile network event owner owned
      remaining absent
    exact (congrArg PublicView.serviceGrant ((runtime setup).reactive_respond_application leaks
      activated owner response).2).trans granted
  · exact FinDist.bind_const _ expected

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
      (_granted : execution.application.serviceGrant = some event)
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
  intro position granted ready timely vacant unsent counted
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
    (runtime setup).runInteractionPlan_append, FinDist.map_bind]
  trans ((runtime setup).runInteractionPlan leaks players network
    (visited.map ServiceInstruction.player) execution).bind (fun _ => expected)
  · apply FinDist.bind_congr
    intro current reached
    obtain ⟨same, ledger, receipts, counters, packets, _⟩ :=
      sourceServiceLastPolicy_waiting_data setup leaks rosters wholeProfile network event owner
        owned visited execution current granted before _ published reached
    have currentGrant : current.application.serviceGrant = some event := by rw [same]; exact granted
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
      owned visited execution granted before] at pureReplay
    have currentUnsent := (replay_recorded setup leaks network visited execution current
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
        currentSerials currentPublished network remaining absent currentGrant currentReady
          currentTimely currentVacant currentUnsent last
    simpa only [same, receipts, counters] using completed
  · exact FinDist.bind_const _ expected

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
    (currentGrant : current.application.serviceGrant = some event)
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
            (fun _ => (application setup leaks).replayPolicy) network (.includeLatest event owner)
            (before.respond (application setup leaks) owner response)).support ∧
      final.application = immediate.application ∧ final.network.ledger = immediate.network.ledger ∧
      final.receipts = immediate.receipts ∧
      final.network.nextSerial = immediate.network.nextSerial := by
  let := Fintype.ofFinite Player
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters profile
  let transport : Player → app.Policy := fun _ => app.replayPolicy
  change final ∈ ((runtime setup).runInteractionPlan leaks players network
    (.player owner :: remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
      current).support at reached
  rw [List.cons_append] at reached
  simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
    ReactiveApplication.invoke, ReactiveApplication.Execution.activation_samples,
    FinDist.bind_map, FinDist.bind_bind] at reached
  obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  let activated := current.sampledActivation app owner sample
  have physical (response : app.Action)
      (supported : response ∈ (sourceServicePolicy setup leaks profile owner
        (activated.recall owner) (activated.observe app owner)).support) :
      ∃ choice : PublicationResult (L.Val payload), response =
        (runtime setup).reactiveBinding leaks owner event payload choice serial := by
    rw [sourceServicePolicy_at_event setup leaks profile owner activated event
      currentGrant owned, FinDist.support_map] at supported
    obtain ⟨choice, _, equal⟩ := supported
    refine ⟨cast (congrArg EventGraph.EventField.Action outputEq) choice, ?_⟩
    apply equal.symm.trans
    simpa only [cast_cast, cast_eq] using serviceDecision_binding_fresh (runtime setup) leaks
      activated owner event payload outputEq codeEq node serial currentSelected currentCandidate
        (cast (congrArg EventGraph.EventField.Action outputEq) choice)
  have responseLaw := sourceServiceLastPolicy_submissions setup leaks rosters profile owner
    (activated.recall owner) (activated.observe app owner) event currentGrant owned currentUnsent
      last (fun response supported => by
        obtain ⟨choice, rfl⟩ := physical response supported
        cases choice <;> exact Option.some_ne_none _)
  change players owner (activated.recall owner) (activated.observe app owner) = _ at responseLaw
  rw [responseLaw] at reached
  obtain ⟨response, chosen, tail⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have sourceChosen := chosen
  obtain ⟨choice, responseEq⟩ := physical response chosen
  have responseGrant : (activated.respond app owner response).application.serviceGrant =
      some event := (congrArg PublicView.serviceGrant ((runtime setup).reactive_respond_application
        leaks activated owner response).2).trans currentGrant
  rw [foreign_tail_law setup leaks rosters profile network event owner owned remaining absent
    (activated.respond app owner response) responseGrant, responseEq] at tail
  let readout (point : app.Execution) :=
    (point.application, point.network.ledger, point.receipts, point.network.nextSerial)
  have mapped : readout final ∈ (((runtime setup).runInteractionPlan leaks transport network
      (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
        (activated.respond app owner
          ((runtime setup).reactiveBinding leaks owner event payload choice serial))).map
            readout).support := FinDist.support_map .. ▸ ⟨final, tail, rfl⟩
  have delayed (opening : Option (Raw L)) := (runtime setup).rawBinding_delayed_inclusion leaks
    bounds transport (fun who past view response supported =>
      bounds.replay_compiled (runtime setup) leaks who past view response supported) network
    activated owner event payload outputEq codeEq node currentGrant owned currentReady
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
  obtain ⟨immediate, included, equal⟩ := FinDist.support_map .. ▸ mapped
  refine ⟨activated, immediate, rfl, rfl, rfl, rfl, currentSerials.learn owner sample, ?_,
    (congrArg Prod.fst equal).symm, (congrArg (fun value => value.2.1) equal).symm,
    (congrArg (fun value => value.2.2.1) equal).symm,
    (congrArg (fun value => value.2.2.2) equal).symm⟩
  rw [FinDist.support_bind]
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
    (granted : initial.application.serviceGrant = some event)
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
            (fun _ => (application setup leaks).replayPolicy) network (.includeLatest event owner)
            (before.respond (application setup leaks) owner response)).support ∧
      final.application = immediate.application ∧ final.network.ledger = immediate.network.ledger ∧
      final.receipts = immediate.receipts ∧
      final.network.nextSerial = immediate.network.nextSerial := by
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
  obtain ⟨current, priorSupport, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨same, ledger, receipts, counters, packets, _⟩ :=
    sourceServiceLastPolicy_waiting_data setup leaks rosters profile network event owner owned
      visited initial current granted waiting _ published priorSupport
  have currentGrant : current.application.serviceGrant = some event := by rw [same]; exact granted
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
    visited initial granted waiting] at pureReplay
  have currentUnsent := (replay_recorded setup leaks network visited initial current pureReplay
    owner event).trans unsent
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
    applicationFinal, ledgerFinal, receiptsFinal, countersFinal⟩ :=
      binding_opportunity_provenance setup leaks bounds rosters
      profile network current event owner payload outputEq codeEq node currentGrant owned
        currentReady serial currentSelected currentCandidate currentSerials currentPublished
          currentUnsent last remaining absent final reached
  exact ⟨before, immediate, applicationEq.trans same, ledgerEq.trans ledger,
    receiptEq.trans receipts,
    counterEq.trans counters, nextSerials, supported, applicationFinal, ledgerFinal, receiptsFinal,
    countersFinal⟩

end Vegas.SourceProgram.RevealService
