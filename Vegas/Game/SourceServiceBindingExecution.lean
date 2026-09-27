/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingPhase

/-! # Joint execution at the source binding opportunity

The original binding lottery is disintegrated inside the actual service
runner. The equality retains the entire native execution, including passive
samples, all players' responses and the dynamically updated private catalogue.
No traffic projection or conditional independence is assumed.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The final owner opportunity draws the source kernel and then runs the
actual foreign response suffix and protected inclusion. -/
theorem sourceServiceLastPolicy_commit_execution
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
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
    (network : (runtime setup).NetworkPolicy leaks)
    (remaining : List Player) (absent : owner ∉ remaining) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (_granted : execution.application.serviceGrant = some event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_last : (execution.recall owner).length + 1 =
        rosterOffset setup rosters owner event + (rosters event).count owner),
    (runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      (.player owner :: remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
      execution =
      ((application setup leaks).observePending owner execution.network.pending).bind fun sample =>
        (commitKernel profile (source.view owner)).bind fun choice =>
          (runtime setup).runInteractionPlan leaks
            (fun _ => (application setup leaks).replayPolicy) network
            (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
            ((execution.sampledActivation (application setup leaks) owner sample).respond
              (application setup leaks) owner
              ((runtime setup).reactiveBinding leaks owner event payload choice serial)) := by
  intro index event granted unsent last
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
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
  simp only [List.cons_append, runInteractionPlan, interactionStep, interactionInstruction,
    FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, ReactiveApplication.invoke,
    ReactiveApplication.Execution.activation_samples, FinDist.bind_map, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro sample _
  let activated := execution.sampledActivation app owner sample
  have sourceLaw := sourceServicePolicy_commit setup leaks fresh guard next wholeProfile profile
    refs source embedding refsBefore offset aligned activated agree history granted
  have raw (choice : PublicationResult (L.Val payload)) :=
    serviceDecision_binding_fresh (runtime setup) leaks activated owner event payload
      outputEq codeEq node serial selected candidate choice
  have responseLaw : players owner (activated.recall owner) (activated.observe app owner) =
      (commitKernel profile (source.view owner)).map fun choice =>
        (runtime setup).reactiveBinding leaks owner event payload choice serial := by
    dsimp only [players]
    rw [sourceServiceLastPolicy_submissions setup leaks rosters wholeProfile owner
      (activated.recall owner) (activated.observe app owner) event granted owned unsent last]
    · rw [sourceLaw]
      apply FinDist.map_congr_of_eq_on_support
      intro choice _
      exact raw choice
    · intro response supported
      rw [sourceLaw, FinDist.support_map] at supported
      obtain ⟨choice, _, equal⟩ := supported
      have same : response =
          (runtime setup).reactiveBinding leaks owner event payload choice serial :=
        equal.symm.trans (raw choice)
      rw [same]
      cases choice <;> exact Option.some_ne_none _
  change (players owner (activated.recall owner) (activated.observe app owner)).bind _ = _
  rw [responseLaw, FinDist.bind_map]
  apply FinDist.bind_congr
  intro choice _
  apply sourceServiceLastPolicy_foreign_tail setup leaks rosters wholeProfile network event owner
    owned remaining absent
  have observable := (runtime setup).reactive_respond_application leaks activated owner
    ((runtime setup).reactiveBinding leaks owner event payload choice serial)
  exact (congrArg PublicView.serviceGrant observable.2).trans granted

/-- The full roster retains the replay prefix, the sampled owner activation,
the original source choice, and the entire native suffix in one exact law. -/
theorem sourceServiceLastPolicy_commit_window_execution
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
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
    (network : (runtime setup).NetworkPolicy leaks)
    (visited remaining : List Player) (absent : owner ∉ remaining) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (_position : rosters event = visited ++ owner :: remaining)
      (_granted : execution.application.serviceGrant = some event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length = rosterOffset setup rosters owner event),
    (runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) execution =
      ((runtime setup).runInteractionPlan leaks
        (fun _ => (application setup leaks).replayPolicy) network
        (visited.map ServiceInstruction.player) execution).bind fun current =>
          ((application setup leaks).observePending owner current.network.pending).bind
            fun sample =>
            (commitKernel profile (source.view owner)).bind fun choice =>
              (runtime setup).runInteractionPlan leaks
                (fun _ => (application setup leaks).replayPolicy) network
                (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
                ((current.sampledActivation (application setup leaks) owner sample).respond
                  (application setup leaks) owner
                  ((runtime setup).reactiveBinding leaks owner event payload choice serial)) := by
  intro index event position granted unsent counted
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have total : (rosters event).count owner = visited.count owner + 1 := by
    rw [position, List.count_append, List.count_cons_self, List.count_eq_zero.mpr absent]
  have before : (execution.recall owner).length + visited.count owner <
      rosterOffset setup rosters owner event + (rosters event).count owner := by
    rw [counted, total]
    omega
  rw [position, List.map_append, List.map_cons, List.append_assoc,
    (runtime setup).runInteractionPlan_append,
    sourceServiceLastPolicy_waiting_law setup leaks rosters wholeProfile network event owner owned
      visited execution granted before]
  apply FinDist.bind_congr
  intro current reached
  have reachedPolicy := reached
  rw [← sourceServiceLastPolicy_waiting_law setup leaks rosters wholeProfile network event owner
    owned visited execution granted before] at reachedPolicy
  obtain ⟨same, _, _, _, _, _⟩ := sourceServiceLastPolicy_waiting_data setup leaks rosters
    wholeProfile network event owner owned visited execution current granted before
      (fun _ => True) ⟨by simp, by simp, by simp, by simp⟩ reachedPolicy
  have currentAgree : refs.Agrees source.state current.application.config.store := by
    rw [same]
    exact agree
  have currentHistory : decodeHistory setup.program (current.application.config.history.map
      (setup.eventGraph.fromModeCompletion .sequential)) = source.history := by
    rw [same]
    exact history
  have currentSelected : reactiveFreshSlot (current.observe app owner).application =
      some serial := by
    change reactiveFreshSlot (app.observePlayer current.application owner) = _
    rw [same]
    exact selected
  have currentCandidate : current.application.candidates.lookup (owner, .prepared serial) =
      .fresh := by rw [same]; exact candidate
  have currentCount := fixed_plan_response_counts setup leaks network players
    (visited.map ServiceInstruction.player) (by simp) execution current reachedPolicy owner
  simp only [instructionActor, List.filterMap_map, Function.comp_def,
    List.filterMap_some] at currentCount
  have atLast : (current.recall owner).length + 1 =
      rosterOffset setup rosters owner event + (rosters event).count owner := by
    rw [currentCount, counted, total]
    omega
  exact sourceServiceLastPolicy_commit_execution setup leaks rosters fresh guard next wholeProfile
    profile refs source embedding refsBefore offset aligned current currentAgree currentHistory
    serial currentSelected currentCandidate network remaining absent (same ▸ granted)
    ((replay_window_eventRecorded setup leaks network visited execution current reached owner
      event).trans unsent) atLast

end Vegas.SourceProgram.RevealService
