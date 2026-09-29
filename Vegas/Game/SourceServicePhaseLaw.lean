/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceExecution

/-! # Source transition laws of complete native service blocks

The actual grant, activation roster, protected service and expiry are evaluated
at operational source boundaries. Their deterministic source-state readout has
the original source transition law. Native traffic and recalls remain in the
physical runner and are integrated out only by this stated readout.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem ServiceBoundary.sample_state_law [Fintype Player]
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {openNames : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) openNames)
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.sample name fresh distribution next))
    (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.sample name fresh distribution next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.sample name fresh distribution next) profile refs source.revelations source.registry
      embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (boundary : ServiceBoundary setup leaks rosters initial source refs offset execution)
    (network : (runtime setup).NetworkPolicy leaks) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      (rosterBlock setup rosters (embedding.event ⟨0, by simp [eventCount]⟩)) execution).map
        (fun final => decodeSourcePrefix? (.sample name fresh distribution next) refs
          source.registry source.revelations embedding.ref 1 final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion .sequential)))) =
      (ProtocolState.behavioralStateStep (.sample name fresh distribution next)
        profile (ProtocolState.entry _ source)).map some := by
  have kernel := congrArg (PMF.map some)
    (ProtocolState.behavioralStateStep_sample_entry profile source)
  simp only [PMF.map_comp, Function.comp_def] at kernel
  apply Eq.trans ?_ kernel.symm
  let index : Fin (eventCount (.sample name fresh distribution next)) :=
    ⟨0, by simp [eventCount]⟩
  let event : (graph setup).EventId := embedding.event index
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
  have atRank : event.val = offset := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have outputEq : (graph setup).outputLayout event = .publicData payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs distribution) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event =
      .sample payload (compilePublicDist refs distribution) outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_sample _ _
  have chance : (graph setup).actor? event = none := by
    change (toEventGraph setup.program).actor? event = none
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  obtain ⟨granted, grantBoundary, grant, _grantApp, _grantRecall, grantLaw⟩ :=
    boundary.grant players network event
  have ready := grantBoundary.ready event atRank
  have phase := sourceServiceLastPolicy_sample_roster setup leaks rosters wholeProfile source refs
    granted grantBoundary.agrees event ready outputEq distribution codeEq node grant
      grantBoundary.published network (event.val + 1)
  let readout (result : (graph setup).Config × List (MessageId Player × Bool)) :=
    decodeSourcePrefix? (.sample name fresh distribution next) refs source.registry
      source.revelations embedding.ref 1 result.1.store
      (decodeHistory setup.program (result.1.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  have mapped := congrArg (PMF.map readout) phase
  simp only [PMF.map_comp, Function.comp_def] at mapped
  change ((runtime setup).runInteractionPlan leaks players network
    (rosterBlock setup rosters event) execution).map _ = _
  rw [rosterBlock, chance]
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    runInteractionPlan, grantLaw,
    PMF.pure_bind]
  refine mapped.trans ?_
  rw [← PMF.bind_pure_comp, Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro value _
  apply congrArg PMF.pure
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none := by
    have action := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
    simpa [event, index, outputEq, decodeEventAction] using action
  have completed := grantBoundary.toSourceCheckpoint.sample name event atRank ready outputEq
    (fun ref => refsBefore ref index) decoded value
  have recovered := completed.decode next (fun tail => embedding.ref tail.succ)
  dsimp only [readout]
  rw [decodeSourcePrefix?_sample]
  exact congrArg (Option.map Sum.inr) recovered

omit [DecidableEq Player] in
private theorem last_owner_split (owner : Player) (visits : List Player)
    (present : owner ∈ visits) :
    ∃ before after, visits = before ++ owner :: after ∧ owner ∉ after := by
  classical
  induction visits with
  | nil => simp only [List.not_mem_nil] at present
  | cons first rest ih =>
      by_cases later : owner ∈ rest
      · obtain ⟨before, after, same, absent⟩ := ih later
        exact ⟨first :: before, after, by simp only [same, List.cons_append], absent⟩
      · have same : owner = first := (List.mem_cons.mp present).resolve_right later
        subst first
        exact ⟨[], rest, rfl, later⟩

theorem ServiceBoundary.commit_state_law [Fintype Player]
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile refs source.revelations source.registry
      embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (boundary : ServiceBoundary setup leaks rosters initial source refs offset execution)
    (bounds : MessageBounds (graph setup))
    (network : (runtime setup).NetworkPolicy leaks)
    (opportunity : owner ∈ rosters (embedding.event ⟨0, by simp [eventCount]⟩)) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      (rosterBlock setup rosters (embedding.event ⟨0, by simp [eventCount]⟩)) execution).map
        (fun final => decodeSourcePrefix? (.commit name owner fresh guard next) refs
          source.registry source.revelations embedding.ref 1 final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion .sequential)))) =
      (ProtocolState.behavioralStateStep (.commit name owner fresh guard next)
        profile (ProtocolState.entry _ source)).map some := by
  have kernel := congrArg (PMF.map some)
    (ProtocolState.behavioralStateStep_commit_entry profile source)
  simp only [PMF.map_comp, Function.comp_def] at kernel
  apply Eq.trans ?_ kernel.symm
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event : (graph setup).EventId := embedding.event index
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
  have atRank : event.val = offset := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  obtain ⟨visited, remaining, position, absent⟩ :=
    last_owner_split owner (rosters event) opportunity
  obtain ⟨granted, grantBoundary, grant, _grantApp, _grantRecall, grantLaw⟩ :=
    boundary.grant players network event
  have ready := grantBoundary.ready event atRank
  obtain ⟨selected, candidate, unused, vacant⟩ :=
    grantBoundary.binding_resources event atRank owner
  have phase := sourceServiceLastPolicy_commit_roster setup leaks bounds rosters fresh guard next
    wholeProfile profile refs source embedding refsBefore offset aligned granted
      grantBoundary.agrees grantBoundary.history
      (granted.application.publicView.bindingCount owner) selected candidate unused
      grantBoundary.serials grantBoundary.published network visited remaining absent position
      grant ready (grantBoundary.timely event atRank (by simp only [owned, Option.isSome_some]))
      vacant (grantBoundary.unsent owner event atRank.ge)
      (grantBoundary.response_offset event atRank owner)
  let inclusion := (runtime setup).runInteractionPlan leaks players network
    ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) granted
  have settled : ∀ middle ∈ inclusion.support, ¬middle.application.config.cut.Ready event := by
    intro middle reached
    have observed : (middle.application.config, middle.receipts) ∈
        (inclusion.map fun point => (point.application.config, point.receipts)).support :=
      PMF.support_map .. ▸ ⟨middle, reached, rfl⟩
    rw [phase, PMF.support_map] at observed
    obtain ⟨choice, _, same⟩ := observed
    have configuration := congrArg Prod.fst same
    dsimp only at configuration
    intro active
    rw [← configuration] at active
    exact active.1 (by simp [EventOrder.Cut.complete, event, index])
  have full := ((runtime setup).settled_tail_config_receipts leaks players network inclusion event
    (event.val + 1) settled).trans phase
  let readout (result : (graph setup).Config × List (MessageId Player × Bool)) :=
    decodeSourcePrefix? (.commit name owner fresh guard next) refs source.registry
      source.revelations embedding.ref 1 result.1.store
      (decodeHistory setup.program (result.1.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  have mapped := congrArg (PMF.map readout) full
  simp only [PMF.map_comp, Function.comp_def] at mapped
  have executionEq : (runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution = inclusion.bind
        ((runtime setup).runInteractionPlan leaks players network
          (List.replicate (event.val + 1) .tick ++ [.expire event])) := by
    rw [rosterBlock_of_owner setup rosters event owner owned,
      (runtime setup).runInteractionPlan_append]
    simp only [runInteractionPlan, grantLaw, PMF.pure_bind]
    have splitPlan :
        ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner] ++
          List.replicate (event.val + 1) .tick ++ [.expire event] :
            List (ServiceInstruction (graph setup))) =
          ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) ++
            (List.replicate (event.val + 1) .tick ++ [.expire event]) :=
      List.append_assoc _ _ _
    rw [splitPlan, (runtime setup).runInteractionPlan_append]
  change ((runtime setup).runInteractionPlan leaks players network
    (rosterBlock setup rosters event) execution).map _ = _
  rw [executionEq]
  refine mapped.trans ?_
  rw [← PMF.bind_pure_comp, Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro choice _
  apply congrArg PMF.pure
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
        some (.commit owner name payload choice) := by
    have action := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
    simpa [event, index, outputEq, decodeEventAction] using action
  have completed := grantBoundary.toSourceCheckpoint.commit name guard event atRank ready
    outputEq (fun ref => refsBefore ref index) choice decoded
  have recovered := completed.decode next (fun tail => embedding.ref tail.succ)
  dsimp only [readout]
  rw [decodeSourcePrefix?_commit]
  exact congrArg (Option.map Sum.inr) recovered

theorem ServiceBoundary.reveal_state_law [Fintype Player]
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (boundary : ServiceBoundary setup leaks rosters initial source refs offset execution)
    (network : (runtime setup).NetworkPolicy leaks)
    (opportunity : owner ∈ rosters (embedding.event ⟨0, by simp [eventCount]⟩))
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      (rosterBlock setup rosters (embedding.event ⟨0, by simp [eventCount]⟩)) execution).map
        (fun final => decodeSourcePrefix?
          (.reveal published owner name fresh binding unresolved next) refs source.registry
          source.revelations embedding.ref 1 final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion .sequential)))) =
      (ProtocolState.behavioralStateStep
        (.reveal published owner name fresh binding unresolved next)
          profile (ProtocolState.entry _ source)).map some := by
  let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
    ⟨0, by simp [eventCount]⟩
  let event : (graph setup).EventId := embedding.event index
  let players := sourceServiceLastPolicy setup leaks rosters wholeProfile
  have atRank : event.val = offset := by
    simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  obtain ⟨visited, remaining, position, absent⟩ :=
    last_owner_split owner (rosters event) opportunity
  obtain ⟨granted, grantBoundary, grant, _grantApp, _grantRecall, grantLaw⟩ :=
    boundary.grant players network event
  have ready := grantBoundary.ready event atRank
  have strategic : ((graph setup).actor? event).isSome = true := by
    simp only [owned, Option.isSome_some]
  obtain ⟨entered, activated⟩ :=
    grantBoundary.invariant.activatedAt_eq_some_of_ready_actor event ready strategic
  have due := grantBoundary.invariant.due_after_deadline (runtime setup) event entered activated
  have phase := sourceServiceLastPolicy_reveal_roster_readout setup leaks rosters fresh binding
    unresolved next wholeProfile profile refs source embedding refsBefore offset aligned granted
    grantBoundary.toSourceCheckpoint grantBoundary.binding entered (event.val + 1)
    grantBoundary.published grantBoundary.serials network visited remaining absent position grant
    ready (grantBoundary.timely event atRank strategic) activated due
    (grantBoundary.unsent owner event atRank.ge)
    (grantBoundary.response_offset event atRank owner)
  change ((runtime setup).runInteractionPlan leaks players network
    (rosterBlock setup rosters event) execution).map _ = _
  rw [rosterBlock_of_owner setup rosters event owner owned,
    (runtime setup).runInteractionPlan_append]
  simp only [runInteractionPlan, grantLaw, PMF.pure_bind]
  simp only [List.append_assoc, List.singleton_append] at phase ⊢
  exact phase.trans (effective_reveal_state_law fresh binding unresolved next profile source
    effective)

/-- Every nonterminal source instruction has its actual source transition
law after one complete native block. All dynamic prerequisites come from the
operational boundary; effectiveness is supplied by disclosure normalization. -/
theorem ServiceBoundary.step_state_law [Fintype Player]
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (positive : 0 < eventCount program)
    (wholeProfile : BehavioralProfile setup.program) (profile : BehavioralProfile program)
    (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile program profile refs
      source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (boundary : ServiceBoundary setup leaks rosters initial source refs offset execution)
    (bounds : MessageBounds (graph setup)) (network : (runtime setup).NetworkPolicy leaks)
    (opportunities : ActorOpportunities setup rosters)
    (effective : ∀ who, (profile who).EffectiveDisclosures program
      source.registry source.revelations) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      (rosterBlock setup rosters (embedding.event ⟨0, positive⟩)) execution).map
        (fun final => decodeSourcePrefix? program refs source.registry source.revelations
          embedding.ref 1 final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion .sequential)))) =
      (ProtocolState.behavioralStateStep program profile (ProtocolState.entry program source)).map
        some := by
  cases program with
  | ret result => simp only [eventCount, lt_self_iff_false] at positive
  | sample name fresh distribution next =>
      exact boundary.sample_state_law fresh distribution next wholeProfile profile source refs
        embedding refsBefore offset aligned execution network
  | commit name owner fresh guard next =>
      have owned : (graph setup).actor? (embedding.event ⟨0, positive⟩) = some owner := by
        change (toEventGraph setup.program).actor? (embedding.event ⟨0, positive⟩) = _
        simpa [eventOwner?, eventCount] using aligned.actorEq ⟨0, positive⟩
      exact boundary.commit_state_law fresh guard next wholeProfile profile source refs embedding
        refsBefore offset aligned execution bounds network (opportunities _ owner owned)
  | reveal published owner name fresh binding unresolved next =>
      have owned : (graph setup).actor? (embedding.event ⟨0, positive⟩) = some owner := by
        change (toEventGraph setup.program).actor? (embedding.event ⟨0, positive⟩) = _
        simpa [eventOwner?, eventCount] using aligned.actorEq ⟨0, positive⟩
      exact boundary.reveal_state_law fresh binding unresolved next wholeProfile profile source refs
        embedding refsBefore offset aligned execution network (opportunities _ owner owned)
        (effective owner)

end Vegas
