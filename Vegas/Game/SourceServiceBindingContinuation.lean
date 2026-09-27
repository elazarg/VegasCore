/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceActiveBindingCheckpoint
import Vegas.Game.SourceServiceTimedReachability
import Vegas.Pending.ReactiveResponseConditioning

/-! # The source continuation selected by a native binding response

A current response conditions the source value and the independent submission
time. Every subsequent source event is executed by the same timed baseline.
The resulting law retains the complete source terminal state.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The complete source law following one legal unsent binding response.
All later native execution is evaluated, and its source correspondence is
derived from the actual fully mixed prefix, not supplied as a comparison
hypothesis. Conditioning may retain the timing tag; terminal source behavior
depends only on its typed binding value. -/
theorem sourceServiceTimedPolicy_binding_response_continuation
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (full : ∀ event who owned, (timing event who owned).FullSupport)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program)
    (permitted : ∀ who, (wholeProfile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (effective : ∀ who, (wholeProfile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile who))
    (assessment : ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (strategy : assessment.strategy = fun who =>
      (sourceServiceMenu setup leaks bounds rosters).restrictPolicy (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
          (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile who))
    (mixed : assessment.IsFullyMixed)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore rank)
    (execution : (application setup leaks).Execution) (remainingFuel : Nat)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remainingFuel, some owner, execution⟩))
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (serial : Nat)
    (freshSlot : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (remaining : List Player) (before : List (ServiceInstruction (graph setup))) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    ∀ (outputEq : (graph setup).outputLayout event = .binding owner payload)
      (owned : (graph setup).actor? event = some owner)
      (granted : execution.application.serviceGrant = some event)
      (unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (counted : (execution.recall owner).length + 1 + remaining.count owner =
        rosterOffset setup rosters owner event + (rosters event).count owner)
      (ready : execution.application.config.cut.Ready event)
      (timely : execution.application.WithinDeadline (runtime setup) event)
      (vacant : execution.application.accepted (.inr event) = none)
      (unused : execution.application.HandleUnused (owner, .prepared serial))
      (serials : execution.network.SerialsBeforeNext)
      (published : execution.network.Satisfies fun message =>
        message.id ∈ execution.network.ledger.map Message.id),
    let app := application setup leaks
    let players := sourceServiceTimedPolicy setup leaks rosters timing wholeProfile
    let phase := remaining.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event])
    let later := ((List.finRange (graph setup).order.eventCount).drop (event.val + 1)).flatMap
      (rosterBlock setup rosters)
    ∀ (_split : rosterPlanPrefix setup rosters (event.val + 1) =
        before ++ .player owner :: phase)
      (_position : execution.environmentRecall.length = before.length + 1)
      (response : app.Action)
      (_allowed : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions owner
        (execution.recall owner) (execution.observe app owner)),
    let posterior := (app.policyMixture (timing event owner owned)
      (sourceServiceTimedFamily setup leaks rosters wholeProfile owner event)).posterior
        (execution.recall owner)
    let branch := fun (choice : PublicationResult (L.Val payload))
      (slot : Fin ((rosters event).count owner)) => app.scheduledPolicy
      (rosterOffset setup rosters owner event) (some slot)
        (fun _ _ => FinDist.pure
          ((runtime setup).reactiveBinding leaks owner event payload choice serial))
        app.replayPolicy
    let tags := (commitKernel profile (source.view owner)).bind fun choice =>
      posterior.bind fun slot =>
        (branch choice slot (execution.recall owner) (execution.observe app owner)).map
          (fun action => (choice, slot, action))
    ((runtime setup).runInteractionPlan leaks players network (HAppend.hAppend phase later)
      (execution.respond app owner response)).map
        (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
      (tags.condOnFibre (fun tag => some tag.2.2) (some response)).bind
        fun (tag : PublicationResult (L.Val payload) ×
          Fin ((rosters event).count owner) × app.Action) =>
        (setup.continuationLaw wholeProfile
          (sourceServicePrefix? setup (HAdd.hAdd event.val 1)
            (execution.application.config.complete event ready
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) tag.1)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm) tag.1)))).map some := by
  intro index event outputEq owned granted unsent counted ready timely vacant unused serials
    published
    app players phase later split position response allowed posterior branch tags
  let menu := sourceServiceMenu setup leaks bounds rosters
  let scheduled := fun choice slot => Function.update (fun _ => app.replayPolicy) owner
    (branch choice slot)
  let kernel := fun tag : PublicationResult (L.Val payload) ×
      Fin ((rosters event).count owner) × app.Action =>
    (runtime setup).runInteractionPlan leaks (scheduled tag.1 tag.2.1) network phase
      (execution.respond app owner tag.2.2)
  let responses := players owner (execution.recall owner) (execution.observe app owner)
  let continued := fun action => (runtime setup).runInteractionPlan leaks players network phase
    (execution.respond app owner action)
  let observed := fun final : app.Execution =>
    ((final.recall owner)[(execution.recall owner).length]?).map
      ReactiveApplication.PlayerEntry.action
  have recorded (other : Player → app.Policy) (action : app.Action) (final : app.Execution)
      (reached : final ∈ ((runtime setup).runInteractionPlan leaks other network phase
        (execution.respond app owner action)).support) : observed final = some action := by
    obtain ⟨entry, recalled, _, chosen⟩ := (runtime setup).response_recall_entry leaks execution
      owner action
    obtain ⟨tail, same⟩ := (runtime setup).runInteractionPlan_recall_prefix leaks other network
      phase (execution.respond app owner action) final reached owner
    dsimp only [observed]
    rw [← same, recalled]
    simp only [List.append_assoc, List.singleton_append, List.getElem?_append_right
      (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.map_some, chosen]
  have factor : responses.bind continued = tags.bind kernel := by
    have law := sourceServiceTimedPolicy_active_binding_law setup leaks bounds values initialValues
      capacity rosters opportunities timing full network fresh guard next wholeProfile permitted
      profile refs source embedding refsBefore rank aligned execution remainingFuel trace agree
      history serial freshSlot candidate remaining (event.val + 1) owned granted unsent counted
    simpa only [ReactiveApplication.invoke, FinDist.bind_map, FinDist.bind_bind,
      Function.update_self, tags, kernel, scheduled, branch, responses, continued, posterior,
      phase, players] using law
  have chosen := roster_fullyMixed_response_support setup leaks rosters network menu players
    covered assessment strategy mixed owner remainingFuel execution trace response allowed
  have tagPresent : some response ∈ (tags.map (fun tag => some tag.2.2)).support := by
    obtain ⟨final, reached⟩ := (continued response).support_nonempty
    have possible : final ∈ (responses.bind continued).support :=
      FinDist.support_bind .. ▸ Set.mem_iUnion₂.mpr ⟨response, chosen, reached⟩
    rw [factor, FinDist.support_bind] at possible
    obtain ⟨tag, member, realized⟩ := Set.mem_iUnion₂.mp possible
    rw [FinDist.support_map]
    exact ⟨tag, member, (recorded _ _ _ realized).symm.trans (recorded _ _ _ reached)⟩
  have conditioned : continued response =
      (tags.condOnFibre (fun tag => some tag.2.2) (some response)).bind kernel := by
    have physical := (runtime setup).runInteractionPlan_response_conditioning leaks players
      network phase execution owner responses response chosen
    change (responses.bind continued).condOnFibre observed (some response) = continued response
      at physical
    rw [factor, FinDist.conditional_bind_of_observation tags kernel
      (fun tag => some tag.2.2) observed (fun tag _ final member => recorded _ _ _ member)
      (some response) tagPresent] at physical
    exact physical.symm
  have tagsSupport (tag) (member : tag ∈ tags.support) :
      tag.1 ∈ (commitKernel profile (source.view owner)).support ∧
      tag.2.1 ∈ posterior.support ∧
      tag.2.2 ∈ (branch tag.1 tag.2.1 (execution.recall owner)
        (execution.observe app owner)).support := by
    obtain ⟨choice, choiceSupport, member⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ member)
    obtain ⟨slot, slotSupport, member⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ member)
    obtain ⟨action, actionSupport, rfl⟩ := FinDist.support_map .. ▸ member
    exact ⟨choiceSupport, slotSupport, actionSupport⟩
  have future : ∀ slot ∈ posterior.support,
      (execution.recall owner).length ≤ rosterOffset setup rosters owner event + slot.val := by
    have positive : 0 < (rosters event).count owner :=
      List.count_pos_iff.mpr (opportunities event owner payload outputEq)
    let last : Fin ((rosters event).count owner) := ⟨(rosters event).count owner - 1, by omega⟩
    exact sourceServiceTimedMixture_binding_future setup leaks bounds values initialValues capacity
      rosters opportunities network wholeProfile permitted owner
      ⟨remainingFuel, some owner, execution⟩
      trace rfl event granted owned payload outputEq unsent (timing event owner owned) last
      (full event owner owned last) (by dsimp only [last]; omega)
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    exact aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq := by
    cases viewed : nodeView (graph setup) event with
    | sample other law kind code => cases kind.symm.trans outputEq
    | resolve other otherPayload binding checks kind code => cases kind.symm.trans outputEq
    | bind other otherPayload kind code =>
        obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj (kind.symm.trans outputEq)
        rfl
  rw [runInteractionPlan_append, FinDist.map_bind]
  change (continued response).bind _ = _
  rw [conditioned, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro tag conditionalMember
  have tagMember : tag ∈ tags.support := by
    unfold FinDist.condOnFibre at conditionalMember
    split at conditionalMember
    · exact (FinDist.support_condOn _ _ _ conditionalMember).2
    · exact conditionalMember
  obtain ⟨choiceSupport, slotSupport, responseSupport⟩ := tagsSupport tag tagMember
  calc
    _ = (kernel tag).bind (fun _ =>
        (setup.continuationLaw wholeProfile (sourceServicePrefix? setup (event.val + 1)
          (execution.application.config.complete event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) tag.1)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) tag.1)))).map some) := by
      apply FinDist.bind_congr
      intro final reached
      have actual : final ∈ (continued response).support := by
        rw [conditioned, FinDist.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨tag, conditionalMember, reached⟩
      have baseline := roster_fullyMixed_response_prefix_support setup leaks rosters network menu
        players covered assessment strategy mixed owner remainingFuel execution trace
        (event.val + 1) before phase split position response allowed final actual
      have suffix := sourceServiceTimedPolicy_continuation_law setup leaks bounds values capacity
        rosters opportunities timing network wholeProfile covered effective owner (event.val + 1)
        (by exact Nat.succ_le_of_lt event.isLt) final baseline
      have supported : final ∈ ((app.invoke (scheduled tag.1 tag.2.1) owner execution).bind
          ((runtime setup).runInteractionPlan leaks (scheduled tag.1 tag.2.1) network
            ((remaining.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
              List.replicate (event.val + 1) .tick ++ [.expire event]))).support := by
        simp only [ReactiveApplication.invoke, FinDist.bind_map, FinDist.support_bind]
        refine Set.mem_iUnion₂.mpr ⟨tag.2.2, by
          simpa only [scheduled, Function.update_self] using responseSupport, ?_⟩
        simpa only [kernel, phase, List.append_assoc, List.cons_append, List.nil_append]
          using reached
      have completed := scheduledBindingActive_config setup leaks bounds network owner event payload
        outputEq codeEq node owned execution granted ready timely serial candidate vacant unused
        serials published remaining tag.2.1 (rosterOffset setup rosters owner event)
        (future _ slotSupport) (by rw [counted]; exact Nat.add_lt_add_left tag.2.1.isLt _)
        tag.1 (event.val + 1) final supported
      rw [completed] at suffix
      exact suffix
    _ = _ := FinDist.bind_const _ _

end Vegas.SourceProgram.RevealService
