/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSource
import Vegas.Game.SourceServiceRecordedContinuation
import Vegas.Game.SourceServiceTimedBindingCheckpoint
import Vegas.Pending.ReactiveRevealBlock

/-! # Foreign visits during a binding phase

A foreign player's legal responses at a binding phase are transport-only. They
leave the application and the owner's recall unchanged, but they can change the
owner's later network observations and therefore its later recall. The owner's
timed policy nevertheless determines the configuration at the next event
boundary from application data alone: its slot posterior depends only on its
recall, which the foreign response does not touch, and each fixed slot either
completes the binding with the source value or leaves only replays. So every
legal foreign response has the same next-boundary configuration law, and the
generic local comparison gives zero gain for every belief.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- With all traffic published, a roster window whose players respond only by
transport while the application is unchanged, followed by protected inclusion,
leaves the application unchanged, so a phase has the application law of its
passive suffix. -/
theorem transport_phase_application_law (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player) (visits : List Player)
    (rest : List (ServiceInstruction (graph setup)))
    (passive : ∀ instruction ∈ rest, instruction ≠ .wire ∧
      (∀ who, instruction ≠ .player who) ∧ ∀ event who, instruction ≠ .includeLatest event who)
    (execution : (application setup leaks).Execution)
    (responses : ∀ (current : (application setup leaks).Execution) who response,
      current.application = execution.application →
      execution.recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (application setup leaks) who)).support →
      response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id) :
    ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ .includeLatest event owner :: rest)
        execution).map ReactiveApplication.Execution.application =
      ((runtime setup).runInteractionPlan leaks players network rest execution).map
        ReactiveApplication.Execution.application := by
  rw [runInteractionPlan_append, FinDist.map_bind]
  calc
    _ = ((runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) execution).bind (fun _ =>
          ((runtime setup).runInteractionPlan leaks players network rest
            execution).map ReactiveApplication.Execution.application) := by
      apply FinDist.bind_congr
      intro current reached
      obtain ⟨sameApp, ledger, _, _, valid, _⟩ := (runtime setup).replay_window_preserves leaks
        players network owner execution responses _ published visits current reached
      have waiting : (runtime setup).reactiveLatest leaks event owner
          (current.observeEnvironment ((runtime setup).reactiveApplication leaks)) = .wait := by
        apply (runtime setup).reactiveLatest_wait_of_pending_published leaks event owner
        intro message member
        have spent := valid.1 message member
        rw [← ledger] at spent
        exact spent
      simp only [runInteractionPlan, interactionStep, interactionInstruction, waiting,
        FinDist.pure_bind, ReactiveApplication.dispatch,
        ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume]
      exact (runtime setup).application_service_law leaks _ network rest passive _ execution
        sameApp
    _ = _ := FinDist.bind_const _ _

/-- With all traffic published, a replay-only roster window and protected
inclusion leave the application unchanged, so a phase has the application law
of its passive suffix. -/
theorem replay_phase_application_law (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player) (visits : List Player)
    (rest : List (ServiceInstruction (graph setup)))
    (passive : ∀ instruction ∈ rest, instruction ≠ .wire ∧
      (∀ who, instruction ≠ .player who) ∧ ∀ event who, instruction ≠ .includeLatest event who)
    (execution : (application setup leaks).Execution)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id) :
    ((runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).replayPolicy)
      network (visits.map ServiceInstruction.player ++ .includeLatest event owner :: rest)
        execution).map ReactiveApplication.Execution.application =
      ((runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).replayPolicy)
        network rest execution).map ReactiveApplication.Execution.application :=
  transport_phase_application_law setup leaks _ network event owner visits rest passive execution
    (fun _ _ response _ _ supported =>
      (application setup leaks).replayPolicy_cases _ _ response supported) published

section

variable [Finite Player]

/-- From any execution of a binding phase with the owner's binding resources,
a fixed timing slot the owner still reaches in the remaining visits completes
the event with the source binding value: the configuration at the next event
boundary is the source commitment lottery, whatever the network traffic. -/
theorem binding_slot_config_law (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program) {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution) {config : (graph setup).Config}
    (site : BindingSource setup wholeProfile event config)
    (sameConfig : execution.application.config = config)
    (granted : execution.application.serviceGrant = some event)
    (unsent : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (ready : config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (serial : Nat)
    (freshSlot : reactiveFreshSlot (execution.observe
      (application setup leaks) site.owner).application = some serial)
    (candidate : execution.application.candidates.lookup (site.owner, .prepared serial) = .fresh)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused (site.owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (visits : List Player) (slot : Fin ((rosters event).count site.owner))
    (notPassed : (execution.recall site.owner).length ≤
      rosterOffset setup rosters site.owner event + slot.val)
    (within : rosterOffset setup rosters site.owner event + slot.val <
      (execution.recall site.owner).length + visits.count site.owner)
    (ticks : Nat) :
    ((runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => (application setup leaks).replayPolicy) site.owner
        (sourceServiceTimedFamily setup leaks rosters wholeProfile site.owner event slot))
      network (visits.map ServiceInstruction.player ++
        (.includeLatest event site.owner :: List.replicate ticks .tick ++ [.expire event]))
      execution).map (fun final => final.application.config) =
      (commitKernel site.residual (site.source.view site.owner)).bind fun choice =>
        FinDist.pure (config.complete event ready
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) choice)
          (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) choice)) := by
  subst sameConfig
  obtain ⟨codeEq, node⟩ := binding_nodeView setup event site.owner site.payload site.outputEq
  have owned := site.owned
  have outputEq := site.outputEq
  obtain ⟨Γ, names, name, owner, payload, fresh, guard, next, residual, refs, source, embedding,
    refsBefore, aligned, agree, history, head⟩ := site
  dsimp only at *
  subst head
  obtain ⟨visited, remaining, position, counted⟩ := split_owner_visit owner visits
    (rosterOffset setup rosters owner (embedding.event ⟨0, by simp [eventCount]⟩) + slot.val -
      (execution.recall owner).length) (by omega)
  have selected : rosterOffset setup rosters owner (embedding.event ⟨0, by simp [eventCount]⟩) +
      slot.val = (execution.recall owner).length + visited.count owner := by omega
  have law := sourceServiceTimedFamily_binding_law setup leaks rosters fresh guard next
    wholeProfile residual refs source embedding refsBefore _ aligned execution agree history
    serial freshSlot candidate network visits visited remaining slot position selected granted
    unsent
  have splitPlan : (visits.map ServiceInstruction.player ++
      (.includeLatest (embedding.event ⟨0, by simp [eventCount]⟩) owner ::
        List.replicate ticks .tick ++ [.expire (embedding.event ⟨0, by simp [eventCount]⟩)]) :
          List (ServiceInstruction (graph setup))) =
      (visits.map ServiceInstruction.player ++
        [.includeLatest (embedding.event ⟨0, by simp [eventCount]⟩) owner]) ++
        (List.replicate ticks .tick ++ [.expire (embedding.event ⟨0, by simp [eventCount]⟩)]) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [splitPlan, runInteractionPlan_append, law, FinDist.bind_bind, FinDist.map_bind]
  apply FinDist.bind_congr
  intro choice _
  let raw := Function.update (fun _ => (application setup leaks).replayPolicy) owner
    ((application setup leaks).scheduledPolicy
      (rosterOffset setup rosters owner (embedding.event ⟨0, by simp [eventCount]⟩))
      (some slot) (fun _ _ => FinDist.pure ((runtime setup).reactiveBinding leaks owner
        (embedding.event ⟨0, by simp [eventCount]⟩) payload choice serial))
      (application setup leaks).replayPolicy)
  refine (FinDist.map_congr_of_eq_on_support (g := fun _ => _) ?_).trans (FinDist.map_const _ _)
  intro final reached
  obtain ⟨current, prior, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  rw [servicePlan_players_eq setup leaks _ raw network _ (by simp) (by intro who; simp) current]
    at rest
  apply scheduledBindingPhase_config setup leaks bounds network owner _ payload outputEq codeEq
    node owned execution granted ready timely serial candidate vacant unused serials published
    visits slot _ (by omega) (by omega) choice ticks final
  rw [List.append_assoc (visits.map ServiceInstruction.player ++ [_]),
    runInteractionPlan_append, FinDist.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨current, prior, rest⟩

end

variable [Fintype Player]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

include approx in
/-- A player who is not the event's actor has only transport responses. -/
theorem foreign_response_transport {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    {event : (graph service.setup).EventId} {owner : Player}
    (owned : (graph service.setup).actor? event = some owner) (foreign : who ≠ owner)
    (granted : execution.application.serviceGrant = some event)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ := by
  have present := roster_fullyMixed_response_support service.setup service.leaks
    service.rosters service.network service.menu approx.players approx.covered approx.assessment
    approx.strategy approx.mixed who remaining execution trace response allowed
  have grant : PublicView.serviceGrant
      (execution.observe (application service.setup service.leaks) who).application.publicView =
        some event := granted
  have notActor : (graph service.setup).actor? event ≠ some who :=
    fun acts => foreign (Option.some.inj (acts.symm.trans owned))
  simp only [players, sourceServiceTimedPolicy, grant, dite_eq_right notActor] at present
  exact (application service.setup service.leaks).replayPolicy_cases _ _ response present

/-- At a binding phase, every legal response of a player other than the owner
leaves the same configuration law at the next event boundary, whether or not the
owner has already submitted its binding. -/
theorem foreign_binding_phase_invariant {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (owner : Player) (payload : L.Ty) (foreign : who ≠ owner)
    (outputEq : (graph service.setup).outputLayout phase.event = .binding owner payload)
    (first second : (application service.setup service.leaks).Action)
    (firstAllowed : first ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (secondAllowed : second ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second := by
  by_cases recorded : (runtime service.setup).eventRecorded service.leaks
      (execution.recall owner) phase.event = true
  · exact approx.recorded_phase_invariant trace phase owner payload outputEq recorded first
      second firstAllowed secondAllowed
  have unsent : (runtime service.setup).eventRecorded service.leaks
      (execution.recall owner) phase.event = false := Bool.eq_false_of_ne_true recorded
  have owned := binding_actor service.setup phase.event owner payload outputEq
  obtain ⟨codeEq, node⟩ := binding_nodeView service.setup phase.event owner payload outputEq
  obtain ⟨ready, timely, _, _, _, serials, resources⟩ := sourceService_binding_decision_resources
    service.setup service.leaks service.bounds service.values service.capacity service.rosters
    service.opportunities.binding service.network who ⟨remaining, some who, execution⟩ trace rfl
    phase.event phase.granted owner payload outputEq codeEq node owned
  obtain ⟨_, freshSlot, fresh, unused, vacant, _, published⟩ := resources unsent
  obtain ⟨site⟩ := service.exists_bindingSource approx.profile trace phase outputEq
  have ownerEq : site.owner = owner := Option.some.inj (site.owned.symm.trans owned)
  subst ownerEq
  let offset := rosterOffset service.setup service.rosters site.owner phase.event
  let rest : List (ServiceInstruction (graph service.setup)) :=
    List.replicate (phase.event.val + 1) .tick ++ [.expire phase.event]
  have passive : ∀ instruction ∈ rest, instruction ≠ .wire ∧
      (∀ actor, instruction ≠ .player actor) ∧
      ∀ selected actor, instruction ≠ .includeLatest selected actor := by
    intro instruction member
    simp only [rest, List.mem_append, List.mem_replicate, List.mem_singleton] at member
    rcases member with ⟨_, rfl⟩ | rfl <;> simp
  have ending : rosterPhaseEnding service.setup phase.event =
      .includeLatest phase.event site.owner :: rest := by
    simp only [rosterPhaseEnding, owned, rest, List.cons_append, List.nil_append]
  let target := fun slot : Fin ((service.rosters phase.event).count site.owner) =>
    if (execution.recall site.owner).length ≤ offset + slot.val ∧
        offset + slot.val < (execution.recall site.owner).length + phase.visits.count site.owner
    then (commitKernel site.residual (site.source.view site.owner)).bind fun choice =>
      FinDist.pure (execution.application.config.complete phase.event ready
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) choice)
        (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) choice))
    else ((runtime service.setup).runInteractionPlan service.leaks
      (fun _ => (application service.setup service.leaks).replayPolicy) service.network rest
        execution).map (fun final => final.application.config)
  let posterior := ((application service.setup service.leaks).policyMixture
    (approx.timing phase.event site.owner owned)
    (sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
      site.owner phase.event)).posterior (execution.recall site.owner)
  have law (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)) :
      approx.phaseConfigLaw phase response = posterior.bind target := by
    have transport := approx.foreign_response_transport trace owned foreign phase.granted
      response allowed
    have preserved := (runtime service.setup).replay_response_preserves service.leaks _
      execution published who response transport
    have counters := (runtime service.setup).replay_response_preserves service.leaks _
      execution serials who response transport
    have sameRecall := (application service.setup service.leaks).respond_recall_other execution
      who site.owner (Ne.symm foreign) response
    set after := execution.respond (application service.setup service.leaks) who response
      with afterDef
    have sameApp : after.application = execution.application := preserved.1
    have afterGrant : after.application.serviceGrant = some phase.event := by
      rw [sameApp]
      exact phase.granted
    have afterPublished : after.network.Satisfies fun message =>
        message.id ∈ after.network.ledger.map Message.id := by
      rw [preserved.2.1]
      exact preserved.2.2.2.2.1
    have afterSerials : after.network.SerialsBeforeNext := by
      unfold MessageNetwork.SerialsBeforeNext
      rw [counters.2.2.2.1]
      exact counters.2.2.2.2.1
    have mixed : (runtime service.setup).runInteractionPlan service.leaks approx.players
        service.network (phase.visits.map ServiceInstruction.player ++
          .includeLatest phase.event site.owner :: rest) after =
        (runtime service.setup).runInteractionPlan service.leaks
          (Function.update (fun _ => (application service.setup service.leaks).replayPolicy)
            site.owner ((application service.setup service.leaks).policyMixture
              (approx.timing phase.event site.owner owned)
              (sourceServiceTimedFamily service.setup service.leaks service.rosters
                approx.profile site.owner phase.event)).policy)
          service.network (phase.visits.map ServiceInstruction.player ++
            .includeLatest phase.event site.owner :: rest) after := by
      rw [runInteractionPlan_append, runInteractionPlan_append,
        sourceServiceTimedPolicy_window_eq service.setup service.leaks service.rosters
          approx.timing approx.profile phase.event site.owner owned service.network phase.visits
          after afterGrant]
      apply FinDist.bind_congr
      intro current _
      exact servicePlan_players_eq service.setup service.leaks _ _ service.network _
        (by simp [rest]) (by intro actor; simp [rest]) current
    have mixture := (runtime service.setup).runInteractionPlan_policyMixture service.leaks
      (approx.timing phase.event site.owner owned)
      (sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
        site.owner phase.event) site.owner
      (fun _ => (application service.setup service.leaks).replayPolicy) service.network
      (phase.visits.map ServiceInstruction.player ++
        .includeLatest phase.event site.owner :: rest) after
    dsimp only at mixture
    rw [sameRecall] at mixture
    unfold phaseConfigLaw phaseLaw DecisionPhase.tail
    rw [ending, mixed, ← mixture, FinDist.map_bind]
    apply FinDist.bind_congr
    intro slot _
    by_cases inside : (execution.recall site.owner).length ≤ offset + slot.val ∧
        offset + slot.val < (execution.recall site.owner).length + phase.visits.count site.owner
    · dsimp only [target]
      simp only [inside.1, inside.2, and_self, ↓reduceIte]
      exact binding_slot_config_law service.setup service.leaks service.bounds service.rosters
        service.network approx.profile after site (by rw [sameApp]) afterGrant
        (by rw [sameRecall]; exact unsent) ready (by rw [sameApp]; exact timely) _
        (by change reactiveFreshSlot ((application service.setup service.leaks).observePlayer
              after.application site.owner) = _
            rw [sameApp]
            exact freshSlot)
        (by rw [sameApp]; exact fresh) (by rw [sameApp]; exact vacant)
        (by rw [sameApp]; exact unused) afterSerials afterPublished phase.visits slot
        (by rw [sameRecall]; exact inside.1) (by rw [sameRecall]; exact inside.2)
        (phase.event.val + 1)
    · dsimp only [target]
      simp only [inside, ↓reduceIte]
      have separated : (after.recall site.owner).length + phase.visits.count site.owner ≤
          offset + slot.val ∨ offset + slot.val < (after.recall site.owner).length := by
        rw [sameRecall]
        omega
      have replayed : (runtime service.setup).runInteractionPlan service.leaks
          (Function.update (fun _ => (application service.setup service.leaks).replayPolicy)
            site.owner (sourceServiceTimedFamily service.setup service.leaks service.rosters
              approx.profile site.owner phase.event slot)) service.network
          (phase.visits.map ServiceInstruction.player ++
            .includeLatest phase.event site.owner :: rest) after =
          (runtime service.setup).runInteractionPlan service.leaks
            (fun _ => (application service.setup service.leaks).replayPolicy) service.network
            (phase.visits.map ServiceInstruction.player ++
              .includeLatest phase.event site.owner :: rest) after := by
        rw [runInteractionPlan_append, runInteractionPlan_append]
        unfold sourceServiceTimedFamily
        rw [scheduled_window_waiting service.setup service.leaks service.network site.owner offset
          slot _ phase.visits after separated]
        apply FinDist.bind_congr
        intro current _
        exact servicePlan_players_eq service.setup service.leaks _ _ service.network _
          (by simp [rest]) (by intro actor; simp [rest]) current
      have applications := (replay_phase_application_law service.setup service.leaks
        service.network phase.event site.owner phase.visits rest passive after
          afterPublished).trans ((runtime service.setup).application_service_law service.leaks _
            service.network rest passive after execution sameApp)
      rw [replayed]
      simpa only [FinDist.map_comp, Function.comp_def] using
        congrArg (FinDist.map EventGraphRuntime.State.config) applications
  rw [law first firstAllowed, law second secondAllowed]

open Classical in
/-- At a foreign player's information site during a binding phase, every local
lottery has the prescribed continuation law, for every belief over the site. -/
theorem foreign_binding_comparison_eq (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId} {owner : Player} {payload : L.Ty}
    (foreign : who ≠ owner)
    (outputEq : (graph service.setup).outputLayout event = .binding owner payload)
    (granted : view.application.publicView.serviceGrant = some event)
    (law : FinDist (service.model.Choice who site.1)) :
    let comparison := service.model.assessmentComparison service.readout service.fuel
      approx.assessment who (site, (approx.assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  apply approx.comparison_eq_of_phase_invariant who site
  intro history remaining execution current info phase first second firstAllowed secondAllowed
  have input := Option.some.inj
    ((service.infoOf_decision history current).symm.trans (info.trans observed))
  have grant : execution.application.serviceGrant = some event :=
    (congrArg (fun pair : List (application service.setup service.leaks).PlayerEntry ×
      (application service.setup service.leaks).PlayerView =>
        pair.2.application.publicView.serviceGrant) input).trans granted
  have same : phase.event = event := Option.some.inj (phase.granted.symm.trans grant)
  subst same
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  exact approx.foreign_binding_phase_invariant trace phase owner payload foreign outputEq first
    second firstAllowed secondAllowed

end TimedApproximant

end Vegas
