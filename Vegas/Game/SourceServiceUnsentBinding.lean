/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOwnerComparison
import Vegas.Game.SourceServiceBindingContinuation
import Vegas.Game.SourceServiceBindingSource
import Vegas.Game.SourceServiceForeignComparison
import Vegas.Pending.ReactiveResolutionWindowState
import Vegas.Game.SourceLocalPolicy
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Support

/-! # The owner's unsent binding

At an owner's visit to its own unsent binding, the timed compiler draws the
source value, then the timing slot, then the current response: a submission of
that value at the chosen slot, and a replay otherwise. A current submission
fixes the source value. A current transport response leaves the source value
law unchanged, because value and timing are independent and a transport
response reveals only that the current slot was not chosen.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- At every retained decision, the acting player has recalled exactly its
activations before the event and its earlier visits in the event's roster. -/
theorem recall_count {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution) :
    (execution.recall who).length =
      rosterOffset service.setup service.rosters who phase.event +
        ((service.rosters phase.event).take phase.slot).count who := by
  obtain ⟨event, slot, _, selected, _, _, _, _, _, _, _, _, _, _, _, _, granted, prior, sample,
      boundary, grant, reached, _, sampled, _, publicEq, _, position, _⟩ :=
    sourceService_decision_boundary service.setup service.leaks service.bounds service.values
      service.capacity service.rosters service.opportunities.binding service.network
      (failureProfile service.setup.program) who ⟨remaining, some who, execution⟩ trace rfl
  have same : event = phase.event := Option.some.inj
    (((congrArg PublicView.serviceGrant publicEq).trans grant).symm.trans phase.granted)
  subst same
  have sameSlot : slot = phase.slot := by
    have lengths := position.symm.trans phase.position
    change (rosterPlanPrefix service.setup service.rosters phase.event.val).length + 1 + slot + 1 =
      (rosterPlanPrefix service.setup service.rosters phase.event.val).length + 1 + phase.slot + 1
      at lengths
    omega
  subst sameSlot
  have counted := fixed_plan_response_counts service.setup service.leaks service.network
    service.menu.uniformResponses
    (((service.rosters phase.event).take phase.slot).map ServiceInstruction.player)
    (by simp only [List.mem_map]; rintro ⟨_, _, impossible⟩; cases impossible)
    granted prior reached who
  simp only [List.filterMap_map, instructionActor, Function.comp_def, List.filterMap_some]
    at counted
  have recalled : execution.recall who = prior.recall who := by
    change execution = _ at sampled
    rw [sampled]
    rfl
  rw [recalled, counted, boundary.counts who]
  rfl

end SourceServiceSpec

omit [Fintype Player] in
/-- Before its binding is recorded, the owner's source opportunity at any
execution of the binding phase submits the source value with the fresh serial. -/
theorem BindingSource.opportunity_law {setup : Setup (Player := Player) (L := L)}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {wholeProfile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution)
    (site : BindingSource setup wholeProfile event execution.application.config)
    (granted : execution.application.serviceGrant = some event)
    (unsent : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (serial : Nat)
    (freshSlot : reactiveFreshSlot (execution.observe
      (application setup leaks) site.owner).application = some serial)
    (candidate : execution.application.candidates.lookup (site.owner, .prepared serial) = .fresh) :
    sourceServiceOpportunity setup leaks wholeProfile site.owner event
      (execution.recall site.owner) (execution.observe (application setup leaks) site.owner) =
      (commitKernel site.residual (site.source.view site.owner)).map fun choice =>
        (runtime setup).reactiveBinding leaks site.owner event site.payload choice serial := by
  obtain ⟨codeEq, node⟩ := binding_nodeView setup event site.owner site.payload site.outputEq
  have outputEq := site.outputEq
  obtain ⟨Γ, names, name, owner, payload, fresh, guard, next, residual, refs, source, embedding,
    refsBefore, aligned, agree, history, head⟩ := site
  dsimp only at *
  subst head
  have policyLaw := sourceServicePolicy_commit setup leaks fresh guard next wholeProfile residual
    refs source embedding refsBefore _ aligned execution agree history granted
  have responses : sourceServicePolicy setup leaks wholeProfile owner
      (execution.recall owner) (execution.observe (application setup leaks) owner) =
        (commitKernel residual (source.view owner)).map fun choice =>
          (runtime setup).reactiveBinding leaks owner (embedding.event ⟨0, by simp [eventCount]⟩)
            payload choice serial := by
    apply policyLaw.trans
    apply map_congr_on_support _
    intro choice _
    exact serviceDecision_binding_fresh (runtime setup) leaks execution owner _ payload
      outputEq codeEq node serial freshSlot candidate choice
  simp only [sourceServiceOpportunity, unsent, Bool.false_eq_true, ↓reduceIte]
  rw [responses, PMF.bind_map, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro choice _
  cases choice <;> rfl

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

/-- At the owner's unsent binding, a current transport response leaves the
source value law of the binding: the next-boundary configuration completes the
binding with the source commitment lottery. The response only rules out the
current timing slot, and every later slot is still reached. -/
theorem unsent_binding_transport_config_law {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (site : BindingSource service.setup approx.profile phase.event execution.application.config)
    (ownerEq : site.owner = who)
    (unsent : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
      phase.event = false)
    (ready : execution.application.config.cut.Ready phase.event)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) :
    approx.phaseConfigLaw phase response =
      (commitKernel site.residual (site.source.view site.owner)).bind fun choice =>
        PMF.pure (execution.application.config.complete phase.event ready
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) choice)
          (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) choice)) := by
  obtain ⟨Γ, names, name, owner, payload, fresh, guard, next, residual, refs, source, embedding,
    refsBefore, aligned, agree, history, head⟩ := site
  dsimp only at ownerEq
  subst ownerEq
  let site : BindingSource service.setup approx.profile phase.event
      execution.application.config :=
    ⟨Γ, names, name, owner, payload, fresh, guard, next, residual, refs, source, embedding,
      refsBefore, aligned, agree, history, head⟩
  change approx.phaseConfigLaw phase response =
    (commitKernel site.residual (site.source.view site.owner)).bind fun choice =>
      PMF.pure (execution.application.config.complete phase.event ready
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) choice)
        (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) choice))
  let app := application service.setup service.leaks
  have owned : (graph service.setup).actor? phase.event = some owner := site.owned
  obtain ⟨codeEq, node⟩ := binding_nodeView service.setup phase.event owner site.payload
    site.outputEq
  obtain ⟨_, timely, _, _, _, serials, resources⟩ := sourceService_binding_decision_resources
    service.setup service.leaks service.bounds service.values service.capacity service.rosters
    service.opportunities.binding service.network owner ⟨remaining, some owner,
      execution⟩ trace rfl phase.event phase.granted owner site.payload site.outputEq codeEq
    node owned
  obtain ⟨_, freshSlot, fresh, unused, vacant, _, published⟩ := resources unsent
  let offset := rosterOffset service.setup service.rosters owner phase.event
  let family := sourceServiceTimedFamily service.setup service.leaks service.rosters
    approx.profile owner phase.event
  let mixtureImpl := app.policyMixture (approx.timing phase.event owner owned) family
  let rest : List (ServiceInstruction (graph service.setup)) :=
    List.replicate (phase.event.val + 1) .tick ++ [.expire phase.event]
  have passive : ∀ instruction ∈ rest, instruction ≠ .wire ∧
      (∀ actor, instruction ≠ .player actor) ∧
      ∀ selected actor, instruction ≠ .includeLatest selected actor := by
    intro instruction member
    simp only [rest, List.mem_append, List.mem_replicate, List.mem_singleton] at member
    rcases member with ⟨_, rfl⟩ | rfl <;> simp
  have ending : rosterPhaseEnding service.setup phase.event =
      .includeLatest phase.event owner :: rest := by
    simp only [rosterPhaseEnding, owned, rest, List.cons_append, List.nil_append]
  have counted := service.recall_count trace phase
  have visitsCount : ((service.rosters phase.event).take phase.slot).count owner + 1 +
      phase.visits.count owner = (service.rosters phase.event).count owner := by
    conv_rhs => rw [phase.roster_split]
    simp only [List.count_append, List.count_cons_self]
    omega
  have positive : 0 < (service.rosters phase.event).count owner := by omega
  let last : Fin ((service.rosters phase.event).count owner) :=
    ⟨(service.rosters phase.event).count owner - 1, by omega⟩
  have posteriorFuture := sourceServiceTimedMixture_binding_future service.setup service.leaks
    service.bounds service.values service.initialValues service.capacity service.rosters
    service.opportunities.binding service.network approx.profile approx.admitted
    owner ⟨remaining, some owner, execution⟩ trace rfl phase.event phase.granted owned
    site.payload site.outputEq unsent (approx.timing phase.event owner owned) last
    (approx.timingFull phase.event owner owned last) (by dsimp only [last]; omega)
  have opening := BindingSource.opportunity_law service.leaks execution site phase.granted unsent
    _ freshSlot fresh
  have preserved := (runtime service.setup).replay_response_preserves service.leaks _
    execution published owner response transport
  have counters := (runtime service.setup).replay_response_preserves service.leaks _
    execution serials owner response transport
  have afterUnsent := (runtime service.setup).eventRecorded_respond_transport service.leaks
    execution owner owner response transport phase.event
  have afterLength := app.respond_recall_length execution owner owner response
  simp only [↓reduceIte] at afterLength
  have grant : PublicView.serviceGrant
      (execution.observe app owner).application.publicView = some phase.event :=
    phase.granted
  have policyEq : approx.players owner (execution.recall owner)
      (execution.observe app owner) =
      mixtureImpl.policy (execution.recall owner) (execution.observe app owner) := by
    simp only [players, sourceServiceTimedPolicy, grant, owned, ↓reduceDIte]
    rfl
  have present := roster_fullyMixed_response_support service.setup service.leaks
    service.rosters service.network service.menu approx.players approx.covered approx.assessment
    approx.strategy approx.mixed owner remaining execution trace response allowed
  rw [policyEq, ReactiveApplication.Implementation.policy_eq, PMF.support_map] at present
  obtain ⟨witness, witnessSupport, witnessAction⟩ := present
  have meets : ∃ pair ∈ Prod.fst ⁻¹' {response}, pair ∈ ((mixtureImpl.posterior
      (execution.recall owner)).bind fun memory => mixtureImpl.respond memory
        (execution.recall owner, execution.observe app owner)).support :=
    ⟨witness, witnessAction, witnessSupport⟩
  set after := execution.respond app owner response with afterDef
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
        .includeLatest phase.event owner :: rest) after =
      (runtime service.setup).runInteractionPlan service.leaks
        (Function.update (fun _ => app.replayPolicy) owner mixtureImpl.policy)
        service.network (phase.visits.map ServiceInstruction.player ++
          .includeLatest phase.event owner :: rest) after := by
    rw [runInteractionPlan_append, runInteractionPlan_append,
      sourceServiceTimedPolicy_window_eq service.setup service.leaks service.rosters
        approx.timing approx.profile phase.event owner owned service.network phase.visits
        after afterGrant]
    apply bind_congr_on_support _
    intro current _
    exact servicePlan_players_eq service.setup service.leaks _ _ service.network _
      (by simp [rest]) (by intro actor; simp [rest]) current
  have mixture := (runtime service.setup).runInteractionPlan_policyMixture service.leaks
    (approx.timing phase.event owner owned) family owner (fun _ => app.replayPolicy)
    service.network (phase.visits.map ServiceInstruction.player ++
      .includeLatest phase.event owner :: rest) after
  dsimp only at mixture
  have later (slot : Fin ((service.rosters phase.event).count owner))
      (member : slot ∈ (mixtureImpl.posterior (after.recall owner)).support) :
      (after.recall owner).length ≤ offset + slot.val ∧
        offset + slot.val < (after.recall owner).length + phase.visits.count owner := by
    rw [afterDef, ReactiveApplication.Implementation.posterior_respond, PMF.support_map]
      at member
    obtain ⟨pair, conditioned, rfl⟩ := member
    obtain ⟨matched, supported⟩ := mem_support_fiberConditional meets conditioned
    obtain ⟨memory, memorySupport, drawn⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨action, actionSupport, rfl⟩ := PMF.support_map .. ▸ drawn
    change action = response at matched
    subst matched
    have notBefore := posteriorFuture memory memorySupport
    have notNow : offset + memory.val ≠ (execution.recall owner).length := by
      intro now
      have scheduled : rosterOffset service.setup service.rosters owner phase.event + memory.val =
          (execution.recall owner).length := now
      have fires : family memory (execution.recall owner) (execution.observe app owner) =
          sourceServiceOpportunity service.setup service.leaks approx.profile owner phase.event
            (execution.recall owner) (execution.observe app owner) := by
        simp only [family, sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
          Option.map_some, scheduled, ↓reduceIte]
      change action ∈ (family memory (execution.recall owner)
        (execution.observe app owner)).support at actionSupport
      rw [fires, opening, PMF.support_map] at actionSupport
      obtain ⟨choice, _, submitted⟩ := actionSupport
      rcases transport with silent | ⟨id, replayed⟩
      · rw [silent] at submitted
        cases submitted
      · rw [replayed] at submitted
        cases submitted
    dsimp only
    rw [afterLength]
    change (execution.recall owner).length ≤ offset + memory.val at notBefore
    have within := memory.isLt
    change (execution.recall owner).length =
      offset + ((service.rosters phase.event).take phase.slot).count owner at counted
    constructor <;> omega
  unfold phaseConfigLaw phaseLaw DecisionPhase.tail
  rw [ending, mixed, ← mixture, PMF.map_bind]
  calc
    _ = (mixtureImpl.posterior (after.recall owner)).bind fun _ =>
        (commitKernel site.residual (site.source.view owner)).bind fun choice =>
          PMF.pure (execution.application.config.complete phase.event ready
            (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) choice)
            (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) choice)) := by
      apply bind_congr_on_support _
      intro slot member
      obtain ⟨notPassed, within⟩ := later slot member
      exact binding_slot_config_law service.setup service.leaks service.bounds service.rosters
        service.network approx.profile after site (by rw [sameApp]) afterGrant
        (afterUnsent.trans unsent) ready (by rw [sameApp]; exact timely) _
        (by change reactiveFreshSlot (app.observePlayer after.application owner) = _
            rw [sameApp]
            exact freshSlot)
        (by rw [sameApp]; exact fresh) (by rw [sameApp]; exact vacant)
        (by rw [sameApp]; exact unused) afterSerials afterPublished phase.visits slot
        notPassed within (phase.event.val + 1)
    _ = _ := PMF.bind_const _ _

end TimedApproximant

omit [Fintype Player] in
/-- A binding submission determines its source value, whatever its serial. -/
theorem reactiveBinding_injective {setup : Setup (Player := Player) (L := L)}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    {first second : PublicationResult (L.Val payload)} {firstSerial secondSerial : Nat}
    (same : (runtime setup).reactiveBinding leaks owner event payload first firstSerial =
      (runtime setup).reactiveBinding leaks owner event payload second secondSerial) :
    first = second := by
  have opening := congrArg
    (fun action : ((runtime setup).reactiveApplication leaks).Action =>
      match action.transmission with
      | some (.submit submission) =>
          (show WitnessedSubmission (graph setup) from submission).call.opening
      | _ => none) same
  cases first <;> cases second <;>
    dsimp only [EventGraphRuntime.reactiveBinding] at opening
  · rfl
  · cases opening
  · cases opening
  · cases opening
    rfl

/-- At the owner's unsent binding, a current submission fixes the source value:
the complete typed source terminal law after the submission is the source
continuation after that binding. -/
theorem BindingSource.submission_readout (service : SourceServiceSpec Player L)
    (timing : TimingLaw service.setup service.rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (wholeProfile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (wholeProfile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (wholeProfile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (covered : ∀ who, service.menu.Admissible (initialLaw service.setup) service.planLength
      service.scheduler who
        (sourceServiceTimedPolicy service.setup service.leaks service.rosters timing
          wholeProfile who))
    (assessment : service.model.BehavioralAssessment)
    (strategy : assessment.strategy = fun who =>
      service.menu.restrictPolicy (initialLaw service.setup) service.planLength service.scheduler
        who (sourceServiceTimedPolicy service.setup service.leaks service.rosters timing
          wholeProfile who))
    (mixed : assessment.IsFullyMixed)
    {event : (graph service.setup).EventId}
    (execution : (application service.setup service.leaks).Execution)
    (site : BindingSource service.setup wholeProfile event execution.application.config)
    (owner : Player) (ownerEq : site.owner = owner) (remainingFuel : Nat)
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remainingFuel, some owner, execution⟩))
    (serial : Nat)
    (freshSlot : reactiveFreshSlot (execution.observe
      (application service.setup service.leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (remaining : List Player) (before : List (ServiceInstruction (graph service.setup)))
    (granted : execution.application.serviceGrant = some event)
    (unsent : (runtime service.setup).eventRecorded service.leaks (execution.recall owner) event =
      false)
    (counted : (execution.recall owner).length + 1 + remaining.count owner =
      rosterOffset service.setup service.rosters owner event + (service.rosters event).count owner)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime service.setup) event)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (split : rosterPlanPrefix service.setup service.rosters (event.val + 1) =
      before ++ .player owner :: (remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event])))
    (position : execution.environmentRecall.length = before.length + 1)
    (choice : PublicationResult (L.Val site.payload))
    (allowed : (runtime service.setup).reactiveBinding service.leaks owner event site.payload
      choice serial ∈ service.menu.actions owner (execution.recall owner)
        (execution.observe (application service.setup service.leaks) owner)) :
    ((runtime service.setup).runInteractionPlan service.leaks
      (sourceServiceTimedPolicy service.setup service.leaks service.rosters timing wholeProfile)
      service.network ((remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++
          [.expire event])) ++ rosterPlanSuffix service.setup service.rosters (event.val + 1))
      (execution.respond (application service.setup service.leaks) owner
        ((runtime service.setup).reactiveBinding service.leaks owner event site.payload choice
          serial))).map
      (fun final => sourceReadout service.setup service.leaks
        ((application service.setup service.leaks).finished final)) =
      (service.setup.continuationLaw wholeProfile (sourceServicePrefix? service.setup
        (event.val + 1) (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) choice)
          (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) choice)))).map
        some := by
  have outputEq := site.outputEq
  obtain ⟨Γ, names, name, siteOwner, payload, fresh, guard, next, residual, refs, source,
    embedding, refsBefore, aligned, agree, history, head⟩ := site
  dsimp only at ownerEq outputEq allowed choice ⊢
  subst ownerEq
  subst head
  let app := application service.setup service.leaks
  let response := (runtime service.setup).reactiveBinding service.leaks siteOwner
    (embedding.event ⟨0, by simp [eventCount]⟩) payload choice serial
  have owned := binding_actor service.setup _ siteOwner payload outputEq
  have law := sourceServiceTimedPolicy_binding_response_continuation service.setup service.leaks
    service.bounds service.values service.initialValues service.capacity service.rosters
    service.opportunities.binding timing timingFull service.network wholeProfile permitted
    effective covered assessment strategy mixed fresh guard next residual refs source embedding
    refsBefore _ aligned execution remainingFuel trace agree history serial freshSlot candidate
    remaining before outputEq owned granted unsent counted ready timely vacant unused serials
    published split position response allowed
  dsimp only at law
  refine law.trans ?_
  let site : BindingSource service.setup wholeProfile (embedding.event ⟨0, by simp [eventCount]⟩)
      execution.application.config :=
    ⟨Γ, names, name, siteOwner, payload, fresh, guard, next, residual, refs, source, embedding,
      refsBefore, aligned, agree, history, rfl⟩
  have opening := BindingSource.opportunity_law service.leaks execution site granted unsent serial
    freshSlot candidate
  have present := roster_fullyMixed_response_support service.setup service.leaks
    service.rosters service.network service.menu
    (sourceServiceTimedPolicy service.setup service.leaks service.rosters timing wholeProfile)
    covered assessment strategy mixed siteOwner remainingFuel execution trace response allowed
  have grant : PublicView.serviceGrant
      (execution.observe (application service.setup service.leaks)
        siteOwner).application.publicView =
        some (embedding.event ⟨0, by simp [eventCount]⟩) := granted
  simp only [sourceServiceTimedPolicy, grant, owned, ↓reduceDIte,
    ReactiveApplication.policyMixture_policy, PMF.support_bind] at present
  obtain ⟨slot, slotSupport, drawn⟩ := Set.mem_iUnion₂.mp present
  have submitted (other : (application service.setup service.leaks).Action)
      (replayed : other ∈ (app.replayPolicy (execution.recall siteOwner)
        (execution.observe app siteOwner)).support) (same : other = response) : False := by
    have transmitted := congrArg ReactiveApplication.Action.transmission same
    rcases app.replayPolicy_cases _ _ other replayed with rfl | ⟨id, rfl⟩ <;>
      simp [response, EventGraphRuntime.reactiveBinding] at transmitted
  by_cases now : rosterOffset service.setup service.rosters siteOwner
      (embedding.event ⟨0, by simp [eventCount]⟩) + slot.val = (execution.recall siteOwner).length
  swap
  · simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy, Option.map_some,
      Option.some.injEq, now, ↓reduceIte] at drawn
    exact (submitted response drawn rfl).elim
  simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy, Option.map_some,
    now, ↓reduceIte] at drawn
  rw [opening, PMF.support_map] at drawn
  obtain ⟨value, valueSupport, valueEq⟩ := drawn
  have sameValue := reactiveBinding_injective service.leaks siteOwner _ payload valueEq
  subst sameValue
  refine (bind_congr_on_support _ (g := fun _ => _) ?_).trans (PMF.bind_const _ _)
  intro tag member
  obtain ⟨matched, supported⟩ := mem_support_fiberConditional ⟨(value, slot, response), rfl, by
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨value, valueSupport, ?_⟩
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨slot, slotSupport, ?_⟩
    simp only [ReactiveApplication.scheduledPolicy, Option.map_some, now, ↓reduceIte,
      PMF.pure_map, PMF.mem_support_pure_iff _ _]
    rfl⟩ member
  obtain ⟨tagValue, _, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨tagSlot, _, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rest)
  obtain ⟨action, actionSupport, rfl⟩ := PMF.support_map .. ▸ rest
  have actionEq : action = response := Option.some.inj matched
  by_cases fires : rosterOffset service.setup service.rosters siteOwner
      (embedding.event ⟨0, by simp [eventCount]⟩) + tagSlot.val =
        (execution.recall siteOwner).length
  · simp only [ReactiveApplication.scheduledPolicy, Option.map_some, fires, ↓reduceIte,
      PMF.mem_support_pure_iff _ _] at actionSupport
    rw [actionSupport] at actionEq
    have tagValueEq := reactiveBinding_injective service.leaks siteOwner _ payload actionEq
    subst tagValueEq
    rfl
  · simp only [ReactiveApplication.scheduledPolicy, Option.map_some, Option.some.injEq, fires,
      ↓reduceIte] at actionSupport
    exact (submitted action actionSupport actionEq).elim


namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- At every retained decision during a binding event's phase, the residual
source commitment is aligned with the given profile, and three source facts
hold at the event's boundary. The source continuation draws the commitment
value and continues from the configuration that completes the binding with it.
Any owner action steps to the configuration completing the binding with that
action's value. The owner's source action law has the commitment lottery as its
value marginal. The native completion with any value decodes to the source
commitment of that value. -/
theorem exists_bindingSource_step (profile : BehavioralProfile service.setup.program)
    {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {owner : Player} {payload : L.Ty}
    (isBinding : (graph service.setup).outputLayout phase.event = .binding owner payload) :
    ∃ site : BindingSource service.setup profile phase.event execution.application.config,
      (∀ value, decodeEventAction service.setup.program phase.event
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value) =
          some (.commit site.owner site.name site.payload value)) ∧
      ∀ ready : execution.application.config.cut.Ready phase.event,
        (service.setup.continuationLaw profile
          (sourceServicePrefix? service.setup phase.event.val execution.application.config) =
        (commitKernel site.residual (site.source.view site.owner)).bind fun choice =>
          service.setup.continuationLaw profile (sourceServicePrefix? service.setup
            (phase.event.val + 1) (execution.application.config.complete phase.event ready
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) choice)
              (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) choice)))) ∧
        (∀ joint : Player → Option (OwnAction Player L),
          service.setup.protocolStep
            (sourceServicePrefix? service.setup phase.event.val execution.application.config)
            joint =
          PMF.pure (sourceServicePrefix? service.setup (phase.event.val + 1)
            (execution.application.config.complete phase.event ready
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm)
                (OwnAction.binding site.owner site.name site.payload (joint site.owner)))
              (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
                (OwnAction.binding site.owner site.name site.payload (joint site.owner)))))) ∧
        ∀ state, sourceServicePrefix? service.setup phase.event.val
            execution.application.config = some state →
          ¬ ProtocolState.terminal service.setup.program state →
          ((profile site.owner).protocolAction service.setup.program
              (ProtocolState.observe site.owner service.setup.program state)).map
            (OwnAction.binding site.owner site.name site.payload) =
          commitKernel site.residual (site.source.view site.owner) := by
  obtain ⟨phaseEvent, phaseSlot, phaseSelected, phasePosition, phaseGranted⟩ := phase
  dsimp only at isBinding ⊢
  obtain ⟨event, _, _, _, _, Γ, names, remaining, remainingProfile, source, refs, embedding,
      refsBefore, aligned, _, ⟨_, _, lift, commutes, transport⟩, _, _, _, _, grant, _, _, _, _,
      publicEq, checkpoint, _⟩ :=
    sourceService_decision_boundary service.setup service.leaks service.bounds service.values
      service.capacity service.rosters service.opportunities.binding service.network profile
      who ⟨remaining, some who, execution⟩ trace rfl
  have same : event = phaseEvent := Option.some.inj
    (((congrArg PublicView.serviceGrant publicEq).trans grant).symm.trans phaseGranted)
  subst same
  cases remaining with
  | ret result =>
      have count := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at count
      have inside := event.isLt
      change event.val < eventCount service.setup.program at inside
      omega
  | sample name fresh law next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have actor := aligned.actorEq ⟨0, by simp [eventCount]⟩
      rw [headEq] at actor
      change (graph service.setup).actor? event = none at actor
      rw [binding_actor service.setup event owner payload isBinding] at actor
      cases actor
  | @reveal Γ names published owner name payload fresh binding unresolved next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have output : (graph service.setup).outputLayout event = .publication payload := by
        rw [← headEq]
        change outputLayout service.setup.program (embedding.event _) = _
        simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
      cases output.symm.trans isBinding
  | @commit Γ names name siteOwner sitePayload fresh guard next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      subst headEq
      let site : BindingSource service.setup profile (embedding.event ⟨0, by simp [eventCount]⟩)
          execution.application.config :=
        ⟨Γ, names, name, siteOwner, sitePayload, fresh, guard, next, remainingProfile, refs,
          source, embedding, refsBefore, aligned, checkpoint.agrees, checkpoint.history, rfl⟩
      have outputEq : (graph service.setup).outputLayout
          (embedding.event ⟨0, by simp [eventCount]⟩) = .binding siteOwner sitePayload :=
        site.outputEq
      have decoded (value : PublicationResult (L.Val sitePayload)) :
          decodeEventAction service.setup.program (embedding.event ⟨0, by simp [eventCount]⟩)
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) value) =
              some (.commit siteOwner name sitePayload value) := by
        have action := aligned.actionEq ⟨0, by simp [eventCount]⟩
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) value)
        simpa [outputEq, decodeEventAction] using action
      refine ⟨site, decoded, fun ready => ?_⟩
      have now := transport 0 execution.application.config.store
        (decodeHistory service.setup.program (execution.application.config.history.map
          (service.setup.eventGraph.fromModeCompletion .sequential)))
      rw [checkpoint.decode _ embedding.ref] at now
      simp only [Nat.add_zero, Option.map_some] at now
      change sourceServicePrefix? service.setup _ execution.application.config = _ at now
      have later (value : PublicationResult (L.Val sitePayload)) :
          sourceServicePrefix? service.setup ((embedding.event ⟨0, by simp [eventCount]⟩).val + 1)
            (execution.application.config.complete (embedding.event ⟨0, by simp [eventCount]⟩)
              ready (cast (congrArg EventGraph.EventField.Action outputEq.symm) value)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)) =
          some (lift (Sum.inr (ProtocolState.entry next
            (commitSuccessor name guard source value)))) := by
        have completed := checkpoint.commit name guard _ rfl ready outputEq
          (fun ref => refsBefore ref ⟨0, by simp [eventCount]⟩) value (decoded value)
        have recovered := completed.decode next (fun tail => embedding.ref tail.succ)
        change sourceServicePrefix? service.setup _
          (execution.application.complete (embedding.event ⟨0, by simp [eventCount]⟩) ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) value)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)).config = _
        unfold sourceServicePrefix?
        rw [transport 1, decodeSourcePrefix?_commit]
        exact congrArg (fun decoded => (Option.map Sum.inr decoded).map lift) recovered
      refine ⟨?_, ?_, ?_⟩
      · rw [now]
        change ProtocolState.continuationLaw service.setup.program profile
          (lift (ProtocolState.entry _ source)) = _
        rw [← sourceStep_continuation, commutes.1]
        change (((ProtocolState.behavioralStateStep _ remainingProfile (.inl source)).map
          lift).bind _) = _
        rw [ProtocolState.behavioralStateStep_commit_entry, PMF.bind_map, PMF.bind_map]
        apply bind_congr_on_support _
        intro choice _
        rw [later choice]
        rfl
      · intro joint
        rw [now, later]
        change ((ProtocolState.step _ (lift (ProtocolState.entry _ source)) joint).map some) = _
        rw [commutes.2.1]
        change ((PMF.pure (Sum.inr (ProtocolState.entry next (commitSuccessor name guard
          source (OwnAction.binding siteOwner name sitePayload (joint siteOwner)))))).map
            lift).map some = _
        simp only [PMF.pure_map]
        rfl
      · intro state decoded running
        rw [now] at decoded
        have stateEq := Option.some.inj decoded
        subst stateEq
        have viaResidual := commutes.1 (ProtocolState.entry _ source)
        change _ = ((ProtocolState.behavioralStateStep _ remainingProfile (.inl source)).map
          lift) at viaResidual
        rw [ProtocolState.behavioralStateStep_commit_entry] at viaResidual
        let advance := fun value : PublicationResult (L.Val sitePayload) =>
          lift (Sum.inr (ProtocolState.entry next (commitSuccessor name guard source value)))
        have viaWhole : ProtocolState.behavioralStateStep service.setup.program profile
            (lift (ProtocolState.entry _ source)) =
            ((profile siteOwner).protocolAction service.setup.program
              (ProtocolState.observe siteOwner service.setup.program
                (lift (ProtocolState.entry _ source)))).map
              (fun action => advance (OwnAction.binding siteOwner name sitePayload action)) := by
          unfold ProtocolState.behavioralStateStep
          simp only [running, ↓reduceIte]
          have stepped (joint : Player → Option (OwnAction Player L)) :
              ProtocolState.step service.setup.program (lift (ProtocolState.entry _ source))
                joint = PMF.pure (advance
                  (OwnAction.binding siteOwner name sitePayload (joint siteOwner))) := by
            rw [commutes.2.1]
            change (PMF.pure (Sum.inr (ProtocolState.entry next (commitSuccessor name guard
              source (OwnAction.binding siteOwner name sitePayload (joint siteOwner)))))).map
                lift = _
            simp only [PMF.pure_map]
            rfl
          rw [show ProtocolState.step service.setup.program (lift (ProtocolState.entry _ source)) =
            fun joint : Player → Option (OwnAction Player L) => PMF.pure (advance
              (OwnAction.binding siteOwner name sitePayload (joint siteOwner))) from
                funext stepped, ← ← PMF.bind_pure_comp, Function.comp_def]
          change (independentProduct _).map ((fun action =>
            advance (OwnAction.binding siteOwner name sitePayload action)) ∘
              fun joint : Player → Option (OwnAction Player L) => joint siteOwner) = _
          rw [← PMF.map_comp, independentProduct_map_eval]
        have injective : Function.Injective advance := by
          intro first second same
          have successor := commutes.2.2 same
          have entries := (Sum.inr_injective successor)
          have configs := ProtocolState.entry_injective next entries
          simpa only [commitSuccessor, Env.cons_get_here] using
            congrArg (fun config : Config Player L
              ((name, .commitment siteOwner sitePayload) :: Γ) =>
                config.state.get HasVar.here) configs
        apply pmf_map_injective injective
        rw [PMF.map_comp]
        change ((profile siteOwner).protocolAction service.setup.program
          (ProtocolState.observe siteOwner service.setup.program
            (lift (ProtocolState.entry _ source)))).map
              (fun action => advance (OwnAction.binding siteOwner name sitePayload action)) = _
        rw [← viaWhole, viaResidual, PMF.map_comp]
        rfl

end SourceServiceSpec


namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

/-- The source continuation after the owner's binding at `event` completes with
a value. -/
def bindingContinuation {execution : (application service.setup service.leaks).Execution}
    {event : (graph service.setup).EventId}
    (ready : execution.application.config.cut.Ready event) {who : Player} {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout event = .binding who payload)
    (value : PublicationResult (L.Val payload)) :
    PMF (Option (State L service.setup.program.terminalCtx)) :=
  approx.boundaryContinuation (event.val + 1)
    (execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) value)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) value))

/-- The native and source laws at an owner's decision on its unsent binding at
`event`. The native continuation of every legal current response is the source
continuation after a binding value: the value the response submits, or, after a
transport response, the commitment lottery `values`. The prescribed native
lottery averages to the source continuation from the event's boundary. The
source side holds at the decoded boundary state: its continuation, the step of
any owner action, and the value marginal of the owner's action law. -/
structure UnsentBindingLaws {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {event : (graph service.setup).EventId} {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout event = .binding who payload)
    (ready : execution.application.config.cut.Ready event) where
  name : VarId
  values : PMF (PublicationResult (L.Val payload))
  decoded : ∀ value, decodeEventAction service.setup.program event
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) value) =
      some (.commit who name payload value)
  boundary : (service.setup.continuationLaw approx.profile (sourceServicePrefix? service.setup
    event.val execution.application.config)).map some =
      values.bind (approx.bindingContinuation ready outputEq)
  step : ∀ joint : Player → Option (OwnAction Player L),
    service.setup.protocolStep (sourceServicePrefix? service.setup event.val
      execution.application.config) joint =
    PMF.pure (sourceServicePrefix? service.setup (event.val + 1)
      (execution.application.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (OwnAction.binding who name payload (joint who)))
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (OwnAction.binding who name payload (joint who)))))
  marginal : ∀ state, sourceServicePrefix? service.setup event.val
      execution.application.config = some state →
    ¬ ProtocolState.terminal service.setup.program state →
    ((approx.profile who).protocolAction service.setup.program
      (ProtocolState.observe who service.setup.program state)).map
        (OwnAction.binding who name payload) = values
  prescribed : (approx.players who (execution.recall who)
    (execution.observe (application service.setup service.leaks) who)).bind
      (approx.responseReadout phase) = values.bind (approx.bindingContinuation ready outputEq)
  responses : ∀ response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who),
    (∃ value ∈ values.support, (∃ serial, response =
        (runtime service.setup).reactiveBinding service.leaks who event payload value serial) ∧
      approx.responseReadout phase response = approx.bindingContinuation ready outputEq value) ∨
    ((response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) ∧
      approx.responseReadout phase response =
        values.bind (approx.bindingContinuation ready outputEq))

/-- Every decision of the owner on its unsent binding has its native and source
laws. -/
theorem unsent_binding_decision {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout phase.event = .binding who payload)
    (unsent : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
      phase.event = false)
    (ready : execution.application.config.cut.Ready phase.event) :
    Nonempty (approx.UnsentBindingLaws phase outputEq ready) := by
  have owned := binding_actor service.setup phase.event who payload outputEq
  obtain ⟨codeEq, node⟩ := binding_nodeView service.setup phase.event who payload outputEq
  obtain ⟨_, timely, _, _, _, serials, resources⟩ := sourceService_binding_decision_resources
    service.setup service.leaks service.bounds service.values service.capacity service.rosters
    service.opportunities.binding service.network who ⟨remaining, some who, execution⟩ trace rfl
    phase.event phase.granted who payload outputEq codeEq node owned
  obtain ⟨_, freshSlot, fresh, unused, vacant, _, published⟩ := resources unsent
  have counted := service.recall_count trace phase
  have visitsCount : ((service.rosters phase.event).take phase.slot).count who + 1 +
      phase.visits.count who = (service.rosters phase.event).count who := by
    conv_rhs => rw [phase.roster_split]
    simp only [List.count_append, List.count_cons_self]
    omega
  have ending : rosterPhaseEnding service.setup phase.event =
      .includeLatest phase.event who :: (List.replicate (phase.event.val + 1) .tick ++
        [.expire phase.event]) := by
    simp only [rosterPhaseEnding, owned, List.cons_append, List.nil_append]
  have split : rosterPlanPrefix service.setup service.rosters (phase.event.val + 1) =
      phase.before ++ .player who :: (phase.visits.map ServiceInstruction.player ++
        (.includeLatest phase.event who :: List.replicate (phase.event.val + 1) .tick ++
          [.expire phase.event])) := by
    rw [phase.prefix_split, DecisionPhase.tail, ending]
    simp only [List.cons_append]
  obtain ⟨site, decodedAction, stepFacts⟩ := service.exists_bindingSource_step approx.profile
    trace phase outputEq
  obtain ⟨sourceStep, anyStep, marginal⟩ := stepFacts ready
  obtain ⟨Γ, names, name, siteOwner, sitePayload, fresh', guard, next, residual, refs, source,
    embedding, refsBefore, aligned, agree, history, head⟩ := site
  have kinds := EventGraph.EventField.binding.inj
    ((BindingSource.outputEq ⟨Γ, names, name, siteOwner, sitePayload, fresh', guard, next,
      residual, refs, source, embedding, refsBefore, aligned, agree, history, head⟩).symm.trans
        outputEq)
  dsimp only at kinds
  obtain ⟨rfl, rfl⟩ := kinds
  let site : BindingSource service.setup approx.profile phase.event
      execution.application.config :=
    ⟨Γ, names, name, siteOwner, sitePayload, fresh', guard, next, residual, refs, source,
      embedding, refsBefore, aligned, agree, history, head⟩
  let values := commitKernel residual (source.view siteOwner)
  have opening := BindingSource.opportunity_law service.leaks execution site phase.granted unsent
    _ freshSlot fresh
  have submitted (value : PublicationResult (L.Val sitePayload))
      (allowed : (runtime service.setup).reactiveBinding service.leaks siteOwner phase.event
        sitePayload value (execution.application.publicView.bindingCount siteOwner) ∈
          service.menu.actions siteOwner (execution.recall siteOwner)
            (execution.observe (application service.setup service.leaks) siteOwner)) :
      approx.responseReadout phase ((runtime service.setup).reactiveBinding service.leaks
        siteOwner phase.event sitePayload value
          (execution.application.publicView.bindingCount siteOwner)) =
        approx.bindingContinuation ready outputEq value := by
    unfold responseReadout
    rw [DecisionPhase.tail, ending]
    exact BindingSource.submission_readout service approx.timing approx.timingFull
      approx.profile approx.admitted approx.effective approx.covered approx.assessment
      approx.strategy approx.mixed execution site siteOwner rfl remaining trace _ freshSlot
      fresh phase.visits phase.before phase.granted unsent (by rw [counted]; omega) ready
      timely vacant unused serials published split phase.position_before value allowed
  have transported (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions siteOwner (execution.recall siteOwner)
        (execution.observe (application service.setup service.leaks) siteOwner))
      (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) :
      approx.responseReadout phase response =
        values.bind (approx.bindingContinuation ready outputEq) := by
    rw [approx.response_continuation_law trace phase response allowed,
      approx.unsent_binding_transport_config_law trace phase site rfl unsent ready response
        allowed transport, PMF.bind_bind]
    simp only [PMF.pure_bind]
    rfl
  have grant : PublicView.serviceGrant
      (execution.observe (application service.setup service.leaks)
        siteOwner).application.publicView = some phase.event := phase.granted
  let mixtureImpl := (application service.setup service.leaks).policyMixture
    (approx.timing phase.event siteOwner owned)
    (sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
      siteOwner phase.event)
  have policyEq : approx.players siteOwner (execution.recall siteOwner)
      (execution.observe (application service.setup service.leaks) siteOwner) =
      (mixtureImpl.posterior (execution.recall siteOwner)).bind fun slot =>
        sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
          siteOwner phase.event slot (execution.recall siteOwner)
            (execution.observe (application service.setup service.leaks) siteOwner) := by
    simp only [players, sourceServiceTimedPolicy, grant, owned, ↓reduceDIte]
    exact (application service.setup service.leaks).policyMixture_policy _ _ _ _
  have slotLaw (slot : Fin ((service.rosters phase.event).count siteOwner)) :
      (rosterOffset service.setup service.rosters siteOwner phase.event + slot.val =
          (execution.recall siteOwner).length ∧
        sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
          siteOwner phase.event slot (execution.recall siteOwner)
            (execution.observe (application service.setup service.leaks) siteOwner) =
          values.map fun value => (runtime service.setup).reactiveBinding service.leaks siteOwner
            phase.event sitePayload value (execution.application.publicView.bindingCount siteOwner))
      ∨ sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
          siteOwner phase.event slot (execution.recall siteOwner)
            (execution.observe (application service.setup service.leaks) siteOwner) =
          (application service.setup service.leaks).replayPolicy (execution.recall siteOwner)
            (execution.observe (application service.setup service.leaks) siteOwner) := by
    by_cases now : rosterOffset service.setup service.rosters siteOwner phase.event + slot.val =
        (execution.recall siteOwner).length
    · left
      refine ⟨now, ?_⟩
      simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy, Option.map_some,
        now, ↓reduceIte]
      exact opening
    · right
      simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy, Option.map_some,
        Option.some.injEq, now, ↓reduceIte]
  have classify (response : (application service.setup service.leaks).Action)
      (supported : response ∈ (approx.players siteOwner (execution.recall siteOwner)
        (execution.observe (application service.setup service.leaks) siteOwner)).support) :
      (∃ value ∈ values.support, response = (runtime service.setup).reactiveBinding
        service.leaks siteOwner phase.event sitePayload value
          (execution.application.publicView.bindingCount siteOwner)) ∨
      (response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) := by
    rw [policyEq, PMF.support_bind] at supported
    obtain ⟨slot, _, drawn⟩ := Set.mem_iUnion₂.mp supported
    rcases slotLaw slot with ⟨_, fires⟩ | waits
    · rw [fires, PMF.support_map] at drawn
      obtain ⟨value, valueSupport, same⟩ := drawn
      exact Or.inl ⟨value, valueSupport, same.symm⟩
    · rw [waits] at drawn
      exact Or.inr ((application service.setup service.leaks).replayPolicy_cases _ _ response drawn)
  have allowedOf (response : (application service.setup service.leaks).Action)
      (supported : response ∈ (approx.players siteOwner (execution.recall siteOwner)
        (execution.observe (application service.setup service.leaks) siteOwner)).support) :
      response ∈ service.menu.actions siteOwner (execution.recall siteOwner)
        (execution.observe (application service.setup service.leaks) siteOwner) :=
    approx.covered siteOwner ⟨remaining, some siteOwner, execution⟩ trace rfl response supported
  refine ⟨⟨name, values, decodedAction, ?_, anyStep, marginal, ?_, ?_⟩⟩
  · rw [sourceStep, PMF.map_bind]
    rfl
  · rw [policyEq, PMF.bind_bind]
    refine (bind_congr_on_support _ (g := fun _ => values.bind (fun value =>
      approx.bindingContinuation ready outputEq value)) ?_).trans
      (PMF.bind_const _ _)
    intro slot slotSupport
    have present (response : (application service.setup service.leaks).Action)
        (drawn : response ∈ (sourceServiceTimedFamily service.setup service.leaks
          service.rosters approx.profile siteOwner phase.event slot (execution.recall siteOwner)
            (execution.observe (application service.setup service.leaks) siteOwner)).support) :
        response ∈ (approx.players siteOwner (execution.recall siteOwner)
          (execution.observe (application service.setup service.leaks) siteOwner)).support := by
      rw [policyEq, PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨slot, slotSupport, drawn⟩
    rcases slotLaw slot with ⟨_, fires⟩ | waits
    · rw [fires, PMF.bind_map]
      apply bind_congr_on_support _
      intro value valueSupport
      exact submitted value (allowedOf _ (present _ (by
        rw [fires, PMF.support_map]
        exact ⟨value, valueSupport, rfl⟩)))
    · rw [waits]
      refine (bind_congr_on_support _ ?_).trans (PMF.bind_const _ _)
      intro response supported
      exact transported response (allowedOf response (present response (by
        rw [waits]
        exact supported)))
        ((application service.setup service.leaks).replayPolicy_cases _ _ response supported)
  · intro response allowed
    have present := roster_fullyMixed_response_support service.setup service.leaks
      service.rosters service.network service.menu approx.players approx.covered
      approx.assessment approx.strategy approx.mixed siteOwner remaining execution trace
      response allowed
    rcases classify response present with ⟨value, valueSupport, rfl⟩ | transport
    · exact Or.inl ⟨value, valueSupport, ⟨_, rfl⟩, submitted value allowed⟩
    · exact Or.inr ⟨transport, transported response allowed transport⟩

end TimedApproximant

namespace TimedApproximant

/-- Each history of an owner site is an actual decision whose own recall and
view are the site's information. -/
theorem site_decision {service : SourceServiceSpec Player L}
    (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view)) {event : (graph service.setup).EventId}
    (granted : view.application.publicView.serviceGrant = some event)
    (history : service.model.InformationHistory who site.1) :
    ∃ (remaining : Nat) (execution : (application service.setup service.leaks).Execution)
      (_ : history.1.state = some ⟨remaining, some who, execution⟩)
      (phase : DecisionPhase service.setup service.leaks service.rosters who execution),
      phase.event = event ∧ execution.recall who = past ∧
        execution.observe (application service.setup service.leaks) who = view := by
  have active := InformationModel.InformationSite.active service.model site history
  obtain ⟨control, current⟩ : ∃ control, history.1.state = some control := by
    cases state : history.1.state with
    | none => rw [state] at active; cases active
    | some control => exact ⟨control, rfl⟩
  have actor : control.actor = some who := by rw [current] at active; exact active
  obtain ⟨remaining, actorValue, execution⟩ := control
  change actorValue = some who at actor
  subst actorValue
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    current ▸ history.1.trace
  obtain ⟨phase⟩ := service.exists_decisionPhase who remaining execution trace
  have input := Option.some.inj
    ((service.infoOf_decision history.1 current).symm.trans (history.2.trans observed))
  have grant : execution.application.serviceGrant = some event :=
    (congrArg (fun pair : List (application service.setup service.leaks).PlayerEntry ×
      (application service.setup service.leaks).PlayerView =>
        pair.2.application.publicView.serviceGrant) input).trans granted
  exact ⟨remaining, execution, current, phase, Option.some.inj (phase.granted.symm.trans grant),
    congrArg Prod.fst input, congrArg Prod.snd input⟩

/-- The prescribed local law of a timed approximant at an actual decision is
the timed policy's response law. -/
theorem prescribed_response_law {service : SourceServiceSpec Player L}
    (approx : TimedApproximant service) {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (info : service.model.InfoState who)
    (observed : info = some (execution.recall who,
      execution.observe (application service.setup service.leaks) who)) :
    (approx.assessment.strategy who info).map (fun choice => choice.1.getD ⟨none⟩) =
      approx.players who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who) := by
  subst observed
  have mapped := service.menu.restrictPolicy_map_val (initialLaw service.setup)
    service.planLength service.scheduler who (approx.players who) (execution.recall who)
    (execution.observe (application service.setup service.leaks) who)
    (approx.covered who ⟨remaining, some who, execution⟩ trace rfl)
  have split : (fun choice : service.model.Choice who (some (execution.recall who,
      execution.observe (application service.setup service.leaks) who)) =>
        choice.1.getD ⟨none⟩) = (fun action => action.getD ⟨none⟩) ∘ Subtype.val := rfl
  have strategyAt : approx.assessment.strategy who (some (execution.recall who,
      execution.observe (application service.setup service.leaks) who)) =
      service.menu.restrictPolicy (initialLaw service.setup) service.planLength
        service.scheduler who (approx.players who) (some (execution.recall who,
          execution.observe (application service.setup service.leaks) who)) := by
    rw [approx.strategy]
  rw [split, ← PMF.map_comp, strategyAt, mapped, PMF.map_comp]
  exact PMF.map_id _

open Classical in
/-- At an owner's visit to its own unsent binding, every local lottery of the
`ofSource` approximant has prescribed and alternative laws equal to the
prescribed and alternative laws of one mixture of original source assessment
comparisons. A native submission of a value is simulated by the source
commitment of that value, and a transport response by the prescribed source
action law, which it leaves unchanged. -/
theorem unsent_binding_comparisons (service : SourceServiceSpec Player L)
    (timing : TimingLaw service.setup service.rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (source : service.sourceModel.BehavioralAssessment)
    [∀ who (site : service.sourceModel.InformationSite who),
      Fintype (service.sourceModel.InformationHistory who site.1)]
    (full : ∀ who info, FullSupport (source.strategy who info))
    (sourceBayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      service.sourceModel source
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program)))
    (approx : TimedApproximant service)
    (built : approx = ofSource service timing timingFull source.strategy full)
    (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId} {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout event = .binding who payload)
    (granted : view.application.publicView.serviceGrant = some event)
    (unsent : (runtime service.setup).eventRecorded service.leaks past event = false)
    (law : PMF (service.model.Choice who site.1)) :
    ∃ mixture : PMF (service.sourceModel.AssessmentDeviation who),
      (service.model.assessmentComparison service.readout service.fuel approx.assessment who
        (site, (approx.assessment.strategy who).withLaw site.1 law)).prescribed =
        mixture.bind (fun deviation => (service.sourceModel.assessmentComparison
            (fun final => service.setup.protocolReadout final.state)
            (instructionCount service.setup.program + 1) source who deviation).prescribed) ∧
      (service.model.assessmentComparison service.readout service.fuel approx.assessment who
        (site, (approx.assessment.strategy who).withLaw site.1 law)).alternative =
        mixture.bind (fun deviation => (service.sourceModel.assessmentComparison
            (fun final => service.setup.protocolReadout final.state)
            (instructionCount service.setup.program + 1) source who deviation).alternative) := by
  have owned := binding_actor service.setup event who payload outputEq
  obtain ⟨codeEq, node⟩ := binding_nodeView service.setup event who payload outputEq
  obtain ⟨sourceView, sourceHistories⟩ := owner_site_source_histories service timing
    timingFull source full sourceBayes approx built who site past view observed owned granted
  let admission := CommitmentInterface.values service.setup.program
  let baseline := service.setup.toProtocolBehavioralPolicy admission who (approx.profile who)
    (approx.admitted who) (some sourceView)
  -- The decision data of every history of the site.
  have atHistory (history : service.model.InformationHistory who site.1) :
      ∃ (remaining : Nat) (execution : (application service.setup service.leaks).Execution)
        (_ : history.1.state = some ⟨remaining, some who, execution⟩)
        (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
        (_ : phase.event = event) (trace : (service.menu.protocol (initialLaw service.setup)
          service.planLength service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
        (ready : execution.application.config.cut.Ready event),
        execution.recall who = past ∧
          execution.observe (application service.setup service.leaks) who = view ∧
          Nonempty (approx.UnsentBindingLaws phase outputEq ready) := by
    obtain ⟨remaining, execution, current, phase, same, recallEq, viewEq⟩ :=
      site_decision who site past view observed granted history
    have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
        service.scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
      current ▸ history.1.trace
    obtain ⟨phaseEvent, slot, selected, position, phaseGranted⟩ := phase
    dsimp only at same
    subst same
    let phase : DecisionPhase service.setup service.leaks service.rosters who execution :=
      ⟨phaseEvent, slot, selected, position, phaseGranted⟩
    obtain ⟨ready, _⟩ := sourceService_binding_decision_resources service.setup service.leaks
      service.bounds service.values service.capacity service.rosters
      service.opportunities.binding service.network who ⟨remaining, some who, execution⟩ trace
      rfl phaseEvent phaseGranted who payload outputEq codeEq node owned
    have unsentNow : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
        phaseEvent = false := recallEq ▸ unsent
    exact ⟨remaining, execution, current, phase, rfl, trace, ready, recallEq, viewEq,
      approx.unsent_binding_decision trace phase outputEq unsentNow ready⟩
  obtain ⟨reference, _, _⟩ := site.2
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨⟨name, _, referenceDecoded, _⟩⟩⟩ := atHistory reference
  let realize : PublicationResult (L.Val payload) →
      (service.setup.informationModel admission).Choice who (some sourceView) := fun value =>
    if found : ∃ choice ∈ baseline.support, OwnAction.binding who name payload choice.1 = value
    then found.choose else baseline.support_nonempty.choose
  let submittedValue : (application service.setup service.leaks).Action →
      Option (PublicationResult (L.Val payload)) := fun response =>
    if found : ∃ value serial, response = (runtime service.setup).reactiveBinding service.leaks
      who event payload value serial then some found.choose else none
  let sourceLaw : PMF ((service.setup.informationModel admission).Choice who
      (some sourceView)) :=
    law.bind fun choice => match submittedValue (choice.1.getD ⟨none⟩) with
      | some value => PMF.pure (realize value)
      | none => baseline
  obtain ⟨alternative, admittedAlternative, alternativeLaw⟩ :=
    service.setup.exists_admitted_local_law admission approx.profile approx.admitted who
      (some sourceView) sourceLaw
  apply owner_comparisons_of_continuations service timing timingFull source full sourceBayes
    approx built who site past view observed owned granted law alternative admittedAlternative
  · intro history _
    obtain ⟨remaining, execution, current, phase, _, trace, ready, recallEq, viewEq,
      ⟨⟨_, values, _, sourceStep, _, _, prescribed, _⟩⟩⟩ := atHistory history
    have localLaw := approx.local_law_readout history.1 current phase history.2
      (approx.assessment.strategy who site.1)
    rw [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self] at localLaw
    rw [localLaw, prescribed_response_law approx trace site.1
      (observed.trans (by rw [recallEq, viewEq])), prescribed, ← sourceStep]
    simp only [decodedState, current, Option.bind_some]
  · intro history member
    obtain ⟨remaining, execution, current, phase, _, trace, ready, recallEq, viewEq,
      ⟨⟨otherName, values, decodedHere, sourceStep, anyStep, marginal, _, responses⟩⟩⟩ :=
        atHistory history
    have sameName : otherName = name := by
      have both := (decodedHere .failure).symm.trans (referenceDecoded .failure)
      simpa using both
    subst sameName
    obtain ⟨sourceHistory, sourceState, running, active, info⟩ := sourceHistories history member
    have decodedEq : decodedState service event history.1 =
        sourceServicePrefix? service.setup event.val execution.application.config := by
      simp only [decodedState, current, Option.bind_some]
    rw [decodedEq] at sourceState
    obtain ⟨state, stateEq⟩ : ∃ state, sourceServicePrefix? service.setup event.val
        execution.application.config = some state := by
      cases decoded : sourceServicePrefix? service.setup event.val execution.application.config
        with
      | none =>
          rw [show (service.setup.informationModel admission).infoOf who sourceHistory.trace =
            service.setup.protocolObserve who sourceHistory.state from
              service.setup.protocol_info admission who sourceHistory.trace, sourceState,
                decoded] at info
          cases info
      | some state => exact ⟨state, rfl⟩
    have stateRunning : ¬ ProtocolState.terminal service.setup.program state := by
      intro stopped
      apply running
      rw [sourceState, stateEq]
      exact stopped
    have stateView : ProtocolState.observe who service.setup.program state = sourceView := by
      rw [show (service.setup.informationModel admission).infoOf who sourceHistory.trace =
        service.setup.protocolObserve who sourceHistory.state from
          service.setup.protocol_info admission who sourceHistory.trace, sourceState,
            stateEq] at info
      exact Option.some.inj info
    have baselineValues : (baseline.map Subtype.val).map (OwnAction.binding who otherName payload) =
        values := by
      rw [Setup.toProtocolBehavioralPolicy_map_val]
      rw [← marginal state stateEq stateRunning, stateView]
      rfl
    have localLaw := approx.local_law_readout history.1 current phase history.2 law
    rw [localLaw, decodedEq, ← sourceState, alternativeLaw sourceHistory running active info,
      sourceState]
    simp only [anyStep, ↓reduceIte, PMF.pure_bind, PMF.map_bind, PMF.bind_map,
      sourceLaw, PMF.bind_bind]
    apply bind_congr_on_support _
    intro choice _
    have allowed := service.choice_allowed history.1 current history.2 choice
    rcases responses _ allowed with ⟨value, valueSupport, ⟨serial, submitted⟩, readout⟩ |
      ⟨transport, readout⟩
    · have found : ∃ value serial, choice.1.getD ⟨none⟩ = (runtime service.setup).reactiveBinding
          service.leaks who event payload value serial := ⟨value, serial, submitted⟩
      have decodedValue : submittedValue (choice.1.getD ⟨none⟩) = some value := by
        simp only [submittedValue, found, ↓reduceDIte]
        obtain ⟨_, chosen⟩ := found.choose_spec
        exact congrArg some (reactiveBinding_injective service.leaks who event payload
          (chosen.symm.trans submitted))
      have realizable : ∃ realized ∈ baseline.support,
          OwnAction.binding who otherName payload realized.1 = value := by
        rw [← baselineValues, PMF.support_map, PMF.support_map] at valueSupport
        obtain ⟨action, ⟨realized, realizedSupport, rfl⟩, same⟩ := valueSupport
        exact ⟨realized, realizedSupport, same⟩
      have realized : OwnAction.binding who otherName payload (realize value).1 = value := by
        simp only [realize, realizable, ↓reduceDIte]
        exact realizable.choose_spec.2
      rw [decodedValue, readout]
      simp only [PMF.pure_bind, realized]
      rfl
    · have decodedValue : submittedValue (choice.1.getD ⟨none⟩) = none := by
        simp only [submittedValue]
        split
        · rename_i found
          obtain ⟨value, serial, submitted⟩ := found
          rcases transport with silent | ⟨id, replayed⟩
          · rw [silent] at submitted
            cases submitted
          · rw [replayed] at submitted
            cases submitted
        · rfl
      rw [decodedValue, readout, ← baselineValues, PMF.bind_map, PMF.bind_map]
      rfl

end TimedApproximant

end Vegas
