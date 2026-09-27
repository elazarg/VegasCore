/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOwnerComparison
import Vegas.Game.SourceServiceBindingContinuation
import Vegas.Game.SourceServiceBindingSource
import Vegas.Game.SourceServiceForeignComparison
import Vegas.Pending.ReactiveResolutionWindowState

/-! # The owner's unsent binding

At an owner's visit to its own unsent binding, the timed compiler draws the
source value, then the timing slot, then the current response: a submission of
that value at the chosen slot, and a replay otherwise. A current submission
fixes the source value. A current transport response leaves the source value
law unchanged, because value and timing are independent and a transport
response reveals only that the current slot was not chosen.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

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
      boundary, grant, reached, _, sampled, _, publicEq, _, position⟩ :=
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
    apply FinDist.map_congr_of_eq_on_support
    intro choice _
    exact serviceDecision_binding_fresh (runtime setup) leaks execution owner _ payload
      outputEq codeEq node serial freshSlot candidate choice
  simp only [sourceServiceOpportunity, unsent, Bool.false_eq_true, ↓reduceIte]
  rw [responses, FinDist.bind_map, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro choice _
  cases choice <;> rfl

omit [Fintype Player] in
private theorem condOnFibre_support {α β : Type*} {μ : FinDist α} {f : α → β} {b : β}
    (meets : ∃ a ∈ f ⁻¹' {b}, a ∈ μ.support) {a : α}
    (member : a ∈ (μ.condOnFibre f b).support) : f a = b ∧ a ∈ μ.support := by
  rw [FinDist.condOnFibre, dite_eq_left meets] at member
  exact FinDist.support_condOn μ _ meets member

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
        FinDist.pure (execution.application.config.complete phase.event ready
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
      FinDist.pure (execution.application.config.complete phase.event ready
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
  rw [policyEq, ReactiveApplication.Implementation.policy_eq, FinDist.support_map] at present
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
    apply FinDist.bind_congr
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
    rw [afterDef, ReactiveApplication.Implementation.posterior_respond, FinDist.support_map]
      at member
    obtain ⟨pair, conditioned, rfl⟩ := member
    obtain ⟨matched, supported⟩ := condOnFibre_support meets conditioned
    obtain ⟨memory, memorySupport, drawn⟩ :=
      Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
    obtain ⟨action, actionSupport, rfl⟩ := FinDist.support_map .. ▸ drawn
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
      rw [fires, opening, FinDist.support_map] at actionSupport
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
  rw [ending, mixed, ← mixture, FinDist.map_bind]
  calc
    _ = (mixtureImpl.posterior (after.recall owner)).bind fun _ =>
        (commitKernel site.residual (site.source.view owner)).bind fun choice =>
          FinDist.pure (execution.application.config.complete phase.event ready
            (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) choice)
            (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) choice)) := by
      apply FinDist.bind_congr
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
    _ = _ := FinDist.bind_const _ _

end TimedApproximant

omit [Fintype Player] in
/-- A binding submission determines its source value. -/
theorem reactiveBinding_injective {setup : Setup (Player := Player) (L := L)}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty) (serial : Nat)
    {first second : PublicationResult (L.Val payload)}
    (same : (runtime setup).reactiveBinding leaks owner event payload first serial =
      (runtime setup).reactiveBinding leaks owner event payload second serial) :
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
    (timing : ∀ event who, (graph service.setup).actor? event = some who →
      FinDist (Fin ((service.rosters event).count who)))
    (timingFull : ∀ event who owned, (timing event who owned).FullSupport)
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
    ReactiveApplication.policyMixture_policy, FinDist.support_bind] at present
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
  rw [opening, FinDist.support_map] at drawn
  obtain ⟨value, valueSupport, valueEq⟩ := drawn
  have sameValue := reactiveBinding_injective service.leaks siteOwner _ payload serial valueEq
  subst sameValue
  refine (FinDist.bind_congr (g := fun _ => _) ?_).trans (FinDist.bind_const _ _)
  intro tag member
  obtain ⟨matched, supported⟩ := condOnFibre_support ⟨(value, slot, response), rfl, by
    rw [FinDist.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨value, valueSupport, ?_⟩
    rw [FinDist.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨slot, slotSupport, ?_⟩
    simp only [ReactiveApplication.scheduledPolicy, Option.map_some, now, ↓reduceIte,
      FinDist.map_pure, FinDist.mem_support_pure]
    rfl⟩ member
  obtain ⟨tagValue, _, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨tagSlot, _, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rest)
  obtain ⟨action, actionSupport, rfl⟩ := FinDist.support_map .. ▸ rest
  have actionEq : action = response := Option.some.inj matched
  by_cases fires : rosterOffset service.setup service.rosters siteOwner
      (embedding.event ⟨0, by simp [eventCount]⟩) + tagSlot.val =
        (execution.recall siteOwner).length
  · simp only [ReactiveApplication.scheduledPolicy, Option.map_some, fires, ↓reduceIte,
      FinDist.mem_support_pure] at actionSupport
    rw [actionSupport] at actionEq
    have tagValueEq := reactiveBinding_injective service.leaks siteOwner _ payload serial actionEq
    subst tagValueEq
    rfl
  · simp only [ReactiveApplication.scheduledPolicy, Option.map_some, Option.some.injEq, fires,
      ↓reduceIte] at actionSupport
    exact (submitted action actionSupport actionEq).elim


end Vegas.SourceProgram.RevealService
