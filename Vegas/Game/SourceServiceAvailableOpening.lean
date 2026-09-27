/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAbsentOpening
import Vegas.Game.SourceServiceUnsentBinding
import Vegas.Game.SourceServiceTimingPosterior

/-! # The owner's disclosure with an available opening

At an owner's visit to its own unsent disclosure whose authentic opening is
available, the timed compiler defers the source disclosure over the owner's
remaining roster visits. On the source side, the continuation from the event's
boundary draws the source disclosure and continues from the configuration that
completes the publication with it.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A window of a granted resolve phase under the uniform service menu after
which the owner's event is still unsent is a replay window: every response in
it is transport and lies in the support of the replay law. -/
theorem replay_window_of_unsent (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    {owner : Player} {event : (graph setup).EventId} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (visits : List Player) (initial final : (application setup leaks).Execution)
    (granted : initial.application.serviceGrant = some event)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (sourceServiceMenu setup leaks bounds rosters).uniformResponses network
        (visits.map ServiceInstruction.player) initial).support)
    (unsent : (runtime setup).eventRecorded leaks (final.recall owner) event = false) :
    final ∈ ((runtime setup).runInteractionPlan leaks
      (fun _ => (application setup leaks).replayPolicy) network
        (visits.map ServiceInstruction.player) initial).support := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  have owned : (graph setup).actor? event = some owner := by
    have acts := congrArg EventGraph.EventCode.actor codeEq
    rw [EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event)] at acts
    exact acts
  induction visits generalizing initial with
  | nil => exact reached
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map,
        FinDist.bind_bind] at reached ⊢
      obtain ⟨sample, sampleSupport, reached⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨response, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      let activated := initial.sampledActivation app actor sample
      have member := sourceServiceMenu_in_compiled setup leaks bounds rosters actor _ _
        ((menu.uniformResponses_support actor _ _ response).mp supported)
      have replayed : response ∈ (app.replayPolicy (activated.recall actor)
          (activated.observe app actor)).support := by
        rcases bounds.compiled_resolution_cases (runtime setup) leaks actor _ _ event owner
          payload binding checks outputEq codeEq node granted response member with silent |
            replay | ⟨candidate, value, evidence, acting, _, _, _, candidateOwned, _, shape⟩
        · rw [silent]
          exact app.replayPolicy_support _ _ none (Finset.mem_insert_self _ _)
        · exact replay
        · exfalso
          have equal : actor = owner := Option.some.inj (acting.symm.trans owned)
          clear candidateOwned
          subst equal
          subst shape
          have recorded := (runtime setup).eventRecorded_respond leaks activated actor
            ⟨some (.submit ⟨⟨.opening event candidate ⟨payload, value⟩, none⟩, evidence⟩)⟩ event rfl
          obtain ⟨entry, present, submitted⟩ :=
            ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
          obtain ⟨tail, same⟩ := (runtime setup).runInteractionPlan_recall_prefix leaks
            menu.uniformResponses network _ _ final reached actor
          have later : (runtime setup).eventRecorded leaks (final.recall actor) event = true :=
            ((runtime setup).eventRecorded_iff leaks _ event).mpr
              ⟨entry, same ▸ List.mem_append_left tail present, submitted⟩
          rw [later] at unsent
          cases unsent
      have transport := app.replayPolicy_cases _ _ response replayed
      have sameApp := ((runtime setup).replay_response_preserves leaks (fun _ => True) activated
        ⟨by simp, by simp, by simp, by simp⟩ actor response transport).1
      rw [FinDist.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨sample, sampleSupport, ?_⟩
      rw [FinDist.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨response, replayed,
        ih _ (by rw [sameApp]; exact granted) reached⟩

omit [Fintype Player] in
/-- With an available authentic opening, the source disclosure succeeds with
the opening's value. -/
theorem RevealSource.opening_success {setup : Setup (Player := Player) (L := L)}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {wholeProfile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution)
    (site : RevealSource setup wholeProfile event execution.application.config)
    (valid : execution.application.BindingInvariant)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks site.owner event
      (execution.observe (application setup leaks) site.owner) = some (candidate, raw)) :
    ∃ value, disclosureResult site.published site.binding site.source true = .success value ∧
      raw = ⟨site.payload, value⟩ ∧ candidate.1 = site.owner ∧
      execution.application.candidates.lookup candidate = .openable ⟨site.payload, value⟩ := by
  have outputEq := site.outputEq
  obtain ⟨Γ, names, publishedName, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, _⟩ := site
  dsimp only at *
  subst head
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) =
        .resolve owner payload (refs.get binding)
          (compileChecks (published := publishedName) refs source.registry
            source.revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) = _
    simpa [compileRankedNodes] using aligned.graphSuffix.nodeEq ⟨0, by simp [eventCount]⟩
  have node : nodeView (graph setup) (embedding.event ⟨0, by simp [eventCount]⟩) =
      .resolve owner payload (refs.get binding)
      (compileChecks (published := publishedName) refs source.registry source.revelations
        binding) outputEq codeEq := by
    cases viewed : nodeView (graph setup) (embedding.event ⟨0, by simp [eventCount]⟩) with
    | sample otherPayload law kind code => cases kind.symm.trans outputEq
    | bind other otherPayload kind code => cases kind.symm.trans outputEq
    | resolve other otherPayload otherBinding otherChecks kind code =>
        have samePayload := EventGraph.EventField.publication.inj (kind.symm.trans outputEq)
        subst otherPayload
        cases code.symm.trans codeEq
        rfl
  cases result : disclosureResult publishedName binding source true with
  | failure =>
      have absent := guarded_rosterOpening_failure setup leaks publishedName binding source refs
        execution agree _ outputEq codeEq node result
      rw [absent] at opening
      cases opening
  | success value =>
      obtain ⟨actual, _, owned, fixed, found⟩ := guarded_rosterOpening_success setup leaks
        publishedName binding source refs execution agree valid _ outputEq codeEq node value result
      rw [found] at opening
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opening)
      exact ⟨value, rfl, rfl, owned, fixed⟩

omit [Fintype Player] in
/-- After the owner's opening at a disclosure phase whose authentic opening is
available, the phase completes the publication with the successful source
disclosure, whatever the remaining traffic. -/
theorem RevealSource.opening_config_law (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (wholeProfile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks) {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution)
    (site : RevealSource setup wholeProfile event execution.application.config)
    (granted : execution.application.serviceGrant = some event)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (valid : execution.application.BindingInvariant)
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks site.owner event
      (execution.observe (application setup leaks) site.owner) = some (candidate, raw))
    (visits : List Player) (ticks : Nat) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
      (visits.map ServiceInstruction.player ++ [.includeLatest event site.owner] ++
        (List.replicate ticks .tick ++ [.expire event]))
      (execution.respond (application setup leaks) site.owner
        ((runtime setup).windowOpening leaks event candidate raw))).map
      (fun final => final.application.config) =
      FinDist.pure (execution.application.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) true)
        (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
          (disclosureResult site.published site.binding site.source true))) := by
  have outputEq := site.outputEq
  have owned := site.owned
  obtain ⟨Γ, names, publishedName, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, _⟩ := site
  dsimp only at *
  subst head
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) =
        .resolve owner payload (refs.get binding)
          (compileChecks (published := publishedName) refs source.registry
            source.revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) = _
    simpa [compileRankedNodes] using aligned.graphSuffix.nodeEq ⟨0, by simp [eventCount]⟩
  have node : nodeView (graph setup) (embedding.event ⟨0, by simp [eventCount]⟩) =
      .resolve owner payload (refs.get binding)
      (compileChecks (published := publishedName) refs source.registry source.revelations
        binding) outputEq codeEq := by
    cases viewed : nodeView (graph setup) (embedding.event ⟨0, by simp [eventCount]⟩) with
    | sample otherPayload law kind code => cases kind.symm.trans outputEq
    | bind other otherPayload kind code => cases kind.symm.trans outputEq
    | resolve other otherPayload otherBinding otherChecks kind code =>
        have samePayload := EventGraph.EventField.publication.inj (kind.symm.trans outputEq)
        subst otherPayload
        cases code.symm.trans codeEq
        rfl
  let app := application setup leaks
  cases result : disclosureResult publishedName binding source true with
  | failure =>
      have absent := guarded_rosterOpening_failure setup leaks publishedName binding source refs
        execution agree _ outputEq codeEq node result
      rw [absent] at opening
      cases opening
  | success value =>
      obtain ⟨actual, associated, candidateOwned, fixed, found⟩ := guarded_rosterOpening_success
        setup leaks publishedName binding source refs execution agree valid _ outputEq codeEq
        node value result
      rw [found] at opening
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opening)
      have resolved := compiled_disclosure_result (graph := graph setup) publishedName binding
        source refs execution.application.config.store agree true
      rw [result, EventGraph.EventCode.resolveOutput?_playerStore] at resolved
      have stored := EventGraph.EventCode.binding_success_of_resolve_success (graph := graph setup)
        (refs.get binding)
        (compileChecks (published := publishedName) refs source.registry source.revelations
          binding) true execution.application.config.store value resolved
      have accepted : app.handle execution.application
          ((runtime setup).windowEnvelope leaks owner
            (embedding.event ⟨0, by simp [eventCount]⟩) actual
            ⟨payload, value⟩ execution) =
            some (execution.application.complete (embedding.event ⟨0, by simp [eventCount]⟩) ready
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                (PublicationResult.success value))) :=
        handle_opening_eq (runtime setup) execution.application _ _ actual owner payload
          (refs.get binding) _ outputEq codeEq node ready timely rfl candidateOwned associated
          value fixed stored (.success value) resolved
      let packet : WitnessedPacket (graph setup) :=
        ⟨.opening (embedding.event ⟨0, by simp [eventCount]⟩) actual ⟨payload, value⟩,
          some ⟨actual, ⟨payload, value⟩⟩⟩
      have materialized := (runtime setup).windowOpening_packet leaks owner
        (embedding.event ⟨0, by simp [eventCount]⟩) actual ⟨payload, value⟩ execution.application
        (execution.network.known owner) candidateOwned fixed
      set after := execution.respond app owner
        ((runtime setup).windowOpening leaks (embedding.event ⟨0, by simp [eventCount]⟩) actual
          ⟨payload, value⟩) with afterDef
      have submitted : after.network = (execution.network.submit owner packet).2 := by
        change (execution.network.submit owner (app.packet execution.application owner
          (execution.network.known owner)
            (disclosureSubmission (.opening (embedding.event ⟨0, by simp [eventCount]⟩) actual
              ⟨payload, value⟩)))).2 = _
        rw [materialized]
      have recorded : (runtime setup).eventRecorded leaks (after.recall owner)
          (embedding.event ⟨0, by simp [eventCount]⟩) = true :=
        (runtime setup).eventRecorded_respond leaks execution owner _ _ rfl
      have law := sourceService_recorded_plan_application_law setup leaks rosters timing
        wholeProfile network _ owner owned after granted recorded
        ((runtime setup).windowEnvelope leaks owner
          (embedding.event ⟨0, by simp [eventCount]⟩) actual
          ⟨payload, value⟩ execution) rfl rfl
        (by
          rw [submitted]
          exact (published.mono fun _ member => Or.inl member).submit owner packet (Or.inr rfl))
        (by
          rw [submitted]
          exact List.mem_append_right _ (List.mem_singleton_self _))
        (by
          rw [submitted]
          exact serials.next_unpublished owner)
        visits ticks
      dsimp only at law
      have handled : (app.handle after.application
          ((runtime setup).windowEnvelope leaks owner
            (embedding.event ⟨0, by simp [eventCount]⟩) actual
            ⟨payload, value⟩ execution)).getD
            after.application =
          execution.application.complete (embedding.event ⟨0, by simp [eventCount]⟩) ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm)
              (PublicationResult.success value)) := by
        change (app.handle execution.application _).getD _ = _
        rw [accepted]
        rfl
      rw [handled] at law
      have settled : ¬ (execution.application.complete
          (embedding.event ⟨0, by simp [eventCount]⟩) ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.success value))).config.cut.Ready
              (embedding.event ⟨0, by simp [eventCount]⟩) := by
        intro unfinished
        exact unfinished.1 (Finset.mem_insert_self ..)
      obtain ⟨endpoint, expiry, endpointApp, _⟩ := (runtime setup).settled_reveal_expiry leaks
        (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
        { after with application := (execution.application.complete
          (embedding.event ⟨0, by simp [eventCount]⟩) ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.success value))) } _ settled ticks
      rw [expiry, FinDist.map_pure] at law
      have mapped := congrArg (FinDist.map EventGraphRuntime.State.config) law
      simp only [FinDist.map_comp, FinDist.map_pure, Function.comp_def] at mapped
      rw [mapped, endpointApp]
      rfl

omit [Fintype Player] in
/-- With all traffic published and every roster response a transport, a
disclosure phase ends by expiry: the publication is completed as withheld. -/
theorem withhold_phase_config (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    {owner : Player} {event : (graph setup).EventId} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (execution : (application setup leaks).Execution)
    (responses : ∀ (current : (application setup leaks).Execution) who response,
      current.application = execution.application →
      execution.recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (application setup leaks) who)).support →
      response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (ready : execution.application.config.cut.Ready event)
    (entered ticks : Nat) (activated : execution.application.activatedAt event = some entered)
    (due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered)
    (visits : List Player) :
    ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++
        .includeLatest event owner :: (List.replicate ticks .tick ++ [.expire event]))
      execution).map (fun final => final.application.config) =
      FinDist.pure (execution.application.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) PublicationResult.failure)) := by
  have passive : ∀ instruction ∈ (List.replicate ticks .tick ++ [.expire event] :
      List (ServiceInstruction (graph setup))), instruction ≠ .wire ∧
      (∀ player, instruction ≠ .player player) ∧
      ∀ selected player, instruction ≠ .includeLatest selected player := by
    intro instruction member
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at member
    rcases member with ⟨_, rfl⟩ | rfl <;> simp
  have applications := transport_phase_application_law setup leaks players network event owner
    visits _ passive execution responses published
  obtain ⟨next, expiry, nextApp, _⟩ := (runtime setup).canonical_silent_expiry leaks players
    network execution owner event payload binding checks outputEq codeEq node ready entered ticks
    activated due
  rw [expiry, FinDist.map_pure] at applications
  have mapped := congrArg (FinDist.map EventGraphRuntime.State.config) applications
  simp only [FinDist.map_comp, FinDist.map_pure, Function.comp_def] at mapped
  rw [mapped, nextApp]
  rfl

omit [Fintype Player] in
/-- With an available authentic opening and the disclosure unsent, the owner's
source opportunity draws the source disclosure and opens exactly when it
discloses. -/
theorem RevealSource.opportunity_law {setup : Setup (Player := Player) (L := L)}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {wholeProfile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution)
    (site : RevealSource setup wholeProfile event execution.application.config)
    (granted : execution.application.serviceGrant = some event)
    (unsent : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (effective : (site.residual site.owner).EffectiveDisclosures
      (.reveal site.published site.owner site.name site.fresh site.binding site.unresolved
        site.next) site.source.registry site.source.revelations)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks site.owner event
      (execution.observe (application setup leaks) site.owner) = some (candidate, raw)) :
    sourceServiceOpportunity setup leaks wholeProfile site.owner event
      (execution.recall site.owner) (execution.observe (application setup leaks) site.owner) =
      (revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
        if disclose then FinDist.pure ((runtime setup).windowOpening leaks event candidate raw)
        else (application setup leaks).replayPolicy (execution.recall site.owner)
          (execution.observe (application setup leaks) site.owner) := by
  obtain ⟨Γ, names, publishedName, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, _⟩ := site
  dsimp only at *
  subst head
  have law := sourceServiceOpportunity_reveal setup leaks fresh binding unresolved next
    wholeProfile residual refs source embedding refsBefore _ aligned execution agree history
    valid recalled origins effective granted unsent
  refine law.trans ?_
  apply FinDist.bind_congr
  intro disclose _
  cases disclose <;> simp only [Bool.false_eq_true, ↓reduceIte, opening]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- At every retained decision during a disclosure event's phase, the residual
source disclosure is aligned with the given profile, and three source facts
hold at the event's boundary. The source continuation draws the disclosure and
continues from the configuration that completes the publication with it. Any
owner action steps to the configuration completing the publication with that
action's disclosure. The owner's source action law has the disclosure lottery
as its disclosure marginal. The native completion with any disclosure decodes
to the source disclosure. While the owner's opening is available and unsent,
its timing posterior after its earlier visits of the phase keeps each earlier
slot with the source withholding probability. -/
theorem exists_revealSource_step (profile : BehavioralProfile service.setup.program)
    {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {payload : L.Ty}
    (isPublication : (graph service.setup).outputLayout phase.event = .publication payload) :
    ∃ site : RevealSource service.setup profile phase.event execution.application.config,
      (∀ disclose, decodeEventAction service.setup.program phase.event
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) =
          some (.reveal site.owner site.name disclose)) ∧
      (∀ (timing : FinDist (Fin ((service.rosters phase.event).count site.owner)))
        (candidate : Handle (graph service.setup)) (raw : Raw L),
        (∀ player, (profile player).EffectiveDisclosures service.setup.program []
          (Revelations.initial service.setup.context)) →
        rosterOpening? service.setup service.leaks site.owner phase.event
          (execution.observe (application service.setup service.leaks) site.owner) =
            some (candidate, raw) →
        (runtime service.setup).eventRecorded service.leaks (execution.recall site.owner)
          phase.event = false →
        (revealKernel site.residual (site.source.view site.owner)).prob true < 1 →
        ∀ slot, (((application service.setup service.leaks).policyMixture timing
          (sourceServiceTimedFamily service.setup service.leaks service.rosters profile
            site.owner phase.event)).posterior (execution.recall site.owner)).prob slot =
          timing.prob slot * (if slot.val <
              ((service.rosters phase.event).take phase.slot).count site.owner then
            1 - (revealKernel site.residual (site.source.view site.owner)).prob true else 1) /
            FinDist.deferredSurvival
              ((revealKernel site.residual (site.source.view site.owner)).prob true) timing
              (((service.rosters phase.event).take phase.slot).count site.owner)) ∧
      ∀ ready : execution.application.config.cut.Ready phase.event,
        (service.setup.continuationLaw profile
          (sourceServicePrefix? service.setup phase.event.val execution.application.config) =
        (revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
          service.setup.continuationLaw profile (sourceServicePrefix? service.setup
            (phase.event.val + 1) (execution.application.config.complete phase.event ready
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
              (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
                (disclosureResult site.published site.binding site.source disclose))))) ∧
        (∀ joint : Player → Option (OwnAction Player L),
          service.setup.protocolStep
            (sourceServicePrefix? service.setup phase.event.val execution.application.config)
            joint =
          FinDist.pure (sourceServicePrefix? service.setup (phase.event.val + 1)
            (execution.application.config.complete phase.event ready
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm)
                (OwnAction.disclosure (joint site.owner)))
              (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
                (disclosureResult site.published site.binding site.source
                  (OwnAction.disclosure (joint site.owner))))))) ∧
        ∀ state, sourceServicePrefix? service.setup phase.event.val
            execution.application.config = some state →
          ¬ ProtocolState.terminal service.setup.program state →
          ((profile site.owner).protocolAction service.setup.program
              (ProtocolState.observe site.owner service.setup.program state)).map
            OwnAction.disclosure =
          revealKernel site.residual (site.source.view site.owner) := by
  obtain ⟨phaseEvent, phaseSlot, phaseSelected, phasePosition, phaseGranted⟩ := phase
  dsimp only at isPublication ⊢
  obtain ⟨event, slot, _, _, _, Γ, names, remaining, remainingProfile, source, refs, embedding,
      refsBefore, aligned, _, ⟨_, inherits, lift, commutes, transport⟩, granted, prior, sample,
      boundary, grant, reachedPrior, _, sampled, _, publicEq, checkpoint, position,
      grantedOrigins⟩ :=
    sourceService_decision_boundary service.setup service.leaks service.bounds service.values
      service.capacity service.rosters service.opportunities.binding service.network profile
      who ⟨remaining, some who, execution⟩ trace rfl
  have same : event = phaseEvent := Option.some.inj
    (((congrArg PublicView.serviceGrant publicEq).trans grant).symm.trans phaseGranted)
  subst same
  have sameSlot : slot = phaseSlot := by
    have lengths := position.symm.trans phasePosition
    omega
  subst sameSlot
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
      have layout := embedding.layout_eq ⟨0, by simp [eventCount]⟩
      simp only [outputLayout, eventCount] at layout
      rw [headEq] at layout
      cases layout.symm.trans isPublication
  | @commit Γ names name owner sitePayload fresh guard next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have output : (graph service.setup).outputLayout event = .binding owner sitePayload := by
        rw [← headEq]
        change outputLayout service.setup.program (embedding.event _) = _
        simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
      cases output.symm.trans isPublication
  | @reveal Γ names published siteOwner name sitePayload fresh binding unresolved next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      subst headEq
      let site : RevealSource service.setup profile (embedding.event ⟨0, by simp [eventCount]⟩)
          execution.application.config :=
        ⟨Γ, names, published, siteOwner, name, sitePayload, fresh, binding, unresolved, next,
          remainingProfile, refs, source, embedding, refsBefore, aligned, checkpoint.agrees,
          checkpoint.history, rfl, inherits⟩
      have outputEq : (graph service.setup).outputLayout
          (embedding.event ⟨0, by simp [eventCount]⟩) = .publication sitePayload :=
        site.outputEq
      have decoded (disclose : Bool) :
          decodeEventAction service.setup.program (embedding.event ⟨0, by simp [eventCount]⟩)
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
              some (.reveal siteOwner name disclose) := by
        have action := aligned.actionEq ⟨0, by simp [eventCount]⟩
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        simpa [outputEq, decodeEventAction] using action
      refine ⟨site, decoded, ?_, fun ready => ?_⟩
      · intro timing candidate raw effective opening unsent small
        obtain ⟨actor, resolveBinding, checks, resolveCode, node⟩ :=
          publication_nodeView service.setup _ sitePayload outputEq
        have actorEq : actor = siteOwner := by
          have acts := congrArg EventGraph.EventCode.actor resolveCode
          rw [EventGraph.EventCode.actor_cast outputEq
            ((graph service.setup).nodes _)] at acts
          exact Option.some.inj (acts.symm.trans site.owned)
        subst actorEq
        have windowApp : prior.application = granted.application :=
          service.bounds.compiled_resolution_run_application (runtime service.setup)
            service.leaks service.menu.uniformResponses
            (fun player past view response supported => sourceServiceMenu_in_compiled
              service.setup service.leaks service.bounds service.rosters player past view
                ((service.menu.uniformResponses_support player past view response).mp
                  supported)) service.network _ _ actor sitePayload resolveBinding checks
            outputEq resolveCode node granted prior grant reachedPrior
        have executionEq : execution = prior.sampledActivation
            (application service.setup service.leaks) who sample := sampled
        have sameApp : execution.application = granted.application := by
          rw [executionEq]
          exact windowApp
        have sameRecall : execution.recall actor = prior.recall actor := by
          rw [executionEq]
          rfl
        have replayWindow := replay_window_of_unsent service.setup service.leaks service.bounds
          service.rosters service.network node _ granted prior grant reachedPrior
          (sameRecall ▸ unsent)
        have within : ((service.rosters (embedding.event ⟨0, by simp [eventCount]⟩)).take
            slot).count actor ≤
              (service.rosters (embedding.event ⟨0, by simp [eventCount]⟩)).count actor :=
          (List.take_sublist _ _).count_le _
        have posterior := sourceServiceTimedMixture_replay_window_posterior_initial service.setup
          service.leaks service.rosters fresh binding unresolved next profile remainingProfile
          refs source embedding refsBefore _ aligned granted boundary.toSourceCheckpoint.agrees
          boundary.toSourceCheckpoint.history boundary.binding boundary.recall grantedOrigins
          (inherits effective actor) service.network _ prior timing candidate raw
          ((rosterOpening?_application_eq service.setup service.leaks actor _ granted execution
            sameApp.symm).trans opening) grant (boundary.unsent actor _ le_rfl)
          (boundary.counts actor) within small replayWindow
        intro chosen
        rw [sameRecall]
        exact posterior chosen
      have now := transport 0 execution.application.config.store
        (decodeHistory service.setup.program (execution.application.config.history.map
          (service.setup.eventGraph.fromModeCompletion .sequential)))
      rw [checkpoint.decode _ embedding.ref] at now
      simp only [Nat.add_zero, Option.map_some] at now
      change sourceServicePrefix? service.setup _ execution.application.config = _ at now
      have later (disclose : Bool) :
          sourceServicePrefix? service.setup ((embedding.event ⟨0, by simp [eventCount]⟩).val + 1)
            (execution.application.config.complete (embedding.event ⟨0, by simp [eventCount]⟩)
              ready (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                (disclosureResult published binding source disclose))) =
          some (lift (Sum.inr (ProtocolState.entry next
            (revealSuccessor published binding source disclose)))) := by
        have completed := checkpoint.reveal published binding _ rfl ready outputEq
          (fun ref => refsBefore ref ⟨0, by simp [eventCount]⟩) disclose (decoded disclose)
        have recovered := completed.decode next (fun tail => embedding.ref tail.succ)
        change sourceServicePrefix? service.setup _
          (execution.application.complete (embedding.event ⟨0, by simp [eventCount]⟩) ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm)
              (disclosureResult published binding source disclose))).config = _
        unfold sourceServicePrefix?
        rw [transport 1, decodeSourcePrefix?_reveal]
        exact congrArg (fun decoded => (Option.map Sum.inr decoded).map lift) recovered
      refine ⟨?_, ?_, ?_⟩
      · rw [now]
        change ProtocolState.continuationLaw service.setup.program profile
          (lift (ProtocolState.entry _ source)) = _
        rw [← sourceStep_continuation, commutes.1]
        change (((ProtocolState.behavioralStateStep _ remainingProfile (.inl source)).map
          lift).bind _) = _
        rw [ProtocolState.behavioralStateStep_reveal_entry, FinDist.bind_map, FinDist.bind_map]
        apply FinDist.bind_congr
        intro disclose _
        rw [later disclose]
        rfl
      · intro joint
        rw [now, later]
        change ((ProtocolState.step _ (lift (ProtocolState.entry _ source)) joint).map some) = _
        rw [commutes.2.1]
        change ((FinDist.pure (Sum.inr (ProtocolState.entry next (revealSuccessor published
          binding source (OwnAction.disclosure (joint siteOwner)))))).map lift).map some = _
        simp only [FinDist.map_pure]
        rfl
      · intro state decodedState running
        rw [now] at decodedState
        have stateEq := Option.some.inj decodedState
        subst stateEq
        have viaResidual := commutes.1 (ProtocolState.entry _ source)
        change _ = ((ProtocolState.behavioralStateStep _ remainingProfile (.inl source)).map
          lift) at viaResidual
        rw [ProtocolState.behavioralStateStep_reveal_entry] at viaResidual
        let advance := fun disclose : Bool =>
          lift (Sum.inr (ProtocolState.entry next (revealSuccessor published binding source
            disclose)))
        have viaWhole : ProtocolState.behavioralStateStep service.setup.program profile
            (lift (ProtocolState.entry _ source)) =
            ((profile siteOwner).protocolAction service.setup.program
              (ProtocolState.observe siteOwner service.setup.program
                (lift (ProtocolState.entry _ source)))).map
              (fun action => advance (OwnAction.disclosure action)) := by
          unfold ProtocolState.behavioralStateStep
          simp only [running, ↓reduceIte]
          have stepped (joint : Player → Option (OwnAction Player L)) :
              ProtocolState.step service.setup.program (lift (ProtocolState.entry _ source))
                joint = FinDist.pure (advance (OwnAction.disclosure (joint siteOwner))) := by
            rw [commutes.2.1]
            change (FinDist.pure (Sum.inr (ProtocolState.entry next (revealSuccessor published
              binding source (OwnAction.disclosure (joint siteOwner)))))).map lift = _
            simp only [FinDist.map_pure]
            rfl
          rw [show ProtocolState.step service.setup.program (lift (ProtocolState.entry _ source)) =
            fun joint : Player → Option (OwnAction Player L) => FinDist.pure (advance
              (OwnAction.disclosure (joint siteOwner))) from funext stepped,
                ← FinDist.map_eq_bind]
          change (FinDist.pi _).map ((fun action => advance (OwnAction.disclosure action)) ∘
              fun joint : Player → Option (OwnAction Player L) => joint siteOwner) = _
          rw [← FinDist.map_comp, FinDist.map_apply_pi]
        have injective : Function.Injective advance := by
          intro first second same
          have successor := commutes.2.2 same
          have entries := (Sum.inr_injective successor)
          have configs := ProtocolState.entry_injective next entries
          have recalled := congrArg (fun config : Config Player L
            ((published, .publication sitePayload) :: Γ) =>
              (config.history siteOwner).getLast?) configs
          simpa [revealSuccessor] using recalled
        apply FinDist.map_injective injective
        rw [FinDist.map_comp]
        change ((profile siteOwner).protocolAction service.setup.program
          (ProtocolState.observe siteOwner service.setup.program
            (lift (ProtocolState.entry _ source)))).map
              (fun action => advance (OwnAction.disclosure action)) = _
        rw [← viaWhole, viaResidual, FinDist.map_comp]
        rfl

end SourceServiceSpec

/-- The acting player's earlier visits in the roster of its decision's event. -/
def DecisionPhase.earlier {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {who : Player}
    {execution : (application setup leaks).Execution}
    (phase : DecisionPhase setup leaks rosters who execution) : Nat :=
  ((rosters phase.event).take phase.slot).count who

/-- The source disclosure probability at a disclosure's source view. -/
def RevealSource.disclosureProbability {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    {config : (graph setup).Config} (site : RevealSource setup profile event config) : ℝ :=
  (revealKernel site.residual (site.source.view site.owner)).prob true

/-- The configuration completing the publication with a source disclosure. -/
def RevealSource.completion {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    {config : (graph setup).Config} (site : RevealSource setup profile event config)
    (ready : config.cut.Ready event) (disclose : Bool) : (graph setup).Config :=
  config.complete event ready
    (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
    (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
      (disclosureResult site.published site.binding site.source disclose))

omit [Fintype Player] in
/-- The source disclosure lottery, completed into configurations, averages the
two completions with the disclosure probability. -/
theorem RevealSource.completion_expect {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    {config : (graph setup).Config} (site : RevealSource setup profile event config)
    (ready : config.cut.Ready event) (utility : (graph setup).Config → ℝ) :
    ((revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
      FinDist.pure (site.completion ready disclose)).expect utility =
      site.disclosureProbability * utility (site.completion ready true) +
        (1 - site.disclosureProbability) * utility (site.completion ready false) := by
  have total := (revealKernel site.residual (site.source.view site.owner)).sum_prob
  simp only [Fintype.sum_bool] at total
  rw [FinDist.expect_bind, FinDist.expect_eq_sum, Fintype.sum_bool]
  simp only [FinDist.expect_pure, RevealSource.disclosureProbability]
  rw [show (revealKernel site.residual (site.source.view site.owner)).prob false =
    1 - (revealKernel site.residual (site.source.view site.owner)).prob true by linarith]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

/-- At the owner's unsent disclosure with an available opening, a current
transport response leaves the eventual disclosure probability deferred to the
owner's remaining visits: the next-boundary configuration completes the
publication with the disclosure, with the deferred remaining probability after
one more silent visit. -/
theorem available_transport_expect {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (site : RevealSource service.setup approx.profile phase.event execution.application.config)
    (ownerEq : site.owner = who)
    (owned : (graph service.setup).actor? phase.event = some who)
    (unsent : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
      phase.event = false)
    (ready : execution.application.config.cut.Ready phase.event)
    (candidate : Handle (graph service.setup)) (raw : Raw L)
    (opening : rosterOpening? service.setup service.leaks who phase.event
      (execution.observe (application service.setup service.leaks) who) = some (candidate, raw))
    (small : site.disclosureProbability < 1)
    (old : ∀ slot, (((application service.setup service.leaks).policyMixture
      (approx.timing phase.event who owned) (sourceServiceTimedFamily service.setup service.leaks
        service.rosters approx.profile who phase.event)).posterior (execution.recall who)).prob
          slot = (approx.timing phase.event who owned).prob slot *
            (if slot.val < phase.earlier then 1 - site.disclosureProbability else 1) /
              FinDist.deferredSurvival site.disclosureProbability
                (approx.timing phase.event who owned) phase.earlier)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (utility : (graph service.setup).Config → ℝ) :
    (approx.phaseConfigLaw phase response).expect utility =
      FinDist.deferredRemaining site.disclosureProbability (approx.timing phase.event who owned)
          (phase.earlier + 1) * utility (site.completion ready true) +
        (1 - FinDist.deferredRemaining site.disclosureProbability
          (approx.timing phase.event who owned) (phase.earlier + 1)) *
            utility (site.completion ready false) := by
  obtain ⟨Γ, names, publishedName, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, inherits⟩ := site
  dsimp only at ownerEq
  subst ownerEq
  let site : RevealSource service.setup approx.profile phase.event
      execution.application.config :=
    ⟨Γ, names, publishedName, owner, name, payload, fresh, binding, unresolved, next,
      residual, refs, source, embedding, refsBefore, aligned, agree, history, head, inherits⟩
  change (approx.phaseConfigLaw phase response).expect utility =
    FinDist.deferredRemaining site.disclosureProbability (approx.timing phase.event owner owned)
        (phase.earlier + 1) * utility (site.completion ready true) +
      (1 - FinDist.deferredRemaining site.disclosureProbability
        (approx.timing phase.event owner owned) (phase.earlier + 1)) *
          utility (site.completion ready false)
  let app := application service.setup service.leaks
  let q := site.disclosureProbability
  let timing := approx.timing phase.event owner owned
  have isPublication : (graph service.setup).outputLayout phase.event = .publication payload :=
    site.outputEq
  obtain ⟨actor, resolveBinding, checks, resolveCode, node⟩ :=
    publication_nodeView service.setup phase.event payload isPublication
  have actorEq : actor = owner := by
    have acts := congrArg EventGraph.EventCode.actor resolveCode
    rw [EventGraph.EventCode.actor_cast isPublication
      ((graph service.setup).nodes phase.event)] at acts
    exact Option.some.inj (acts.symm.trans owned)
  subst actorEq
  obtain ⟨entered, state, activated, due, _, timely, valid, recalled, origins⟩ :=
    service.disclosure_decision_resources trace phase owned isPublication
  have published := state.2.2.1 unsent
  have serials := state.2.1
  have counted := service.recall_count trace phase
  have visitsCount : phase.earlier + 1 + phase.visits.count actor =
      (service.rosters phase.event).count actor := by
    conv_rhs => rw [phase.roster_split]
    simp only [DecisionPhase.earlier, List.count_append, List.count_cons_self]
    omega
  have effective := inherits approx.effective actor
  have opportunity := RevealSource.opportunity_law service.leaks execution site phase.granted
    unsent valid recalled origins effective candidate raw opening
  let offset := rosterOffset service.setup service.rosters actor phase.event
  let family := sourceServiceTimedFamily service.setup service.leaks service.rosters
    approx.profile actor phase.event
  let mixtureImpl := app.policyMixture timing family
  let current : Fin ((service.rosters phase.event).count actor) :=
    ⟨phase.earlier, by omega⟩
  have firing : rosterOffset service.setup service.rosters actor phase.event + current.val =
      (execution.recall actor).length := by
    rw [counted]
    rfl
  have member := sourceServiceMenu_in_compiled service.setup service.leaks service.bounds
    service.rosters actor _ _ allowed
  have replaySupport : response ∈ (app.replayPolicy (execution.recall actor)
      (execution.observe app actor)).support := by
    rcases service.bounds.compiled_resolution_cases (runtime service.setup) service.leaks actor
      _ _ phase.event actor payload resolveBinding checks isPublication resolveCode node
      phase.granted response member with silent | replay | ⟨_, _, _, _, _, _, _, _, _, shape⟩
    · rw [silent]
      exact app.replayPolicy_support _ _ none (Finset.mem_insert_self _ _)
    · exact replay
    · rcases transport with silent | ⟨id, replayed⟩
      · rw [silent] at shape
        cases shape
      · rw [replayed] at shape
        cases shape
  obtain ⟨entry, entryRecall, entryView, entryAction⟩ :=
    (runtime service.setup).response_recall_entry service.leaks execution actor response
  have likelihood (slot : Fin ((service.rosters phase.event).count actor)) :
      (family slot (execution.recall actor) entry.beforeView).prob entry.action =
        (if slot = current then 1 - q else 1) *
          (app.replayPolicy (execution.recall actor) entry.beforeView).prob entry.action := by
    rw [entryView, entryAction]
    by_cases same : slot = current
    · subst same
      have fires : family current (execution.recall actor) (execution.observe app actor) =
          sourceServiceOpportunity service.setup service.leaks approx.profile actor phase.event
            (execution.recall actor) (execution.observe app actor) := by
        simp only [family, sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
          Option.map_some, firing, ↓reduceIte]
      have different : response ≠ (runtime service.setup).windowOpening service.leaks
          phase.event candidate raw := by
        rcases transport with rfl | ⟨id, rfl⟩ <;> simp [windowOpening]
      rw [fires, opportunity, FinDist.bind_bool_mix, FinDist.prob_mix,
        FinDist.prob_pure_of_ne different]
      simp only [↓reduceIte, mul_zero, zero_add]
      rfl
    · have waiting : ¬ rosterOffset service.setup service.rosters actor phase.event + slot.val =
          (execution.recall actor).length := by
        intro now
        apply same
        apply Fin.ext
        change slot.val = phase.earlier
        rw [counted] at now
        change rosterOffset service.setup service.rosters actor phase.event + slot.val =
          rosterOffset service.setup service.rosters actor phase.event + phase.earlier at now
        omega
      simp only [family, sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
        Option.map_some, Option.some.injEq, waiting, ↓reduceIte, same, one_mul]
      rfl
  have possible : entry.action ∈
      (app.replayPolicy (execution.recall actor) entry.beforeView).support := by
    rw [entryAction, entryView]
    exact replaySupport
  have updated := app.scheduledChoice_posterior_step timing family q (FinDist.prob_nonneg _ _)
    small (execution.recall actor) entry current
    (app.replayPolicy (execution.recall actor) entry.beforeView) possible likelihood old
  have remainingMass := ReactiveApplication.scheduledChoice_remaining_probability timing
    (mixtureImpl.posterior (execution.recall actor ++ [entry])) q (phase.earlier + 1) updated
  have preserved := (runtime service.setup).replay_response_preserves service.leaks _
    execution published actor response transport
  have counters := (runtime service.setup).replay_response_preserves service.leaks _
    execution serials actor response transport
  have afterUnsent := (runtime service.setup).eventRecorded_respond_transport service.leaks
    execution actor actor response transport phase.event
  have afterRecalled := app.respond_inputRecall execution actor response recalled
  have afterOrigins := origins_replayed service.setup service.leaks execution origins actor
    response transport
  have grant : PublicView.serviceGrant
      (execution.observe (application service.setup service.leaks) actor).application.publicView =
        some phase.event := phase.granted
  set after := execution.respond app actor response with afterDef
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
  have afterLength : (after.recall actor).length = offset + phase.earlier + 1 := by
    rw [afterDef, entryRecall, List.length_append, counted]
    rfl
  let rest : List (ServiceInstruction (graph service.setup)) :=
    List.replicate (phase.event.val + 1) .tick ++ [.expire phase.event]
  have ending : rosterPhaseEnding service.setup phase.event =
      .includeLatest phase.event actor :: rest := by
    simp only [rosterPhaseEnding, owned, rest, List.cons_append, List.nil_append]
  have mixed : (runtime service.setup).runInteractionPlan service.leaks approx.players
      service.network (phase.visits.map ServiceInstruction.player ++
        .includeLatest phase.event actor :: rest) after =
      (runtime service.setup).runInteractionPlan service.leaks
        (Function.update (fun _ => app.replayPolicy) actor mixtureImpl.policy)
        service.network (phase.visits.map ServiceInstruction.player ++
          .includeLatest phase.event actor :: rest) after := by
    rw [runInteractionPlan_append, runInteractionPlan_append,
      sourceServiceTimedPolicy_window_eq service.setup service.leaks service.rosters
        approx.timing approx.profile phase.event actor owned service.network phase.visits
        after afterGrant]
    apply FinDist.bind_congr
    intro current _
    exact servicePlan_players_eq service.setup service.leaks _ _ service.network _
      (by simp [rest]) (by intro player; simp [rest]) current
  have mixture := (runtime service.setup).runInteractionPlan_policyMixture service.leaks
    timing family actor (fun _ => app.replayPolicy) service.network
    (phase.visits.map ServiceInstruction.player ++ .includeLatest phase.event actor :: rest) after
  dsimp only at mixture
  have slotLaw (slot : Fin ((service.rosters phase.event).count actor)) :
      ((runtime service.setup).runInteractionPlan service.leaks
        (Function.update (fun _ => app.replayPolicy) actor (family slot)) service.network
        (phase.visits.map ServiceInstruction.player ++ .includeLatest phase.event actor :: rest)
        after).map (fun final => final.application.config) =
        if phase.earlier + 1 ≤ slot.val then
          (revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
            FinDist.pure (site.completion ready disclose)
        else FinDist.pure (site.completion ready false) := by
    by_cases future : phase.earlier + 1 ≤ slot.val
    · simp only [future, ↓reduceIte]
      exact reveal_slot_config_law service.setup service.leaks service.rosters service.network
        approx.profile after site (by rw [sameApp]) afterGrant
        (afterUnsent.trans unsent) effective ready (by rw [sameApp]; exact timely)
        (by rw [sameApp]; exact valid) afterRecalled afterOrigins entered (phase.event.val + 1)
        (by rw [sameApp]; exact activated) (by rw [sameApp]; exact due) afterSerials
        afterPublished phase.visits slot
        (by rw [afterLength]; change offset + phase.earlier + 1 ≤ offset + slot.val; omega)
        (by
          rw [afterLength]
          have bound := slot.isLt
          change offset + slot.val < offset + phase.earlier + 1 + phase.visits.count actor
          omega)
    · simp only [future, ↓reduceIte]
      have separated : (after.recall actor).length + phase.visits.count actor ≤
          offset + slot.val ∨ offset + slot.val < (after.recall actor).length := by
        rw [afterLength]
        omega
      have replayed : (runtime service.setup).runInteractionPlan service.leaks
          (Function.update (fun _ => app.replayPolicy) actor (family slot)) service.network
          (phase.visits.map ServiceInstruction.player ++
            .includeLatest phase.event actor :: rest) after =
          (runtime service.setup).runInteractionPlan service.leaks
            (fun _ => app.replayPolicy) service.network
            (phase.visits.map ServiceInstruction.player ++
              .includeLatest phase.event actor :: rest) after := by
        rw [runInteractionPlan_append, runInteractionPlan_append]
        unfold family sourceServiceTimedFamily
        rw [scheduled_window_waiting service.setup service.leaks service.network actor offset
          slot _ phase.visits after separated]
        apply FinDist.bind_congr
        intro current _
        exact servicePlan_players_eq service.setup service.leaks _ _ service.network _
          (by simp [rest]) (by intro player; simp [rest]) current
      rw [replayed, withhold_phase_config service.setup service.leaks _ service.network node
        after (fun _ _ action _ _ supported => app.replayPolicy_cases _ _ action supported)
        afterPublished (by rw [sameApp]; exact ready) entered (phase.event.val + 1)
        (by rw [sameApp]; exact activated) (by rw [sameApp]; exact due) phase.visits]
      simp only [RevealSource.completion, disclosureResult_false, sameApp]
  have posteriorEq : mixtureImpl.posterior (after.recall actor) =
      mixtureImpl.posterior (execution.recall actor ++ [entry]) := by
    rw [afterDef, entryRecall]
  unfold phaseConfigLaw phaseLaw DecisionPhase.tail
  rw [ending, mixed, ← mixture, FinDist.map_bind, FinDist.expect_bind]
  change (mixtureImpl.posterior (after.recall actor)).expect _ = _
  rw [posteriorEq]
  calc
    _ = (mixtureImpl.posterior (execution.recall actor ++ [entry])).expect (fun slot =>
        utility (site.completion ready false) +
          q * (utility (site.completion ready true) - utility (site.completion ready false)) *
            (if slot ∈ {slot : Fin ((service.rosters phase.event).count actor) |
              phase.earlier + 1 ≤ slot.val} then 1 else 0)) := by
      apply FinDist.expect_congr
      intro slot _
      rw [slotLaw slot]
      by_cases future : phase.earlier + 1 ≤ slot.val
      · simp only [future, ↓reduceIte, Set.mem_ofPred_eq]
        rw [site.completion_expect ready utility]
        change q * _ + (1 - q) * _ = _
        ring
      · simp only [future, ↓reduceIte, Set.mem_ofPred_eq, FinDist.expect_pure]
        ring
    _ = utility (site.completion ready false) +
        q * (utility (site.completion ready true) - utility (site.completion ready false)) *
          (mixtureImpl.posterior (execution.recall actor ++ [entry])).probOf
            {slot | phase.earlier + 1 ≤ slot.val} := by
      rw [FinDist.expect_add, FinDist.expect_const, FinDist.expect_smul,
        FinDist.expect_indicator_eq_probOf]
    _ = _ := by
      rw [← remainingMass]
      ring

end TimedApproximant

end Vegas.SourceProgram.RevealService
