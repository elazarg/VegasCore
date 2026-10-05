/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceForeignComparison
import Vegas.Game.SourceServiceEvidence
import Vegas.Game.SourceServiceDecisionResources
import Vegas.Pending.ReactiveResolutionWindowState
import GameTheoryExtensions.Math.Probability.Support

/-! # Foreign visits during a disclosure phase

At every retained decision of a disclosure phase the network is in a
`ResolutionWindowState`: all traffic published before the owner's opening, and
afterwards the opening is the one unpublished envelope in flight, possibly in
several copies. Once the opening is recorded, every
remaining response is transport and the pending opening alone settles the
event, so no current response of any player, the owner included, changes the
next-boundary configuration law, the distribution over configurations at the
next event boundary. Before the opening, a foreign response leaves
the application and the owner's recall unchanged; each timing slot the owner
still reaches settles the event with the source disclosure, and every other
slot leaves only silence. Hence every legal foreign response has the same
next-boundary configuration law, and the generic local comparison gives zero
gain for every belief.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A publication output has a resolution node. -/
theorem publication_nodeView (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload) :
    ∃ (owner : Player) (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
      (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve owner payload binding checks),
      nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq := by
  cases viewed : nodeView (graph setup) event with
  | sample otherPayload law kind code => cases kind.symm.trans outputEq
  | bind other otherPayload kind code => cases kind.symm.trans outputEq
  | resolve other otherPayload binding checks kind code =>
      have same := EventGraph.EventField.publication.inj (kind.symm.trans outputEq)
      subst same
      exact ⟨other, binding, checks, code, rfl⟩

/-- From any execution of a disclosure phase with all traffic published, a
fixed timing slot the owner still reaches in the remaining visits settles the
event with the source disclosure: the configuration at the next event boundary
is the source disclosure lottery, whatever the network traffic. -/
theorem reveal_slot_config_law (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program) {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution) {config : (graph setup).Config}
    (site : RevealSource setup wholeProfile event config)
    (sameConfig : execution.application.config = config)
    (unsent : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (effective : (site.residual site.owner).EffectiveDisclosures
      (.reveal site.published site.owner site.name site.fresh site.binding site.unresolved
        site.next) site.source.registry site.source.revelations)
    (ready : config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (entered ticks : Nat) (activated : execution.application.activatedAt event = some entered)
    (due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered)
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (visits : List Player) (slot : Fin ((rosters event).count site.owner))
    (notPassed : (execution.recall site.owner).length ≤
      rosterOffset setup rosters site.owner event + slot.val)
    (within : rosterOffset setup rosters site.owner event + slot.val <
      (execution.recall site.owner).length + visits.count site.owner) :
    ((runtime setup).runInteractionPlan leaks
      (Function.update (fun _ => (application setup leaks).silentPolicy) site.owner
        (sourceServiceTimedFamily setup leaks rosters wholeProfile site.owner event slot))
      network (visits.map ServiceInstruction.player ++
        (.includeLatest event site.owner :: List.replicate ticks .tick ++ [.expire event]))
      execution).map (fun final => final.application.config) =
      (revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
        PMF.pure (config.complete event ready
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
          (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
            (disclosureResult site.published site.binding site.source disclose))) := by
  subst sameConfig
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
        binding) outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  obtain ⟨visited, remaining, position, counted⟩ := split_owner_visit owner visits
    (rosterOffset setup rosters owner (embedding.event ⟨0, by simp [eventCount]⟩) + slot.val -
      (execution.recall owner).length) (by omega)
  have selected : rosterOffset setup rosters owner
      (embedding.event ⟨0, by simp [eventCount]⟩) + slot.val =
        (execution.recall owner).length + visited.count owner := by
    omega
  have law := sourceServiceTimedFamily_reveal_law setup leaks rosters fresh binding unresolved
    next wholeProfile residual refs source embedding refsBefore _ aligned execution agree history
    valid recalled origins effective network visits visited remaining slot position selected
    ready unsent
  have splitPlan : (visits.map ServiceInstruction.player ++
      (.includeLatest (embedding.event ⟨0, by simp [eventCount]⟩) owner ::
        List.replicate ticks .tick ++ [.expire (embedding.event ⟨0, by simp [eventCount]⟩)]) :
          List (ServiceInstruction (graph setup))) =
      (visits.map ServiceInstruction.player ++
        [.includeLatest (embedding.event ⟨0, by simp [eventCount]⟩) owner]) ++
        (List.replicate ticks .tick ++ [.expire (embedding.event ⟨0, by simp [eventCount]⟩)]) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [splitPlan, runInteractionPlan_append, law, PMF.bind_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro disclose supported
  have guarded := effective_reveal_supported fresh binding unresolved next residual source
    effective disclose supported
  let base := (execution.recall owner).length
  let visit : Fin (visits.count owner) :=
    ⟨rosterOffset setup rosters owner (embedding.event ⟨0, by simp [eventCount]⟩) + slot.val - base,
      by omega⟩
  let guardedPlayers := match (if disclose then rosterOpening? setup leaks owner
      (embedding.event ⟨0, by simp [eventCount]⟩)
        (execution.observe (application setup leaks) owner) else none) with
    | none => fun _ => (application setup leaks).silentPolicy
    | some (candidate, raw) =>
        (runtime setup).openingWindowPlayers leaks owner
          (embedding.event ⟨0, by simp [eventCount]⟩) candidate raw base (some visit)
  have playersEq : Function.update (fun _ => (application setup leaks).silentPolicy) owner
      ((application setup leaks).scheduledPolicy
        (rosterOffset setup rosters owner (embedding.event ⟨0, by simp [eventCount]⟩)) (some slot)
        (fun past view => match (if disclose then rosterOpening? setup leaks owner
          (embedding.event ⟨0, by simp [eventCount]⟩)
            (execution.observe (application setup leaks) owner) else none) with
          | none => (application setup leaks).silentPolicy past view
          | some (candidate, raw) => PMF.pure ((runtime setup).windowOpening leaks
              (embedding.event ⟨0, by simp [eventCount]⟩) candidate raw))
        (application setup leaks).silentPolicy) = guardedPlayers := by
    have firing : ∀ length : Nat, (some slot).map (fun selected =>
        rosterOffset setup rosters owner (embedding.event ⟨0, by simp [eventCount]⟩) +
          selected.val) = some length ↔
        (some visit).map (fun selected => base + selected.val) = some length := by
      intro length
      simp only [Option.map_some, Option.some.injEq, visit]
      omega
    dsimp only [guardedPlayers]
    split
    · funext who past view
      by_cases same : who = owner
      · subst same
        simp only [Function.update_self, ReactiveApplication.scheduledPolicy, ite_self]
      · simp only [Function.update_of_ne same]
    · funext who past view
      by_cases same : who = owner
      · subst same
        simp only [Function.update_self, ReactiveApplication.scheduledPolicy,
          openingWindowPlayers, ↓reduceIte, firing]
      · simp only [Function.update_of_ne same, openingWindowPlayers, same, ↓reduceIte]
  refine (map_congr_on_support _ (g := fun _ => _) ?_).trans (PMF.map_const _ _)
  intro final reached
  obtain ⟨current, prior, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [servicePlan_players_eq setup leaks _ guardedPlayers network _ (by simp)
    (by intro who; simp) current] at rest
  have prior : current ∈ ((runtime setup).runInteractionPlan leaks guardedPlayers network
      (visits.map ServiceInstruction.player ++
        [.includeLatest (embedding.event ⟨0, by simp [eventCount]⟩) owner])
        execution).support := by
    rw [← playersEq]
    exact prior
  apply guardedDisclosureWindow_config setup leaks publishedName binding source refs execution
    agree valid (embedding.event ⟨0, by simp [eventCount]⟩) outputEq codeEq node ready timely
    entered ticks activated due published serials network visits visit disclose guarded final
  rw [List.append_assoc (visits.map ServiceInstruction.player ++ [_]),
    runInteractionPlan_append, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨current, prior, rest⟩

variable [Fintype Player]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- Every retained decision of a disclosure phase, whoever acts, has the
window state of that phase, its activation time and deadline, and the
application invariants the opening window needs. -/
theorem disclosure_decision_resources {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {owner : Player} {payload : L.Ty}
    (owned : (graph service.setup).actor? phase.event = some owner)
    (isPublication : (graph service.setup).outputLayout phase.event = .publication payload) :
    ∃ entered : Nat,
      (runtime service.setup).ResolutionWindowState service.leaks owner phase.event
        execution.application execution ∧
      execution.application.activatedAt phase.event = some entered ∧
      (runtime service.setup).deadline phase.event ≤
        execution.application.clock + (phase.event.val + 1) - entered ∧
      execution.application.config.cut.Ready phase.event ∧
      execution.application.WithinDeadline (runtime service.setup) phase.event ∧
      execution.application.BindingInvariant ∧
      execution.InputRecall (application service.setup service.leaks) ∧
      (runtime service.setup).ResolutionEvidenceOrigins service.leaks execution := by
  obtain ⟨ready, timely, valid, recalled, _, _, _⟩ := sourceService_decision_resources
    service.setup service.leaks service.bounds service.values service.capacity service.rosters
    service.opportunities.binding service.network who ⟨remaining, some who, execution⟩ trace rfl
    phase.event phase.ready owner owned
  have origins := sourceService_resolutionEvidence service.setup service.leaks service.bounds
    service.rosters _ _ ⟨remaining, some who, execution⟩ trace
  obtain ⟨event, slot, _, _, _, _, _, _, _, _, _, _, _, _, _, _, phaseStart, prior, sample,
    boundary,
      turn, reached, _, sampled, _, publicEq, _, _⟩ :=
    sourceService_decision_boundary service.setup service.leaks service.bounds service.values
      service.capacity service.rosters service.opportunities.binding service.network
      (failureProfile service.setup.program) who ⟨remaining, some who, execution⟩ trace rfl
  have same : event = phase.event := phase.sole.2 event turn.1
  subst same
  obtain ⟨actor, binding, checks, codeEq, node⟩ :=
    publication_nodeView service.setup phase.event payload isPublication
  have actorEq : actor = owner := by
    have acts := congrArg EventGraph.EventCode.actor codeEq
    rw [EventGraph.EventCode.actor_cast isPublication
      ((graph service.setup).nodes phase.event)] at acts
    exact Option.some.inj (acts.symm.trans owned)
  subst actorEq
  have lawful : ∀ player past view response,
      response ∈ (service.menu.uniformResponses player past view).support →
        response ∈ service.bounds.compiledActions (runtime service.setup) service.leaks player
          past view := fun player past view response member =>
    sourceServiceMenu_in_compiled service.setup service.leaks service.bounds service.rosters
      player past view ((service.menu.uniformResponses_support player past view response).mp
        member)
  have initialState := EventGraphRuntime.ResolutionWindowState.initial (runtime service.setup)
    service.leaks actor phase.event phaseStart boundary.serials boundary.published
    (boundary.unsent actor phase.event le_rfl)
  have priorState := EventGraphRuntime.ResolutionWindowState.run (runtime service.setup)
    service.leaks service.bounds service.menu.uniformResponses lawful service.network actor
    phase.event payload binding checks isPublication codeEq node
    ((service.rosters phase.event).take slot) phaseStart prior initialState
    (by rw [← publicEq]; exact phase.sole) reached
  have state := priorState.learn (runtime service.setup) service.leaks who sample
  rw [← sampled] at state
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
    ((boundary.invariant.activated_iff phase.event).mpr
      ⟨boundary.ready phase.event rfl, by simp only [owned, Option.isSome_some]⟩)
  have earlier := boundary.invariant.activated_le phase.event entered activated
  have clock : execution.application.clock = phaseStart.application.clock :=
    congrArg PublicView.clock publicEq
  have activation : execution.application.activatedAt = phaseStart.application.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  refine ⟨entered, ⟨rfl, state.2⟩, by rw [activation]; exact activated, ?_, ready, timely, valid,
    recalled, origins⟩
  rw [clock]
  change phase.event.val + 1 ≤ phaseStart.application.clock + (phase.event.val + 1) - entered
  omega

end SourceServiceSpec

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

include approx in
/-- At a disclosure phase after the owner's opening is recorded, every legal
current response of any player, the owner included, leaves the same
configuration law at the next event boundary: only the pending opening can
settle the event. -/
theorem recorded_disclosure_phase_invariant {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {owner : Player} {payload : L.Ty}
    (owned : (graph service.setup).actor? phase.event = some owner)
    (isPublication : (graph service.setup).outputLayout phase.event = .publication payload)
    (recorded : (runtime service.setup).eventRecorded service.leaks (execution.recall owner)
      phase.event = true)
    (first second : (application service.setup service.leaks).Action)
    (firstAllowed : first ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (secondAllowed : second ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second := by
  obtain ⟨_, state, _⟩ := service.disclosure_decision_resources trace phase owned isPublication
  obtain ⟨message, authored, addressed, pending, unpublished, packets⟩ := state.2.2.2 recorded
  have transport (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)) :
      response = ⟨none⟩ := by
    have supported := service.menu.fullyMixed_response_support (initialLaw service.setup)
      service.planLength service.scheduler approx.players approx.covered approx.assessment
      approx.strategy approx.mixed who remaining execution trace response allowed
    exact sourceServiceTimedPolicy_recorded_transport service.setup service.leaks service.rosters
      approx.timing approx.profile phase.event owner owned execution phase.sole recorded
      execution rfl (List.Subset.refl _) who response supported
  have ending : rosterPhaseEnding service.setup phase.event =
      [.includeLatest phase.event owner] ++
        (List.replicate (phase.event.val + 1) .tick ++ [.expire phase.event]) := by
    simp only [rosterPhaseEnding, owned, List.append_assoc]
  have law (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)) :=
    sourceService_recorded_response_application_law service.setup service.leaks service.rosters
      approx.timing approx.profile service.network phase.event owner owned execution phase.sole
      recorded message authored addressed packets pending unpublished who response
      (transport response allowed) phase.visits (phase.event.val + 1)
  have applications := (law first firstAllowed).trans (law second secondAllowed).symm
  simp only [phaseConfigLaw, phaseLaw, DecisionPhase.tail, ending]
  simpa only [List.append_assoc, PMF.map_comp, Function.comp_def] using
    congrArg (PMF.map EventGraphRuntime.State.config) applications

/-- At a disclosure phase, every legal response of a player other than the
owner leaves the same configuration law at the next event boundary, whether or
not the owner has already submitted its opening. -/
theorem foreign_disclosure_phase_invariant {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {owner : Player} {payload : L.Ty} (foreign : who ≠ owner)
    (owned : (graph service.setup).actor? phase.event = some owner)
    (isPublication : (graph service.setup).outputLayout phase.event = .publication payload)
    (first second : (application service.setup service.leaks).Action)
    (firstAllowed : first ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (secondAllowed : second ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second := by
  by_cases recorded : (runtime service.setup).eventRecorded service.leaks
      (execution.recall owner) phase.event = true
  · exact approx.recorded_disclosure_phase_invariant trace phase owned isPublication recorded
      first second firstAllowed secondAllowed
  have unsent : (runtime service.setup).eventRecorded service.leaks
      (execution.recall owner) phase.event = false := Bool.eq_false_of_ne_true recorded
  obtain ⟨entered, state, activated, due, ready, timely, valid, recalled, origins⟩ :=
    service.disclosure_decision_resources trace phase owned isPublication
  have serials := state.2.1
  have published := state.2.2.1 unsent
  obtain ⟨site⟩ := service.exists_revealSource approx.profile trace phase isPublication
  have ownerEq : site.owner = owner := Option.some.inj (site.owned.symm.trans owned)
  subst ownerEq
  have effective := site.inherits approx.effective site.owner
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
    then (revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
      PMF.pure (execution.application.config.complete phase.event ready
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
        (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
          (disclosureResult site.published site.binding site.source disclose)))
    else ((runtime service.setup).runInteractionPlan service.leaks
      (fun _ => (application service.setup service.leaks).silentPolicy) service.network rest
        execution).map (fun final => final.application.config)
  let posterior := ((application service.setup service.leaks).policyMixture
    (approx.timing phase.event site.owner owned)
    (sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
      site.owner phase.event)).posterior (execution.recall site.owner)
  have law (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)) :
      approx.phaseConfigLaw phase response = posterior.bind target := by
    have transport := approx.foreign_response_transport trace owned foreign phase.sole
      response allowed
    have member := sourceServiceMenu_in_compiled service.setup service.leaks service.bounds
      service.rosters who _ _ allowed
    have preserved := (runtime service.setup).silent_response_preserves service.leaks _
      execution published who response transport
    have counters := (runtime service.setup).silent_response_preserves service.leaks _
      execution serials who response transport
    have sameRecall := (application service.setup service.leaks).respond_recall_other execution
      who site.owner (Ne.symm foreign) response
    have afterRecalled := (application service.setup service.leaks).respond_inputRecall execution
      who response recalled
    have afterOrigins := (runtime service.setup).resolutionEvidenceOrigins_respond service.leaks
      service.bounds execution recalled valid origins who response member
    set after := execution.respond (application service.setup service.leaks) who response
      with afterDef
    have sameApp : after.application = execution.application := preserved.1
    have afterSole : after.application.publicView.SoleReady phase.event := by
      rw [sameApp]
      exact phase.sole
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
          (Function.update (fun _ => (application service.setup service.leaks).silentPolicy)
            site.owner ((application service.setup service.leaks).policyMixture
              (approx.timing phase.event site.owner owned)
              (sourceServiceTimedFamily service.setup service.leaks service.rosters
                approx.profile site.owner phase.event)).policy)
          service.network (phase.visits.map ServiceInstruction.player ++
            .includeLatest phase.event site.owner :: rest) after := by
      rw [runInteractionPlan_append, runInteractionPlan_append,
        sourceServiceTimedPolicy_window_eq service.setup service.leaks service.rosters
          approx.timing approx.profile phase.event site.owner owned service.network phase.visits
          after afterSole]
      apply bind_congr_on_support _
      intro current _
      exact servicePlan_players_eq service.setup service.leaks _ _ service.network _
        (by simp [rest]) (by intro actor; simp [rest]) current
    have mixture := (runtime service.setup).runInteractionPlan_policyMixture service.leaks
      (approx.timing phase.event site.owner owned)
      (sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
        site.owner phase.event) site.owner
      (fun _ => (application service.setup service.leaks).silentPolicy) service.network
      (phase.visits.map ServiceInstruction.player ++
        .includeLatest phase.event site.owner :: rest) after
    dsimp only at mixture
    rw [sameRecall] at mixture
    unfold phaseConfigLaw phaseLaw DecisionPhase.tail
    rw [ending, mixed, ← mixture, PMF.map_bind]
    apply bind_congr_on_support _
    intro slot _
    by_cases inside : (execution.recall site.owner).length ≤ offset + slot.val ∧
        offset + slot.val < (execution.recall site.owner).length + phase.visits.count site.owner
    · dsimp only [target]
      simp only [inside.1, inside.2, and_self, ↓reduceIte]
      exact reveal_slot_config_law service.setup service.leaks service.rosters service.network
        approx.profile after site (by rw [sameApp])
        (by rw [sameRecall]; exact unsent) effective ready (by rw [sameApp]; exact timely)
        (by rw [sameApp]; exact valid) afterRecalled afterOrigins entered (phase.event.val + 1)
        (by rw [sameApp]; exact activated) (by rw [sameApp]; exact due) afterSerials
        afterPublished phase.visits slot (by rw [sameRecall]; exact inside.1)
        (by rw [sameRecall]; exact inside.2)
    · dsimp only [target]
      simp only [inside, ↓reduceIte]
      have separated : (after.recall site.owner).length + phase.visits.count site.owner ≤
          offset + slot.val ∨ offset + slot.val < (after.recall site.owner).length := by
        rw [sameRecall]
        omega
      have silentRun : (runtime service.setup).runInteractionPlan service.leaks
          (Function.update (fun _ => (application service.setup service.leaks).silentPolicy)
            site.owner (sourceServiceTimedFamily service.setup service.leaks service.rosters
              approx.profile site.owner phase.event slot)) service.network
          (phase.visits.map ServiceInstruction.player ++
            .includeLatest phase.event site.owner :: rest) after =
          (runtime service.setup).runInteractionPlan service.leaks
            (fun _ => (application service.setup service.leaks).silentPolicy) service.network
            (phase.visits.map ServiceInstruction.player ++
              .includeLatest phase.event site.owner :: rest) after := by
        rw [runInteractionPlan_append, runInteractionPlan_append]
        unfold sourceServiceTimedFamily
        rw [scheduled_window_waiting service.setup service.leaks service.network site.owner offset
          slot _ phase.visits after separated]
        apply bind_congr_on_support _
        intro current _
        exact servicePlan_players_eq service.setup service.leaks _ _ service.network _
          (by simp [rest]) (by intro actor; simp [rest]) current
      have applications := (silent_phase_application_law service.setup service.leaks
        service.network phase.event site.owner phase.visits rest passive after
          afterPublished).trans ((runtime service.setup).application_service_law service.leaks _
            service.network rest passive after execution sameApp)
      rw [silentRun]
      simpa only [PMF.map_comp, Function.comp_def] using
        congrArg (PMF.map EventGraphRuntime.State.config) applications
  rw [law first firstAllowed, law second secondAllowed]

open Classical in
/-- At a foreign player's information site during a disclosure phase, every
local lottery has the prescribed continuation law, for every belief over the
site. -/
theorem foreign_disclosure_comparison_eq (who : Player)
    (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId} {owner : Player} {payload : L.Ty}
    (foreign : who ≠ owner) (owned : (graph service.setup).actor? event = some owner)
    (isPublication : (graph service.setup).outputLayout event = .publication payload)
    (readyView : view.application.publicView.EventReady event)
    (law : PMF (service.model.Choice who site.1)) :
    let comparison := service.model.assessmentComparisonWith (service.model.truncatedRunner
        service.fuel) service.readout
      approx.assessment who (site, (approx.assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  apply approx.comparison_eq_of_phase_invariant who site
  intro history remaining execution current info phase first second firstAllowed secondAllowed
  have input := Option.some.inj
    ((service.infoOf_decision history current).symm.trans (info.trans observed))
  have readyNow :=
    (congrArg (fun pair : List (application service.setup service.leaks).PlayerEntry ×
      (application service.setup service.leaks).PlayerView =>
        pair.2.application.publicView.EventReady event) input).mpr readyView
  have same : phase.event = event := (phase.sole.2 event readyNow).symm
  subst same
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  exact approx.foreign_disclosure_phase_invariant trace phase foreign owned isPublication first
    second firstAllowed secondAllowed

open Classical in
/-- At an owner's information site after its opening is recorded, every local
lottery has the prescribed continuation law, for every belief over the site. -/
theorem recorded_disclosure_comparison_eq (who : Player)
    (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId} {payload : L.Ty}
    (owned : (graph service.setup).actor? event = some who)
    (isPublication : (graph service.setup).outputLayout event = .publication payload)
    (readyView : view.application.publicView.EventReady event)
    (recorded : (runtime service.setup).eventRecorded service.leaks past event = true)
    (law : PMF (service.model.Choice who site.1)) :
    let comparison := service.model.assessmentComparisonWith (service.model.truncatedRunner
        service.fuel) service.readout
      approx.assessment who (site, (approx.assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  apply approx.comparison_eq_of_phase_invariant who site
  intro history remaining execution current info phase first second firstAllowed secondAllowed
  have input := Option.some.inj
    ((service.infoOf_decision history current).symm.trans (info.trans observed))
  have readyNow :=
    (congrArg (fun pair : List (application service.setup service.leaks).PlayerEntry ×
      (application service.setup service.leaks).PlayerView =>
        pair.2.application.publicView.EventReady event) input).mpr readyView
  have same : phase.event = event := (phase.sole.2 event readyNow).symm
  subst same
  have ownRecall : execution.recall who = past := congrArg Prod.fst input
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  exact approx.recorded_disclosure_phase_invariant trace phase owned isPublication
    (ownRecall ▸ recorded) first second firstAllowed secondAllowed

end TimedApproximant

end Vegas
