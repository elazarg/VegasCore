/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceForeignDisclosure

/-! # The owner's disclosure without an available opening

When the owner's view carries no authentic opening of its commitment, the
resolution menu offers it no submission, and the timed compiler, at every point
of the phase, responds only by transport: the source disclosure, if any, is
realized as silence. The application stays fixed and all traffic stays
published, so every legal current response of the owner leaves the same
configuration law at the next event boundary, and the generic local comparison
gives zero gain for every belief.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Whether a view carries an authentic opening depends only on its
application part. -/
theorem rosterOpening_congr (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (event : (graph setup).EventId)
    {view other : (application setup leaks).PlayerView}
    (same : view.application = other.application) :
    rosterOpening? setup leaks who event view = rosterOpening? setup leaks who event other := by
  unfold rosterOpening?
  rw [same]

/-- A view without an authentic opening admits no resolution submission. -/
theorem rosterOpening_none_no_opening (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {who actor : Player} {event : (graph setup).EventId} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding actor payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve actor payload binding checks}
    (node : nodeView (graph setup) event = .resolve actor payload binding checks outputEq codeEq)
    (view : (application setup leaks).PlayerView)
    (absent : rosterOpening? setup leaks who event view = none)
    (candidate : Handle (graph setup)) (value : L.Val payload)
    (result : EventGraph.EventCode.resolveOutput? binding checks true
      view.application.observation.store = some (.success value))
    (associated : view.application.publicView.accepted binding.field = some candidate)
    (owned : candidate.1 = who) : False := by
  unfold rosterOpening? at absent
  rw [node] at absent
  simp [result, associated, owned] at absent

/-- At any point of a disclosure phase whose owner has no authentic opening,
the timed compiler responds only by transport, for every player. -/
theorem sourceServiceTimedPolicy_absent_transport (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    {actor : Player} {event : (graph setup).EventId} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding actor payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve actor payload binding checks}
    (node : nodeView (graph setup) event = .resolve actor payload binding checks outputEq codeEq)
    (current : (application setup leaks).Execution)
    (granted : current.application.serviceGrant = some event)
    (absent : rosterOpening? setup leaks actor event
      (current.observe (application setup leaks) actor) = none)
    (who : Player) (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServiceTimedPolicy setup leaks rosters timing profile who
      (current.recall who) (current.observe (application setup leaks) who)).support) :
    response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ := by
  let app := application setup leaks
  have grant : PublicView.serviceGrant
      (current.observe (application setup leaks) who).application.publicView = some event :=
    granted
  have actorOwned : (graph setup).actor? event = some actor := by
    have acts := congrArg EventGraph.EventCode.actor codeEq
    rw [EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event)] at acts
    exact acts
  by_cases acts : (graph setup).actor? event = some who
  · have same : actor = who := Option.some.inj (actorOwned.symm.trans acts)
    subst same
    simp only [sourceServiceTimedPolicy, grant, acts, ↓reduceDIte,
      ReactiveApplication.policyMixture_policy, FinDist.support_bind] at supported
    obtain ⟨slot, _, drawn⟩ := Set.mem_iUnion₂.mp supported
    unfold sourceServiceTimedFamily ReactiveApplication.scheduledPolicy at drawn
    split at drawn
    · unfold sourceServiceOpportunity at drawn
      split at drawn
      · exact app.replayPolicy_cases _ _ response drawn
      · rw [sourceServicePolicy_at_event setup leaks profile actor current event granted acts,
          FinDist.bind_map, FinDist.support_bind] at drawn
        obtain ⟨action, _, drawn⟩ := Set.mem_iUnion₂.mp drawn
        rcases (runtime setup).serviceDecision_resolution_cases leaks actor (current.recall actor)
          (current.observe (application setup leaks) actor) event actor payload binding checks
          outputEq codeEq node
          (cast (congrArg EventGraph.EventField.Action outputEq) action) with silent |
            ⟨candidate, value, evidence, result, associated, owned, _⟩
        · simp only [cast_cast, cast_eq] at silent
          simp only [silent, ↓reduceIte] at drawn
          exact app.replayPolicy_cases _ _ response drawn
        · exact (rosterOpening_none_no_opening setup leaks node _ absent candidate value result
            associated owned).elim
    · exact app.replayPolicy_cases _ _ response drawn
  · simp only [sourceServiceTimedPolicy, grant, dite_eq_right acts] at supported
    exact app.replayPolicy_cases _ _ response supported

variable [Fintype Player]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

include approx in
/-- At the owner's disclosure without an available opening, every legal current
response of the owner leaves the same configuration law at the next event
boundary. -/
theorem absent_opening_phase_invariant {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {payload : L.Ty}
    (owned : (graph service.setup).actor? phase.event = some who)
    (isPublication : (graph service.setup).outputLayout phase.event = .publication payload)
    (unsent : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
      phase.event = false)
    (absent : rosterOpening? service.setup service.leaks who phase.event
      (execution.observe (application service.setup service.leaks) who) = none)
    (first second : (application service.setup service.leaks).Action)
    (firstAllowed : first ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (secondAllowed : second ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second := by
  let app := application service.setup service.leaks
  obtain ⟨actor, binding, checks, codeEq, node⟩ :=
    publication_nodeView service.setup phase.event payload isPublication
  have actorEq : actor = who := by
    have acts := congrArg EventGraph.EventCode.actor codeEq
    rw [EventGraph.EventCode.actor_cast isPublication
      ((graph service.setup).nodes phase.event)] at acts
    exact Option.some.inj (acts.symm.trans owned)
  subst actorEq
  obtain ⟨_, state, _⟩ := service.disclosure_decision_resources trace phase owned isPublication
  have published := state.2.2.1 unsent
  let rest : List (ServiceInstruction (graph service.setup)) :=
    List.replicate (phase.event.val + 1) .tick ++ [.expire phase.event]
  have passive : ∀ instruction ∈ rest, instruction ≠ .wire ∧
      (∀ player, instruction ≠ .player player) ∧
      ∀ selected player, instruction ≠ .includeLatest selected player := by
    intro instruction member
    simp only [rest, List.mem_append, List.mem_replicate, List.mem_singleton] at member
    rcases member with ⟨_, rfl⟩ | rfl <;> simp
  have ending : rosterPhaseEnding service.setup phase.event =
      .includeLatest phase.event actor :: rest := by
    simp only [rosterPhaseEnding, owned, rest, List.cons_append, List.nil_append]
  have law (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions actor (execution.recall actor)
        (execution.observe app actor)) :
      approx.phaseConfigLaw phase response =
        ((runtime service.setup).runInteractionPlan service.leaks approx.players
          service.network rest execution).map (fun final => final.application.config) := by
    have member := sourceServiceMenu_in_compiled service.setup service.leaks service.bounds
      service.rosters actor _ _ allowed
    have transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ := by
      rcases service.bounds.compiled_resolution_cases (runtime service.setup) service.leaks actor
        _ _ phase.event actor payload binding checks isPublication codeEq node phase.granted
        response member with silent | replay | ⟨candidate, value, _, _, _, result, associated,
          candidateOwned, _, _⟩
      · exact Or.inl silent
      · exact app.replayPolicy_cases _ _ response replay
      · exact (rosterOpening_none_no_opening service.setup service.leaks node _ absent candidate
          value result associated candidateOwned).elim
    have preserved := (runtime service.setup).replay_response_preserves service.leaks _
      execution published actor response transport
    set after := execution.respond app actor response with afterDef
    have sameApp : after.application = execution.application := preserved.1
    have afterPublished : after.network.Satisfies fun message =>
        message.id ∈ after.network.ledger.map Message.id := by
      rw [preserved.2.1]
      exact preserved.2.2.2.2.1
    have responses (current : (application service.setup service.leaks).Execution)
        (player : Player) (action : (application service.setup service.leaks).Action)
        (currentApp : current.application = after.application) (_ : after.recall actor ⊆
          current.recall actor)
        (supported : action ∈ (approx.players player (current.recall player)
          (current.observe app player)).support) :
        action = ⟨none⟩ ∨ ∃ id, action = ⟨some (.replay id)⟩ :=
      sourceServiceTimedPolicy_absent_transport service.setup service.leaks service.rosters
        approx.timing approx.profile node current
        (by rw [currentApp, sameApp]; exact phase.granted)
        ((rosterOpening_congr service.setup service.leaks actor phase.event
          (by change app.observePlayer current.application actor =
                app.observePlayer execution.application actor
              rw [currentApp, sameApp])).trans absent)
        player action supported
    have applications := (transport_phase_application_law service.setup service.leaks
      approx.players service.network phase.event actor phase.visits rest passive after responses
        afterPublished).trans ((runtime service.setup).application_service_law service.leaks _
          service.network rest passive after execution sameApp)
    unfold phaseConfigLaw phaseLaw DecisionPhase.tail
    rw [ending]
    simpa only [FinDist.map_comp, Function.comp_def] using
      congrArg (FinDist.map EventGraphRuntime.State.config) applications
  rw [law first firstAllowed, law second secondAllowed]

open Classical in
/-- At an owner's information site of its unsent disclosure without an
available opening, every local lottery has the prescribed continuation law, for
every belief over the site. -/
theorem absent_opening_comparison_eq (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId} {payload : L.Ty}
    (owned : (graph service.setup).actor? event = some who)
    (isPublication : (graph service.setup).outputLayout event = .publication payload)
    (granted : view.application.publicView.serviceGrant = some event)
    (unsent : (runtime service.setup).eventRecorded service.leaks past event = false)
    (absent : rosterOpening? service.setup service.leaks who event view = none)
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
  have ownRecall : execution.recall who = past := congrArg Prod.fst input
  have ownView : execution.observe (application service.setup service.leaks) who = view :=
    congrArg Prod.snd input
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  exact approx.absent_opening_phase_invariant trace phase owned isPublication
    (ownRecall ▸ unsent) (ownView ▸ absent) first second firstAllowed secondAllowed

end TimedApproximant

end Vegas.SourceProgram.RevealService
