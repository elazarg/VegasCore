/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceProtectedDecisionLaw
import Vegas.Game.SourceServiceAlignedConstructors
import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Game.SourceServiceDisclosure

/-! # Actual source disclosure marginals after protected deferrals

The current response law is the original residual disclosure kernel rendered
at the actual own recall and observation, with only its geometric waiting mass
added. For effective source policies the actual withholding and opening packets
identify FALSE and TRUE respectively. Their marginal is therefore the original
source Bool law, rather than an assumed source draw or a support-only result.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Read the actual named withholding or opening decision from its response.
Silence and packets naming other events have no current resolution decision. -/
def resolutionResponseDecision? (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (event : (graph setup).EventId) (response : (application setup leaks).Action) : Option Bool :=
  response.transmission.bind fun material => match material.call.packet with
    | .withhold addressed => if addressed = event then some false else none
    | .opening addressed _ _ => if addressed = event then some true else none
    | .commitment .. | .malformed .. => none

private theorem revealSource_response_law
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution)
    (site : RevealSource setup profile event execution.application.config)
    (ready : execution.application.config.cut.Ready event) :
    sourceServiceCanonicalPolicy setup leaks profile site.owner (execution.recall site.owner)
        (execution.observe (application setup leaks) site.owner) =
      (revealKernel site.residual (site.source.view site.owner)).map fun disclose =>
        (runtime setup).canonicalServiceDecision leaks site.owner (execution.recall site.owner)
          (execution.observe (application setup leaks) site.owner) event
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) := by
  have outputEq := site.outputEq
  obtain ⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, _, _⟩ := site
  dsimp only at *
  subst head
  exact sourceServiceCanonicalPolicy_reveal setup leaks fresh binding unresolved next profile
    residual refs source embedding refsBefore _ aligned execution agree history ready

variable [Fintype Player]

/-- The actual marginal at any clear protected resolution turn is the residual
source disclosure law with geometric waiting. Previous silent turns are
accounted for by the actual recall posterior, not reset to a first turn. -/
theorem sourceServiceDecision_clear_protected_resolution_response {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (profile : BehavioralProfile setup.program) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (site : RevealSource setup profile event execution.application.config)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some site.owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (ready : execution.application.config.cut.Ready event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1) :
    sourceServiceTurnPolicy setup leaks bound horizon
        (geometricTiming setup horizon weight positive.le below.le) profile site.owner
        (execution.recall site.owner) (execution.observe (application setup leaks) site.owner) =
      mix weight positive.le below.le (PMF.pure ⟨none⟩)
        ((revealKernel site.residual (site.source.view site.owner)).map fun disclose =>
          (runtime setup).canonicalServiceDecision leaks site.owner (execution.recall site.owner)
            (execution.observe (application setup leaks) site.owner) event
            (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)) := by
  have turn := ownTurn?_of_ready setup execution.application ready site.owned
  have law := sourceServiceDecision_clear_protected_compiled_response bounds bound profile
    site.owner execution trace clear event unrecorded turn fits weight positive below
  rw [← sourceServiceCanonicalPolicy_at_event setup leaks profile site.owner execution event turn
      site.owned, revealSource_response_law execution site ready] at law
  exact law

omit [Fintype Player] in
private theorem effective_resolution_response_decision
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {owner : Player}
    (execution : (application setup leaks).Execution)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (site : RevealSource setup profile event execution.application.config)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (disclose : Bool)
    (supported : disclose ∈ (revealKernel site.residual (site.source.view site.owner)).support) :
    resolutionResponseDecision? setup leaks event
        ((runtime setup).canonicalServiceDecision leaks site.owner (execution.recall site.owner)
          (execution.observe (application setup leaks) site.owner) event
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)) =
      some disclose := by
  have outputEq := site.outputEq
  obtain ⟨Γ, names, published, who, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head,
    inherits, supportedChoices⟩ := site
  dsimp only at *
  subst head
  let index : Fin (eventCount (.reveal published who name fresh binding unresolved next)) :=
    ⟨0, by simp [eventCount]⟩
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes (embedding.event index)) = .resolve who payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations
          binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes _) = _
    simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node := nodeView_eq_resolve outputEq codeEq
  rcases effective_reveal_supported fresh binding unresolved next residual source
      (inherits effective who) disclose supported with rfl | ⟨value, rfl, success⟩
  · rw [(runtime setup).canonicalServiceDecision_resolution_false leaks who _ _ _ who payload
      (refs.get binding) _ outputEq codeEq node]
    simp only [resolutionResponseDecision?, Option.bind_some, ↓reduceIte]
  · have facts := legalFacts setup leaks horizon scheduler _ trace
    obtain ⟨candidate, associated, owned, fixed, _⟩ := guarded_rosterOpening_success setup leaks
      published binding source refs execution agree facts.binding (embedding.event index) outputEq
      codeEq node value success
    have resolved := compiled_disclosure_result (graph := graph setup) published binding source
      refs execution.application.config.store agree true
    rw [success, EventGraph.EventCode.resolveOutput?_playerStore] at resolved
    rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks who _ _ _ _ (by
      intro actor ty output code impossible
      rw [node] at impossible
      cases impossible), (runtime setup).serviceDecision_successful_opening leaks execution
        facts.inputs who (embedding.event index) payload (refs.get binding) _ outputEq codeEq node
        candidate value associated owned fixed resolved]
    simp only [resolutionResponseDecision?, WitnessedSubmission.normalizeReactive,
      disclosureSubmission, Submission.normalizeReactive_none, Option.bind_some, index, ↓reduceIte]

/-- The physical FALSE/TRUE marginal is exactly the source Bool marginal with
the actual geometric wait mass. Effectiveness and authentic initialized state
derive the packet's Bool; no source-draw law is assumed. -/
theorem sourceServiceDecision_clear_protected_resolution_marginal {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (site : RevealSource setup profile event execution.application.config)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some site.owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (ready : execution.application.config.cut.Ready event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1) :
    (sourceServiceTurnPolicy setup leaks bound horizon
        (geometricTiming setup horizon weight positive.le below.le) profile site.owner
        (execution.recall site.owner) (execution.observe (application setup leaks) site.owner)).map
          (resolutionResponseDecision? setup leaks event) =
      mix weight positive.le below.le (PMF.pure none)
        ((revealKernel site.residual (site.source.view site.owner)).map some) := by
  rw [sourceServiceDecision_clear_protected_resolution_response bounds bound profile execution
    event site trace clear ready unrecorded fits weight positive below, mix_map, PMF.pure_map,
    PMF.map_comp]
  congr 1
  apply map_congr_on_support _
  intro disclose supported
  exact effective_resolution_response_decision execution
    ((bounds.riskMenu (runtime setup) leaks bound).toRawTrace _ _ _ trace) site effective disclose
    supported

end Vegas
