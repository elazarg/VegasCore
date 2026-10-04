/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceProtectedDecisionLaw
import Vegas.Game.SourceServiceDisclosureMemory

/-! # Actual deferred resolution responses with original intention memory

The source policy here is the existing conditional-memory disclosure normalizer.
Its effective reveal kernel is derived from that construction. Waiting retains
the original source configuration, while a transmitted effective decision is
coupled with the complete original successor and its intended action history.
The native marginal is the actual geometric policy at a clear protected turn,
including turns following earlier benign deferrals.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem canonical_disclosure_response_memory
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (remember : DecisionView owner Γ → PMF (List (OwnAction Player L)))
    (choose : DecisionView owner Γ → PMF Bool) :
    let response := fun disclose => (runtime setup).canonicalServiceDecision leaks owner
      (execution.recall owner) (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    let memory := disclosureMemoryLaw published binding source.registry source.revelations
      remember choose (source.view owner)
    ((source.restoreMemory owner remember).bind fun original =>
      (choose (original.view owner)).map fun intended =>
        (execution.respond (application setup leaks) owner (response intended),
          revealSuccessor published binding original intended)) =
      (memory.map Prod.fst).bind fun effective =>
        ((fiberPosterior memory Prod.fst effective).map Prod.snd).map fun past =>
          (execution.respond (application setup leaks) owner (response effective),
            (revealSuccessor published binding source effective).withOwnHistory owner past) := by
  have rendered (disclose : Bool) :=
    (runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner
      (execution.recall owner) (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) (by
        intro actor ty output code impossible
        rw [node] at impossible
        cases impossible)
  dsimp only
  simp_rw [rendered]
  exact guarded_disclosure_response_memory setup leaks published binding source refs execution
    agree event outputEq codeEq node remember choose

variable [Fintype Player]

/-- The actual current native policy is the marginal of this joint original-
memory law. The source suffix is instantiated with the real disclosure
normalizer; its effective kernel and memory posterior are derived, not assumed.
The tagged original configuration remains before the reveal on waiting and
advances by the original intention on transmission. -/
theorem sourceServiceDecision_clear_protected_resolution_memory
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (original : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (remember : DecisionView owner Γ → PMF (List (OwnAction Player L)))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next)
      (Function.update original owner ((original owner).normalizeDisclosureFrom
        (.reveal published owner name fresh binding unresolved next)
          source.registry source.revelations remember))
      refs source.revelations source.registry embedding refsBefore offset)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some owner, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (ready : execution.application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩))
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall owner)
      (embedding.event ⟨0, by simp [eventCount]⟩) = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      (embedding.event ⟨0, by simp [eventCount]⟩))
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1) :
    let program := SourceProgram.reveal published owner name fresh binding unresolved next
    let normalized := Function.update original owner ((original owner).normalizeDisclosureFrom
      program source.registry source.revelations remember)
    let index : Fin (eventCount program) := ⟨0, by simp [program, eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, program, outputLayout, eventCount] using embedding.layout_eq index
    let response := fun disclose => (runtime setup).canonicalServiceDecision leaks owner
      (execution.recall owner) (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    let memory := disclosureMemoryLaw published binding source.registry source.revelations
      remember (revealKernel original) (source.view owner)
    let waiting : PMF ((application setup leaks).Execution ×
        (Config Player L Γ ⊕ Config Player L ((published, .publication payload) :: Γ))) :=
      (source.restoreMemory owner remember).map fun old =>
        (execution.respond (application setup leaks) owner ⟨none⟩, Sum.inl old)
    let transmitting := (source.restoreMemory owner remember).bind fun old =>
      (revealKernel original (old.view owner)).map fun intended =>
        (execution.respond (application setup leaks) owner (response intended),
          Sum.inr (revealSuccessor published binding old intended))
    let joint := mix weight positive.le below.le waiting transmitting
    joint = mix weight positive.le below.le waiting
      ((revealKernel normalized (source.view owner)).bind fun effective =>
        ((fiberPosterior memory Prod.fst effective).map Prod.snd).map fun past =>
          (execution.respond (application setup leaks) owner (response effective),
            Sum.inr ((revealSuccessor published binding source effective).withOwnHistory
              owner past))) ∧
      joint.map Prod.fst =
        (sourceServiceTurnPolicy setup leaks bound horizon
          (geometricTiming setup horizon weight positive.le below.le) wholeProfile owner
          (execution.recall owner) (execution.observe (application setup leaks) owner)).map
            (execution.respond (application setup leaks) owner) := by
  intro program normalized index event outputEq response memory waiting transmitting joint
  have kernel : revealKernel normalized (source.view owner) = memory.map Prod.fst := by
    simp only [normalized, revealKernel, Function.update_self,
      BehavioralPolicy.normalizeDisclosureFrom, program]
    rfl
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations
          binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes _) = _
    simpa [event, index, program, outputLayout, compileRankedNodes] using
      aligned.graphSuffix.nodeEq index
  have node := nodeView_eq_resolve outputEq codeEq
  have coupled := canonical_disclosure_response_memory setup leaks published binding source refs
    execution agree event outputEq codeEq node remember (revealKernel original)
  have transmitted : transmitting =
      (revealKernel normalized (source.view owner)).bind fun effective =>
        ((fiberPosterior memory Prod.fst effective).map Prod.snd).map fun past =>
          (execution.respond (application setup leaks) owner (response effective),
            Sum.inr ((revealSuccessor published binding source effective).withOwnHistory
              owner past)) := by
    rw [kernel]
    have mapped := congrArg
      (PMF.map fun pair => (pair.1, Sum.inr (α := Config Player L Γ) pair.2)) coupled
    simpa only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def,
      transmitting, response, memory]
      using mapped
  have actor : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, program, eventOwner?, eventCount] using aligned.actorEq index
  have physical := sourceServiceDecision_clear_geometric_response bounds bound wholeProfile owner
    execution trace clear event unrecorded (ownTurn?_of_ready setup execution.application ready
      actor) weight positive below
  rw [sourceServiceCanonicalOpportunity_protected bound wholeProfile owner event
    (execution.recall owner) (execution.observe (application setup leaks) owner) unrecorded fits,
    sourceServiceCanonicalPolicy_reveal setup leaks fresh binding unresolved next wholeProfile
      normalized refs source embedding refsBefore offset aligned execution agree history ready]
    at physical
  change _ = mix weight positive.le below.le (PMF.pure ⟨none⟩)
    ((revealKernel normalized (source.view owner)).map response) at physical
  constructor
  · exact congrArg (mix weight positive.le below.le waiting) transmitted
  · rw [physical]
    simp only [joint, mix_map, PMF.pure_map]
    rw [transmitted]
    congr 1
    · simp only [waiting, PMF.map_comp, Function.comp_def]
      exact PMF.map_const _ _
    · simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      calc
        _ = (revealKernel normalized (source.view owner)).bind (fun effective =>
            PMF.pure (execution.respond (application setup leaks) owner (response effective))) := by
          apply bind_congr_on_support _
          intro effective _
          exact PMF.map_const _ _
        _ = _ := rfl

end Vegas
