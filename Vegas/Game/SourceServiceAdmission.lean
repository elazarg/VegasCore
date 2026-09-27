/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBinding
import Vegas.Source.ProtocolBehavioralPolicy

/-! # Value-only source choices in the concrete binding service

The original value-only source game already excludes failed bindings. Its
legal policies therefore emit successful typed bindings through the actual
compiler. This is a consequence of source-game legality, not an extra compiler
restriction on an otherwise available source choice. Deferred guard failure
is separate and remains possible at publication.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every supported physical binding response of a legal value-only source
policy names a successful typed value. Allocation uses the actual current
catalogue; earlier binding phases need not have left it unchanged. -/
theorem sourceServicePolicy_commit_supported
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (permitted : (profile owner).Admitted (.commit name owner fresh guard next)
      (CommitmentInterface.values _))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (granted : execution.application.serviceGrant =
      some (embedding.event ⟨0, by simp [eventCount]⟩))
    (serial : Nat)
    (selected : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServicePolicy setup leaks wholeProfile owner
      (execution.recall owner) (execution.observe (application setup leaks) owner)).support) :
    ∃ value : L.Val payload,
      PublicationResult.success value ∈ (commitKernel profile (source.view owner)).support ∧
      response = (runtime setup).reactiveBinding leaks owner
        (embedding.event ⟨0, by simp [eventCount]⟩) payload (.success value) serial := by
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event index
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq := by
    cases viewed : nodeView (graph setup) event with
    | sample otherPayload law kind code => cases kind.symm.trans outputEq
    | resolve other otherPayload binding checks kind code => cases kind.symm.trans outputEq
    | bind other otherPayload kind code =>
        obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj (kind.symm.trans outputEq)
        rfl
  rw [sourceServicePolicy_commit setup leaks fresh guard next wholeProfile profile refs source
    embedding refsBefore offset aligned execution agree history granted,
    FinDist.support_map] at supported
  obtain ⟨choice, choiceSupported, responseEq⟩ := supported
  have allowed := permitted.1 rfl (source.view owner) choice choiceSupported
  cases choice with
  | failure => cases allowed
  | success value =>
      refine ⟨value, choiceSupported, ?_⟩
      rw [← responseEq]
      exact serviceDecision_binding_fresh (runtime setup) leaks execution owner event payload
        outputEq codeEq node serial selected candidate (.success value)

end Vegas.SourceProgram.RevealService
