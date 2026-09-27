/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCheckpoint
import Vegas.Game.SourceServiceRosterPolicy
import Vegas.Game.SourceServiceAdmission
import Vegas.Pending.ReactiveBoundedValues
import Vegas.Pending.ReactiveGuardedResponse

/-! # Coverage of actual source decisions in the retained service

Legality of the original value-binding source policy and the fixed finite
alphabet cover every supported binding response. The proof uses the current
catalogue's fresh slot; earlier source commitments may have changed it.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A successful guarded opening lies in the actual retained menu. Candidate
and handle bounds are the reachable raw-runtime invariants; they do not require
enumerating the publication type or keeping its catalogue initial. -/
theorem sourceService_opening_covered
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (execution : (application setup leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (handles : bounds.AcceptedHandles execution.application)
    (values : bounds.CandidateValues execution.application)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (actor : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
    (value : L.Val payload)
    (resolved : EventGraph.EventCode.resolveOutput? binding checks true
      execution.application.config.store = some (.success value)) :
    (runtime setup).serviceDecision leaks owner (execution.recall owner)
      (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) ∈
      (sourceServiceMenu setup leaks bounds rosters).actions owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) := by
  classical
  let app := application setup leaks
  have stored : binding.get? execution.application.config.store = some (.success value) := by
    have result := resolved
    simp only [EventGraph.EventCode.resolveOutput?, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at result
    obtain ⟨bound, stored, accepted, _, same⟩ := result
    cases accepted with
    | false => cases same
    | true =>
        have boundEq : bound = .success value := Option.some.inj same
        simpa only [boundEq] using stored
  obtain ⟨candidate, associated, owned, fixed⟩ := valid.success_provenance binding value stored
  have canonical : (runtime setup).serviceDecision leaks owner (execution.recall owner)
      (execution.observe app owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) =
      ((runtime setup).reactiveNormalization leaks).action owner (execution.recall owner)
        (execution.observe app owner)
        ((runtime setup).canonicalRevealResponse leaks event candidate ⟨payload, value⟩ true) := by
    rw [(runtime setup).serviceDecision_successful_opening leaks execution recalled owner event
      payload binding checks outputEq codeEq node candidate value associated owned fixed resolved]
    have known := app.known_from_recall execution owner recalled
    change execution.network.known owner = ReactiveApplication.ResponseMenu.knownPackets
      (execution.recall owner) (execution.observe app owner) at known
    change (⟨some (.submit
      ((disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
        owner _ (execution.network.known owner)))⟩ : app.Action) = _
    rw [known]
    rfl
  have optional : ¬ bindingRequired setup leaks rosters owner (execution.recall owner)
      (execution.observe app owner) := by
    rintro ⟨other, otherPayload, otherGrant, otherBinding, _⟩
    have same : other = event := Option.some.inj (otherGrant.symm.trans granted)
    subst other
    cases otherBinding.symm.trans outputEq
  change _ ∈ sourceServiceActions setup leaks bounds rosters owner (execution.recall owner)
    (execution.observe app owner)
  rw [sourceServiceActions, ite_eq_right optional]
  apply bounds.decision_compiled (runtime setup) leaks owner (execution.recall owner)
    (execution.observe app owner)
  · have publicReady := (execution.application.publicView_eventReady event).mpr ready
    have grantedView : (execution.observe app owner).application.publicView.serviceGrant =
        some event := granted
    have readyView : (execution.observe app owner).application.publicView.EventReady event :=
      publicReady
    simp only [MessageBounds.decisionActions, grantedView, actor, readyView, and_self,
      ↓reduceIte, node]
    exact Finset.mem_image.mpr ⟨true, Finset.mem_univ _, rfl⟩
  · rw [canonical, (runtime setup).firstSubmission_normalization]
    simp only [canonicalRevealResponse, ↓reduceIte, firstSubmission, submittedEvent?,
      disclosureSubmission, Payload.event?, unsent, Bool.not_false]
  · rw [canonical]
    apply bounds.normalized_submission_available (runtime setup) leaks owner
      (execution.recall owner) (execution.observe app owner)
      (disclosureSubmission (.opening event candidate ⟨payload, value⟩))
    · exact ⟨handles binding.field candidate associated, values candidate ⟨payload, value⟩ fixed⟩
    · simp only [disclosureSubmission, Submission.normalizeReactive_none,
        MessageBounds.AllowsOpening]
    · apply bounds.normalize_evidence_mem
      exact ⟨handles binding.field candidate associated, values candidate ⟨payload, value⟩ fixed⟩

theorem sourceServiceLastPolicy_commit_covered
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (rosters : (graph setup).EventId → List Player)
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
    (serial : Nat)
    (selected : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial)
    (candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (capacity : serial < bounds.candidateCount) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    ∀ (_granted : execution.application.serviceGrant = some event)
      (_ready : execution.application.config.cut.Ready event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_last : (execution.recall owner).length + 1 =
        rosterOffset setup rosters owner event + (rosters event).count owner)
      response,
      response ∈ (sourceServiceLastPolicy setup leaks rosters wholeProfile owner
        (execution.recall owner) (execution.observe (application setup leaks) owner)).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions owner
        (execution.recall owner) (execution.observe (application setup leaks) owner) := by
  classical
  intro index event granted ready unsent last response supported
  let app := application setup leaks
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
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  rw [sourceServiceLastPolicy_at_last setup leaks rosters wholeProfile owner
    (execution.recall owner) (execution.observe app owner) event granted owned unsent last]
      at supported
  obtain ⟨chosen, chosenSupported, supported⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨value, _sourceSupported, chosenEq⟩ := sourceServicePolicy_commit_supported
    setup leaks fresh guard next wholeProfile profile permitted refs source embedding refsBefore
    offset aligned execution agree history granted serial selected candidate chosen chosenSupported
  have transmitted : chosen.transmission ≠ none := by
    rw [chosenEq]
    exact Option.some_ne_none _
  rw [ite_eq_right transmitted] at supported
  cases FinDist.mem_support_pure.mp supported
  rw [chosenEq]
  have bounded := covered event
  rw [outputEq] at bounded
  have member := bounds.binding_value_required (runtime setup) leaks owner
    (execution.recall owner) (execution.observe app owner) event payload outputEq codeEq node
    granted owned ((execution.application.publicView_eventReady event).mpr ready)
    unsent serial selected capacity value (bounded value)
  rw [serviceDecision_binding_fresh (runtime setup) leaks execution owner event payload
    outputEq codeEq node serial selected candidate (.success value)] at member
  exact required_binding_sourceService setup leaks bounds rosters owner
    (execution.recall owner) (execution.observe app owner) _ member

/-- Every supported guarded disclosure is retained at the final unsent owner
visit. Failed intentions and withholding use actual replay aliases; successful
intentions use the bounded authentic opening. -/
theorem sourceServiceLastPolicy_reveal_covered
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs offset execution.application.config)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (handles : bounds.AcceptedHandles execution.application)
    (values : bounds.CandidateValues execution.application) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    ∀ (_granted : execution.application.serviceGrant = some event)
      (_ready : execution.application.config.cut.Ready event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_last : (execution.recall owner).length + 1 =
        rosterOffset setup rosters owner event + (rosters event).count owner)
      response,
      response ∈ (sourceServiceLastPolicy setup leaks rosters wholeProfile owner
        (execution.recall owner) (execution.observe (application setup leaks) owner)).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions owner
        (execution.recall owner) (execution.observe (application setup leaks) owner) := by
  classical
  intro index event granted ready unsent last response supported
  let app := application setup leaks
  have outputEq : (graph setup).outputLayout event = .publication payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry
          source.revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq := by
    cases viewed : nodeView (graph setup) event with
    | sample otherPayload law kind code => cases kind.symm.trans outputEq
    | bind other otherPayload kind code => cases kind.symm.trans outputEq
    | resolve other otherPayload otherBinding otherChecks kind code =>
        have samePayload := EventGraph.EventField.publication.inj (kind.symm.trans outputEq)
        subst otherPayload
        have sameCode := code.symm.trans codeEq
        cases sameCode
        rfl
  have optional : ¬ bindingRequired setup leaks rosters owner (execution.recall owner)
      (execution.observe app owner) := by
    rintro ⟨other, otherPayload, otherGrant, otherBinding, _⟩
    have same : other = event := Option.some.inj (otherGrant.symm.trans granted)
    subst other
    cases otherBinding.symm.trans outputEq
  rw [sourceServiceLastPolicy_at_last setup leaks rosters wholeProfile owner _ _ event
    granted owned unsent last,
    sourceServicePolicy_reveal setup leaks fresh binding unresolved next wholeProfile profile
      refs source embedding refsBefore offset aligned execution checkpoint.agrees checkpoint.history
        granted, FinDist.bind_map] at supported
  obtain ⟨disclose, _chosen, supported⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  rw [serviceDecision_effectiveDisclosure (runtime setup) leaks published binding source refs
    execution checkpoint.agrees event outputEq codeEq node disclose] at supported
  cases effective : effectiveDisclosure published binding source disclose with
  | false =>
      rw [effective] at supported
      have silent : (runtime setup).serviceDecision leaks owner (execution.recall owner)
          (execution.observe app owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) false) = ⟨none⟩ := by
        simp only [serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
          cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
          disclosureSubmission_normalize_withhold]
        rfl
      rw [silent, ite_eq_left rfl] at supported
      change response ∈ sourceServiceActions setup leaks bounds rosters owner
        (execution.recall owner) (execution.observe app owner)
      rw [sourceServiceActions, ite_eq_right optional]
      exact bounds.replay_compiled (runtime setup) leaks owner _ _ response supported
  | true =>
      rw [effective] at supported
      by_cases silent : ((runtime setup).serviceDecision leaks owner (execution.recall owner)
          (execution.observe app owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission = none
      · rw [ite_eq_left silent] at supported
        change response ∈ sourceServiceActions setup leaks bounds rosters owner
          (execution.recall owner) (execution.observe app owner)
        rw [sourceServiceActions, ite_eq_right optional]
        exact bounds.replay_compiled (runtime setup) leaks owner _ _ response supported
      · rw [ite_eq_right silent] at supported
        cases FinDist.mem_support_pure.mp supported
        obtain ⟨value, success⟩ : ∃ value,
            disclosureResult published binding source true = .success value := by
          cases disclose with
          | false => simp only [effectiveDisclosure_false, Bool.false_eq_true] at effective
          | true =>
              cases result : disclosureResult published binding source true with
              | failure => simp only [effectiveDisclosure, result, Bool.false_eq_true] at effective
              | success value => exact ⟨value, rfl⟩
        have resolved := compiled_disclosure_result (graph := graph setup)
          published binding source refs
          execution.application.config.store checkpoint.agrees true
        rw [success, EventGraph.EventCode.resolveOutput?_playerStore] at resolved
        exact sourceService_opening_covered setup leaks bounds rosters execution valid recalled
          handles values owner event payload (refs.get binding)
          (compileChecks (published := published) refs source.registry source.revelations binding)
          outputEq codeEq node granted owned ready unsent value resolved

end Vegas.SourceProgram.RevealService
