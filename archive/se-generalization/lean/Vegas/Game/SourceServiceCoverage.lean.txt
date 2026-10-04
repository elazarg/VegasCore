/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCheckpoint
import Vegas.Game.SourceServiceTimedPolicy
import Vegas.Game.SourceServiceAdmission
import Vegas.Pending.ReactiveBoundedValues
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Pending.ReactiveCompiledResolution

/-! # Coverage of actual source decisions in the retained service

Legality of the original value-binding source policy and the fixed finite
alphabet cover every supported binding response. The proof uses the current
catalogue's fresh slot; earlier source commitments may have changed it.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

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
  have serving := ownTurn?_of_ready setup execution.application ready actor
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
    change (⟨some ((disclosureSubmission (.opening event candidate
        ⟨payload, value⟩)).normalizeReactive
        owner _ (execution.network.known owner))⟩ : app.Action) = _
    rw [known]
    rfl
  apply required_decision_sourceService setup leaks bounds rosters owner
    (execution.recall owner) (execution.observe app owner)
  apply bounds.decision_required (runtime setup) leaks owner (execution.recall owner)
    (execution.observe app owner)
  · have publicReady := (execution.application.publicView_eventReady event).mpr ready
    have turnView : (execution.observe app owner).application.publicView.ownTurn? owner =
        some event := serving
    have readyView : (execution.observe app owner).application.publicView.EventReady event :=
      publicReady
    simp only [MessageBounds.decisionActions, turnView, actor, readyView, and_self,
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

/-- Authenticated withholding remains available at the final owner visit as
well as at every earlier unsent resolution opportunity. -/
theorem sourceService_withholding_covered
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (execution : (application setup leaks).Execution)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false) :
    (runtime setup).serviceDecision leaks owner (execution.recall owner)
      (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false) ∈
      (sourceServiceMenu setup leaks bounds rosters).actions owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) := by
  classical
  let app := application setup leaks
  have serving := ownTurn?_of_ready setup execution.application ready owned
  have canonical : (runtime setup).serviceDecision leaks owner (execution.recall owner)
      (execution.observe app owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false) =
      ⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩ := by
    simp only [serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
      cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
      disclosureSubmission_normalize_withhold]
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none, EvidenceRequest.normalize_none]
  apply required_decision_sourceService setup leaks bounds rosters owner
    (execution.recall owner) (execution.observe app owner)
  apply bounds.decision_required (runtime setup) leaks owner (execution.recall owner)
    (execution.observe app owner)
  · have publicReady := (execution.application.publicView_eventReady event).mpr ready
    have turnView : (execution.observe app owner).application.publicView.ownTurn? owner =
        some event := serving
    have readyView : (execution.observe app owner).application.publicView.EventReady event :=
      publicReady
    simp only [MessageBounds.decisionActions, turnView, owned, readyView,
      and_self, ↓reduceIte, node]
    exact Finset.mem_image.mpr ⟨false, Finset.mem_univ _, rfl⟩
  · rw [canonical]
    simp only [firstSubmission, submittedEvent?, Payload.event?, unsent, Bool.not_false]
  · rw [canonical, bounds.menu_mem]
    refine ⟨⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
      EvidenceRequest.normalize_none]

theorem sourceServiceOpportunity_commit_covered
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
    ∀ (_ready : execution.application.config.cut.Ready event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      response,
      response ∈ (sourceServiceOpportunity setup leaks wholeProfile owner event
        (execution.recall owner) (execution.observe (application setup leaks) owner)).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions owner
        (execution.recall owner) (execution.observe (application setup leaks) owner) ∧
      (runtime setup).submittedEvent? leaks response = some event := by
  classical
  intro index event ready unsent response supported
  let app := application setup leaks
  have outputEq : (graph setup).outputLayout event = .binding owner payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_bind _ _
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  simp only [sourceServiceOpportunity, unsent, Bool.false_eq_true, ↓reduceIte] at supported
  obtain ⟨chosen, chosenSupported, supported⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨value, _sourceSupported, chosenEq⟩ := sourceServicePolicy_commit_supported
    setup leaks fresh guard next wholeProfile profile permitted refs source embedding refsBefore
    offset aligned execution agree history ready serial selected candidate chosen chosenSupported
  have transmitted : chosen.transmission ≠ none := by
    rw [chosenEq]
    exact Option.some_ne_none _
  rw [ite_eq_right transmitted] at supported
  cases (PMF.mem_support_pure_iff _ _).mp supported
  rw [chosenEq]
  have bounded := covered event
  rw [outputEq] at bounded
  have member := bounds.binding_value_required (runtime setup) leaks owner
    (execution.recall owner) (execution.observe app owner) event payload outputEq codeEq node
    ((soleReady_of_ready setup execution.application ready).ownTurn owned) owned
    ((execution.application.publicView_eventReady event).mpr ready)
    unsent serial selected capacity value (bounded value)
  rw [serviceDecision_binding_fresh (runtime setup) leaks execution owner event payload
    outputEq codeEq node serial selected candidate (.success value)] at member
  exact ⟨required_decision_sourceService setup leaks bounds rosters owner
    (execution.recall owner) (execution.observe app owner) _ member, rfl⟩

/-- Every supported guarded disclosure is retained at any unsent owner
visit. Failed intentions and withholding use actual replay aliases; successful
intentions use the bounded authentic opening. -/
theorem sourceServiceOpportunity_reveal_covered
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
    ∀ (_ready : execution.application.config.cut.Ready event)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      response,
      response ∈ (sourceServiceOpportunity setup leaks wholeProfile owner event
        (execution.recall owner) (execution.observe (application setup leaks) owner)).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions owner
        (execution.recall owner) (execution.observe (application setup leaks) owner) ∧
        (runtime setup).submittedEvent? leaks response = some event := by
  classical
  intro index event ready unsent response supported
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
      outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  have emitted (choice : Bool) : ((runtime setup).serviceDecision leaks owner
      (execution.recall owner) (execution.observe app owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)).transmission ≠ none := by
    rcases (runtime setup).serviceDecision_resolution_cases leaks owner (execution.recall owner)
      (execution.observe app owner) event owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq node choice with withheld | ⟨candidate, value, evidence, _, _, _, opened⟩
    · rw [withheld]
      intro same
      cases same
    · rw [opened]
      intro same
      cases same
  have named (choice : Bool) : (runtime setup).submittedEvent? leaks
      ((runtime setup).serviceDecision leaks owner (execution.recall owner)
        (execution.observe app owner) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)) = some event := by
    rcases (runtime setup).serviceDecision_resolution_cases leaks owner (execution.recall owner)
      (execution.observe app owner) event owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq node choice with withheld | ⟨candidate, value, evidence, _, _, _, opened⟩
    · rw [withheld]
      rfl
    · rw [opened]
      rfl
  simp only [sourceServiceOpportunity, unsent, Bool.false_eq_true, ↓reduceIte] at supported
  rw [sourceServicePolicy_reveal setup leaks fresh binding unresolved next wholeProfile profile
      refs source embedding refsBefore offset aligned execution checkpoint.agrees checkpoint.history
        ready, PMF.bind_map] at supported
  obtain ⟨disclose, _chosen, supported⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  simp only [Function.comp_apply] at supported
  rw [serviceDecision_effectiveDisclosure (runtime setup) leaks published binding source refs
    execution checkpoint.agrees event outputEq codeEq node disclose] at supported
  cases effective : effectiveDisclosure published binding source disclose with
  | false =>
      rw [effective, ite_eq_right (emitted false)] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨sourceService_withholding_covered setup leaks bounds rosters execution owner event
        payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding)
        outputEq codeEq node owned ready unsent, named false⟩
  | true =>
      rw [effective, ite_eq_right (emitted true)] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
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
      exact ⟨sourceService_opening_covered setup leaks bounds rosters execution valid recalled
        handles values owner event payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding)
        outputEq codeEq node owned ready unsent value resolved, named true⟩

end Vegas
