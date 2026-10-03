/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingCopiedWindow
import Vegas.Pending.ReactiveBindingRiskRecall
import Vegas.Pending.ReactiveBindingGuardedStep
import Vegas.Pending.ReactiveCompiledResolution
import Vegas.Pending.ReactiveBindingCopiedResume

/-! # Retained decision admission through private binding repair

Original risk-menu membership derives repaired admission at the same actual
input. Clear binding and resolution inputs derive fresh typed slots, protected
opportunities, and actual certificate and guard transport. Expanded inputs
retain every bounded effective response using their equal risk records. The
actual invocation and resume coupling permits noncommitments, fresh owned
registrations and fixed reuses with matching meanings or a public association.
Unassociated changed candidates and whole-continuation utility remain
separate.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- The canonical counted-or-least-fresh allocator sees the same public count
and candidate freshness on both actual executions. -/
theorem canonicalFreshSlot_eq
    (frame : Frame runtime leaks memory owner original repaired) :
    canonicalFreshSlot owner
        (original.observe (runtime.reactiveApplication leaks) owner).application =
      canonicalFreshSlot owner
        (repaired.observe (runtime.reactiveApplication leaks) owner).application := by
  classical
  let app := runtime.reactiveApplication leaks
  have count := congrFun (congrArg PublicView.bindingCount frame.publicView) owner
  have allocated := reactiveFreshSlot_congr (original.observe app owner).application
    (repaired.observe app owner).application (fun serial => frame.slots (.prepared serial))
  change (if original.application.candidates.lookup
      (owner, .prepared (original.application.publicView.bindingCount owner)) = .fresh then
        some (original.application.publicView.bindingCount owner) else _) =
    (if repaired.application.candidates.lookup
      (owner, .prepared (repaired.application.publicView.bindingCount owner)) = .fresh then
        some (repaired.application.publicView.bindingCount owner) else _)
  rw [count]
  by_cases fresh : original.application.candidates.lookup
      (owner, .prepared (repaired.application.publicView.bindingCount owner)) = .fresh
  · rw [ite_eq_left fresh, ite_eq_left ((frame.slots _).mp fresh)]
  · rw [ite_eq_right fresh,
      ite_eq_right (fun available => fresh ((frame.slots _).mpr available))]
    exact allocated

variable [Fintype Player]

/-- Clear retained binding responses transport as the same actual response.
Non-silence derives a fresh typed registration and protected delivery from the
original menu; neither property is an extra policy assumption. -/
theorem clear_binding_response_retained
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (bound : graph.EventId → Nat)
    (riskRecords : (original.recall owner).map (runtime.submissionRiskRecord leaks) =
      (repaired.recall owner).map (runtime.submissionRiskRecord leaks))
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (turn : original.application.publicView.ownTurn? owner = some event)
    (clear : runtime.serviceRisk leaks bound owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner) = false)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.riskActions runtime leaks bound owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    runtime.serviceRisk leaks bound owner (repaired.recall owner)
        (repaired.observe app owner) = false ∧
      response ∈ bounds.riskActions runtime leaks bound owner (repaired.recall owner)
        (repaired.observe app owner) ∧
      (response = ⟨none⟩ ∨
        (original.application.publicView.InclusionFitsDeadline runtime bound event ∧
          FreshUsableBindingResponse runtime leaks owner
            (original.observe app owner).application response)) := by
  classical
  let app := runtime.reactiveApplication leaks
  have rightClear : runtime.serviceRisk leaks bound owner (repaired.recall owner)
      (repaired.observe app owner) = false :=
    (runtime.serviceRisk_congr leaks bound owner (original.recall owner) (repaired.recall owner)
      (original.observe app owner) (repaired.observe app owner) rfl frame.publicView
        riskRecords).symm.trans clear
  have effective := bounds.riskActions_effective runtime leaks bound owner _ _ member
  have transported := runtime.effectiveResponse_openable_transport leaks bounds owner
    original repaired leftRecall rightRecall frame.network frame.publicView frame.slots
      preserved response effective
  rw [bounds.riskActions_of_clear runtime leaks bound owner _ _ clear] at member
  rcases bounds.canonicalActions_cases runtime leaks owner _ _ response member with silent |
    ⟨other, choice, ownTurn, owned, ready, timely, represented, first, same⟩
  · subst response
    exact ⟨rightClear, bounds.canonicalActions_subset_risk runtime leaks bound owner _ _
      (bounds.silence_canonical runtime leaks owner _ _), Or.inl rfl⟩
  have equal : other = event := Option.some.inj (ownTurn.symm.trans turn)
  subst other
  simp only [MessageBounds.canonicalChoices, node] at represented
  obtain ⟨value, included, rfl⟩ := Finset.mem_image.mp represented
  cases selected : canonicalFreshSlot owner (original.observe app owner).application with
  | none =>
      dsimp only [app] at selected
      have silent : response = ⟨none⟩ := by
        simp only [canonicalServiceDecision, canonicalReactiveDecision, node, selected,
          Option.map_none] at same
        exact same
      refine ⟨rightClear, ?_, Or.inl silent⟩
      rw [silent]
      exact bounds.canonicalActions_subset_risk runtime leaks bound owner _ _
        (bounds.silence_canonical runtime leaks owner _ _)
  | some serial =>
      have actual := same.trans (runtime.canonicalServiceDecision_binding leaks owner _ _
        event payload outputEq codeEq node serial selected (.success value))
      have named : runtime.submittedEvent? leaks response = some event := by
        rw [actual]
        rfl
      have unsent : runtime.eventRecorded leaks (original.recall owner) event = false := by
        simpa only [EventGraphRuntime.firstSubmission, named, Bool.not_eq_true_eq_eq_false]
          using first
      have fits := runtime.serviceRisk_clear_protected_opportunity leaks bound owner
        (original.recall owner) (original.observe app owner) event rfl turn unsent clear
      have rightSelected : canonicalFreshSlot owner (repaired.observe app owner).application =
          some serial := frame.canonicalFreshSlot_eq.symm.trans selected
      have rightDecision : runtime.canonicalServiceDecision leaks owner (repaired.recall owner)
          (repaired.observe app owner) event
            (cast (congrArg EventField.Action outputEq.symm) (.success value)) = response :=
        (runtime.canonicalServiceDecision_binding leaks owner _ _ event payload outputEq codeEq
          node serial rightSelected (.success value)).trans actual.symm
      have rightUnsent := (runtime.eventRecorded_congr leaks _ _ frame.submissions event).symm.trans
        unsent
      have rightTurn : (repaired.observe app owner).application.publicView.ownTurn? owner =
          some event := by
        change repaired.application.publicView.ownTurn? owner = some event
        rw [← frame.publicView]
        exact turn
      have rightReady : (repaired.observe app owner).application.publicView.EventReady event := by
        change repaired.application.publicView.EventReady event
        rw [← frame.publicView]
        exact ready
      have rightTimely : (repaired.observe app owner).application.publicView.WithinDeadline runtime
          event := by
        change repaired.application.publicView.WithinDeadline runtime event
        rw [← frame.publicView]
        exact timely
      have rightMember := bounds.canonical_decision_retained runtime leaks owner
        (repaired.recall owner) (repaired.observe app owner) event
          (cast (congrArg EventField.Action outputEq.symm) (.success value))
          rightTurn owned rightReady rightTimely
          rightUnsent (by
            simp only [MessageBounds.canonicalChoices, node]
            exact Finset.mem_image.mpr ⟨value, included, rfl⟩) (by
              rw [rightDecision]
              exact transported.1)
      rw [rightDecision] at rightMember
      refine ⟨rightClear, bounds.canonicalActions_subset_risk runtime leaks bound owner _ _
        rightMember, Or.inr ⟨fits, ?_⟩⟩
      exact ⟨event, payload, outputEq, codeEq, serial, ⟨payload, value⟩, value, node, ready,
        canonicalFreshSlot_spec owner _ serial selected, Raw.as?_mk payload value, actual⟩

private theorem copied_retained_invoke_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (provenance : OwnerCommitmentsInertOrMatching owner original repaired)
    (leftBinding : original.application.BindingInvariant)
    (bounds : MessageBounds graph) (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (effective : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
        (original.observe (runtime.reactiveApplication leaks) owner))
    (copied : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      (∀ material, response.transmission = some material →
          ∀ addressed candidate, material.call.packet ≠ .commitment addressed candidate) ∨
        FreshOwnedBindingResponse runtime leaks owner
          (original.observe (runtime.reactiveApplication leaks) owner).application response ∨
        InertFixedOwnedBindingResponse runtime leaks owner
          (original.observe (runtime.reactiveApplication leaks) owner).application
          (repaired.observe (runtime.reactiveApplication leaks) owner).application response)
    (retained : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      response ∈ menu.actions owner (repaired.recall owner)
        (repaired.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu
      owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings owner ∧
          next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsInertOrMatching owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
          (∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
            next.2.1.application.candidates.lookup (owner, slot) = .openable raw) ∧
          ∀ slot, original.application.candidates.lookup (owner, slot) =
              repaired.application.candidates.lookup (owner, slot) →
            next.1.application.candidates.lookup (owner, slot) =
              next.2.1.application.candidates.lookup (owner, slot) := by
  let app := runtime.reactiveApplication leaks
  let effectiveMenu := bounds.menu runtime leaks
  have retainedLaw := retainedImplementation_respond_of_members runtime leaks menu owner
    reference (players owner) memory (repaired.recall owner) (repaired.observe app owner)
      started (by
        intro response chosen
        rw [frame.past, frame.observed] at chosen
        exact retained response chosen)
  have effectiveLaw := retainedImplementation_respond_of_members runtime leaks effectiveMenu owner
    reference (players owner) memory (repaired.recall owner) (repaired.observe app owner)
      started (by
        intro response chosen
        rw [frame.past, frame.observed] at chosen
        exact (runtime.effectiveResponse_openable_transport leaks bounds owner original repaired
          leftRecall rightRecall frame.network frame.publicView frame.slots preserved response
            (effective response chosen)).1)
  have resumeEq :
      (retainedImplementation runtime leaks menu owner reference (players owner)).resume
          owner players (some owner) repaired memory =
        (retainedImplementation runtime leaks effectiveMenu owner reference (players owner)).resume
          owner players (some owner) repaired memory := by
    simp only [ReactiveApplication.Implementation.resume, ↓reduceIte]
    rw [retainedLaw, effectiveLaw]
  obtain ⟨coupling, left, right, related⟩ := frame.copied_effective_response_coupling
    onlyBindings past provenance leftBinding bounds leftRecall rightRecall preserved players
      reference
      started effective copied
  exact ⟨coupling, left, right.trans resumeEq.symm, related⟩

/-- A clear retained resolution response remains the same physical action in
the repaired menu. TRUE's value, certificate and guard success are recovered
from its actual original selection and the two binding invariants. A selected
withholding response is retained as FALSE regardless of repaired private data. -/
theorem clear_resolution_response_retained
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (bound : graph.EventId → Nat)
    (riskRecords : (original.recall owner).map (runtime.submissionRiskRecord leaks) =
      (repaired.recall owner).map (runtime.submissionRiskRecord leaks))
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (turn : original.application.publicView.ownTurn? owner = some event)
    (clear : runtime.serviceRisk leaks bound owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner) = false)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.riskActions runtime leaks bound owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    runtime.serviceRisk leaks bound owner (repaired.recall owner)
        (repaired.observe app owner) = false ∧
      response ∈ bounds.riskActions runtime leaks bound owner (repaired.recall owner)
        (repaired.observe app owner) ∧
      (∀ material, response.transmission = some material →
        ∀ addressed candidate, material.call.packet ≠ .commitment addressed candidate) ∧
      (response = ⟨none⟩ ∨
        original.application.publicView.InclusionFitsDeadline runtime bound event) := by
  classical
  let app := runtime.reactiveApplication leaks
  have rightClear : runtime.serviceRisk leaks bound owner (repaired.recall owner)
      (repaired.observe app owner) = false :=
    (runtime.serviceRisk_congr leaks bound owner (original.recall owner) (repaired.recall owner)
      (original.observe app owner) (repaired.observe app owner) rfl frame.publicView
        riskRecords).symm.trans clear
  have effective := bounds.riskActions_effective runtime leaks bound owner _ _ member
  rw [bounds.riskActions_of_clear runtime leaks bound owner _ _ clear] at member
  rcases bounds.canonicalActions_cases runtime leaks owner _ _ response member with silent |
    ⟨other, choice, ownTurn, owned, ready, timely, represented, first, same⟩
  · rw [silent]
    exact ⟨rightClear, bounds.canonicalActions_subset_risk runtime leaks bound owner _ _
      (bounds.silence_canonical runtime leaks owner _ _),
      (by intro material emitted; cases emitted), Or.inl rfl⟩
  have equal : other = event := Option.some.inj (ownTurn.symm.trans turn)
  subst other
  simp only [MessageBounds.canonicalChoices, node] at represented
  obtain ⟨disclose, _, rfl⟩ := Finset.mem_image.mp represented
  have notBind : ∀ actor ty actorOutput actorCode,
      nodeView graph event ≠ .bind actor ty actorOutput actorCode := by
    intro actor ty actorOutput actorCode equality
    rw [node] at equality
    cases equality
  rw [runtime.canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _ notBind] at same
  have casesResponse := runtime.serviceDecision_resolution_cases leaks owner
    (original.recall owner) (original.observe app owner) event owner payload binding checks
      outputEq codeEq node disclose
  rw [← same] at casesResponse
  have named : runtime.submittedEvent? leaks response = some event := by
    rcases casesResponse with withheld | ⟨candidate, value, evidence, _, _, _, opening⟩
    · rw [withheld]
      rfl
    · rw [opening]
      rfl
  have unsent : runtime.eventRecorded leaks (original.recall owner) event = false := by
    simpa only [EventGraphRuntime.firstSubmission, named, Bool.not_eq_true_eq_eq_false]
      using first
  have fits := runtime.serviceRisk_clear_protected_opportunity leaks bound owner
    (original.recall owner) (original.observe app owner) event rfl turn unsent clear
  have rightUnsent := (runtime.eventRecorded_congr leaks _ _ frame.submissions event).symm.trans
    unsent
  have rightTurn : (repaired.observe app owner).application.publicView.ownTurn? owner =
      some event := by
    change repaired.application.publicView.ownTurn? owner = some event
    rw [← frame.publicView]
    exact turn
  have rightReady : (repaired.observe app owner).application.publicView.EventReady event := by
    change repaired.application.publicView.EventReady event
    rw [← frame.publicView]
    exact ready
  have rightTimely : (repaired.observe app owner).application.publicView.WithinDeadline runtime
      event := by
    change repaired.application.publicView.WithinDeadline runtime event
    rw [← frame.publicView]
    exact timely
  have retain (disclose : Bool)
      (rightDecision : runtime.canonicalServiceDecision leaks owner (repaired.recall owner)
        (repaired.observe app owner) event
          (cast (congrArg EventField.Action outputEq.symm) disclose) = response)
      (available : response ∈ (bounds.menu runtime leaks).actions owner (repaired.recall owner)
        (repaired.observe app owner)) :
      response ∈ bounds.riskActions runtime leaks bound owner (repaired.recall owner)
        (repaired.observe app owner) := by
    have canonical := bounds.canonical_decision_retained runtime leaks owner
      (repaired.recall owner) (repaired.observe app owner) event
        (cast (congrArg EventField.Action outputEq.symm) disclose) rightTurn owned rightReady
        rightTimely rightUnsent (by
          simp only [MessageBounds.canonicalChoices, node]
          exact Finset.mem_image.mpr ⟨disclose, Finset.mem_univ _, rfl⟩) (by
            rw [rightDecision]
            exact available)
    rw [rightDecision] at canonical
    exact bounds.canonicalActions_subset_risk runtime leaks bound owner _ _ canonical
  rcases casesResponse with withheld | ⟨candidate, value, evidence, localResolved,
    _associated, _owned, opening⟩
  · have rightDecision := runtime.canonicalServiceDecision_resolution_false leaks owner
      (repaired.recall owner) (repaired.observe app owner) event owner payload binding checks
        outputEq codeEq node
    refine ⟨rightClear, retain false (rightDecision.trans withheld.symm) ?_, ?_, Or.inr fits⟩
    · rw [withheld]
      apply (bounds.menu_mem runtime leaks owner _ _ _).mpr
      refine ⟨⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
      simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
        WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
        EvidenceRequest.normalize_none]
    · intro material emitted addressed chosen
      rw [withheld] at emitted
      cases Option.some.inj emitted
      intro impossible
      cases impossible
  · have actualResolved : EventCode.resolveOutput? binding checks true
        original.application.config.store = some (.success value) := by
      change EventCode.resolveOutput? binding checks true
        (graph.playerStore owner original.application.config.store) = _ at localResolved
      rwa [EventCode.resolveOutput?_playerStore] at localResolved
    have stored := EventCode.binding_success_of_resolve_success binding checks true
      original.application.config.store value actualResolved
    have discloseTrue : disclose = true := by
      cases disclose with
      | true => rfl
      | false =>
          have withheld := runtime.serviceDecision_resolution_false leaks owner
            (original.recall owner) (original.observe app owner) event owner payload binding checks
              outputEq codeEq node
          rw [withheld] at same
          rw [same] at opening
          cases Option.some.inj (congrArg ReactiveApplication.Action.transmission opening)
    subst discloseTrue
    obtain ⟨_, chosen, associated, _, chosenOwner, leftFixed, rightFixed⟩ :=
      frame.successful_opening leftBinding rightBinding binding value stored
    have physical := runtime.serviceDecision_successful_opening leaks original leftRecall owner
      event payload binding checks outputEq codeEq node chosen value associated chosenOwner
        leftFixed actualResolved
    have leftAvailable := effective
    rw [same, physical] at leftAvailable
    have rightAvailable := frame.normalized_opening_available bounds leftRecall rightRecall event
      chosen ⟨payload, value⟩ chosenOwner leftFixed rightFixed leftAvailable
    have sameDecision := frame.successful_serviceDecision_eq leftRecall rightRecall leftBinding
      rightBinding event payload binding checks outputEq codeEq node
        ((original.application.publicView_eventReady event).mp ready) timely value stored
          actualResolved
    have rightDecision : runtime.canonicalServiceDecision leaks owner (repaired.recall owner)
        (repaired.observe app owner) event
          (cast (congrArg EventField.Action outputEq.symm) true) = response := by
      rw [runtime.canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _ notBind,
        ← sameDecision, ← same]
    have normalizedEq := frame.normalized_opening_eq event chosen ⟨payload, value⟩ chosenOwner
      leftFixed rightFixed
    rw [← normalizedEq, ← physical, ← same] at rightAvailable
    refine ⟨rightClear, retain true rightDecision rightAvailable, ?_, Or.inr fits⟩
    rw [opening]
    intro material emitted addressed chosen
    cases Option.some.inj emitted
    intro impossible
    cases impossible

/-- An actual original risk-supported response remains available at the
repaired whole input. Expanded inputs use effective transport; clear inputs
derive silence or the retained binding/resolution constructors above. -/
theorem risk_response_retained
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (bound : graph.EventId → Nat)
    (riskRecords : (original.recall owner).map (runtime.submissionRiskRecord leaks) =
      (repaired.recall owner).map (runtime.submissionRiskRecord leaks))
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.riskActions runtime leaks bound owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)) :
    response ∈ bounds.riskActions runtime leaks bound owner (repaired.recall owner)
      (repaired.observe (runtime.reactiveApplication leaks) owner) := by
  let app := runtime.reactiveApplication leaks
  have riskEq := runtime.serviceRisk_congr leaks bound owner (original.recall owner)
    (repaired.recall owner) (original.observe app owner) (repaired.observe app owner) rfl
      frame.publicView riskRecords
  cases risky : runtime.serviceRisk leaks bound owner (original.recall owner)
      (original.observe app owner) with
  | true =>
      have rightRisk := riskEq.symm.trans risky
      rw [bounds.riskActions_of_risk runtime leaks bound owner _ _ rightRisk]
      exact (runtime.effectiveResponse_openable_transport leaks bounds owner original repaired
        leftRecall rightRecall frame.network frame.publicView frame.slots preserved response
          (bounds.riskActions_effective runtime leaks bound owner _ _ member)).1
  | false =>
      cases turn : original.application.publicView.ownTurn? owner with
      | none =>
          have canonical := member
          rw [bounds.riskActions_of_clear runtime leaks bound owner _ _ risky] at canonical
          rcases bounds.canonicalActions_cases runtime leaks owner _ _ response canonical with
            silent | ⟨event, choice, selected, _⟩
          · rw [silent]
            exact bounds.canonicalActions_subset_risk runtime leaks bound owner _ _
              (bounds.silence_canonical runtime leaks owner _ _)
          · change original.application.publicView.ownTurn? owner = some event at selected
            rw [turn] at selected
            cases selected
      | some event =>
          have actor := (original.application.publicView.ownTurn?_spec owner event turn).2
          cases node : nodeView graph event with
          | sample payload law outputEq codeEq =>
              have foreign : graph.actor? event = none :=
                (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                  (congrArg EventCode.actor codeEq)
              rw [foreign] at actor
              cases actor
          | bind who payload outputEq codeEq =>
              have codeActor : graph.actor? event = some who :=
                (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                  (congrArg EventCode.actor codeEq)
              have equal : who = owner :=
                Option.some.inj (codeActor.symm.trans actor)
              subst who
              exact (frame.clear_binding_response_retained bounds bound riskRecords leftRecall
                rightRecall preserved event payload outputEq codeEq node turn risky response
                  member).2.1
          | resolve who payload binding checks outputEq codeEq =>
              have codeActor : graph.actor? event = some who :=
                (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
                  (congrArg EventCode.actor codeEq)
              have equal : who = owner :=
                Option.some.inj (codeActor.symm.trans actor)
              subst who
              exact (frame.clear_resolution_response_retained bounds bound riskRecords leftRecall
                rightRecall leftBinding rightBinding event payload binding checks outputEq codeEq
                  node turn risky response member).2.1

/-- A whole-input risk-supported owner law has an actual risk-menu invocation
coupling on its explicit noncommitment/fresh-or-inert response slice. Repaired
menu membership is derived, including at already expanded inputs. -/
theorem risk_copied_invoke_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (provenance : OwnerCommitmentsInertOrMatching owner original repaired)
    (bounds : MessageBounds graph) (bound : graph.EventId → Nat)
    (riskRecords : (original.recall owner).map (runtime.submissionRiskRecord leaks) =
      (repaired.recall owner).map (runtime.submissionRiskRecord leaks))
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (supported : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      response ∈ bounds.riskActions runtime leaks bound owner (original.recall owner)
        (original.observe (runtime.reactiveApplication leaks) owner))
    (copied : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      (∀ material, response.transmission = some material →
          ∀ addressed candidate, material.call.packet ≠ .commitment addressed candidate) ∨
        FreshOwnedBindingResponse runtime leaks owner
          (original.observe (runtime.reactiveApplication leaks) owner).application response ∨
        InertFixedOwnedBindingResponse runtime leaks owner
          (original.observe (runtime.reactiveApplication leaks) owner).application
          (repaired.observe (runtime.reactiveApplication leaks) owner).application response) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks (bounds.riskMenu runtime leaks bound)
      owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings owner ∧
          next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsInertOrMatching owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
          (∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
            next.2.1.application.candidates.lookup (owner, slot) = .openable raw) ∧
          ∀ slot, original.application.candidates.lookup (owner, slot) =
              repaired.application.candidates.lookup (owner, slot) →
            next.1.application.candidates.lookup (owner, slot) =
              next.2.1.application.candidates.lookup (owner, slot) := by
  apply copied_retained_invoke_coupling frame onlyBindings past provenance leftBinding bounds
    (bounds.riskMenu runtime leaks bound) leftRecall rightRecall preserved players reference started
  · intro response chosen
    exact bounds.riskActions_effective runtime leaks bound owner _ _ (supported response chosen)
  · exact copied
  · intro response chosen
    exact frame.risk_response_retained bounds bound riskRecords leftRecall rightRecall
      leftBinding rightBinding preserved response (supported response chosen)

/-- Arbitrary foreign raw responses use their unchanged law and the existing
scalar coupling. Only the owner's locally reconstructed response is restricted
by the risk menu; fixed reuses require matching meanings or a public association. -/
theorem risk_copied_resume_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (provenance : OwnerCommitmentsInertOrMatching owner original repaired)
    (bounds : MessageBounds graph) (bound : graph.EventId → Nat)
    (riskRecords : (original.recall owner).map (runtime.submissionRiskRecord leaks) =
      (repaired.recall owner).map (runtime.submissionRiskRecord leaks))
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (supported : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      response ∈ bounds.riskActions runtime leaks bound owner (original.recall owner)
        (original.observe (runtime.reactiveApplication leaks) owner))
    (copied : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      (∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
        FreshOwnedBindingResponse runtime leaks owner
          (original.observe (runtime.reactiveApplication leaks) owner).application response ∨
        InertFixedOwnedBindingResponse runtime leaks owner
          (original.observe (runtime.reactiveApplication leaks) owner).application
          (repaired.observe (runtime.reactiveApplication leaks) owner).application response)
    (actor : Option Player) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks (bounds.riskMenu runtime leaks bound)
      owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.resume players actor original ∧
      coupling.map Prod.snd = strategy.resume owner players actor repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings owner ∧
          next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsInertOrMatching owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
          (∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
            next.2.1.application.candidates.lookup (owner, slot) = .openable raw) ∧
          ∀ slot, original.application.candidates.lookup (owner, slot) =
              repaired.application.candidates.lookup (owner, slot) →
            next.1.application.candidates.lookup (owner, slot) =
              next.2.1.application.candidates.lookup (owner, slot) := by
  let app := runtime.reactiveApplication leaks
  by_cases own : actor = some owner
  · subst actor
    exact frame.risk_copied_invoke_coupling onlyBindings past provenance bounds bound riskRecords
      leftRecall rightRecall leftBinding rightBinding preserved players reference started
        supported copied
  · obtain ⟨coupling, left, right, related⟩ := frame.copied_effective_resume_coupling onlyBindings
      past provenance leftBinding bounds leftRecall rightRecall preserved players reference started
        (fun response chosen => bounds.riskActions_effective runtime leaks bound
          owner _ _ (supported response chosen)) copied actor
    have resumeEq :
        (retainedImplementation runtime leaks (bounds.menu runtime leaks) owner reference
          (players owner)).resume owner players actor repaired memory =
        (retainedImplementation runtime leaks (bounds.riskMenu runtime leaks bound) owner reference
          (players owner)).resume owner players actor repaired memory := by
      cases actor with
      | none => rfl
      | some actor =>
          have foreign : actor ≠ owner := fun equal => own (congrArg some equal)
          simp only [ReactiveApplication.Implementation.resume, foreign, ↓reduceIte]
    exact ⟨coupling, left, right.trans resumeEq, related⟩

end Vegas.EventGraphRuntime.BindingMemory.Frame
