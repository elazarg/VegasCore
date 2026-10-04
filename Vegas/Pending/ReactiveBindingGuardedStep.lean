/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameOpening
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Pending.ReactiveBindingContinuation

/-! # Guarded disclosures in the legal repaired continuation

A successful original disclosure has the same certificate and normalized
response after hidden binding repair. The actual retained menu admits that
response, including its once-per-event discipline. No claim is made for a
guard-rejected opening: that branch has publicly checkable departure evidence.
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

/-- Semantic evidence normalization does not inspect unrelated hidden bindings.
Forwarded certificates use the same known envelope on the two executions. -/
theorem normalized_opening_eq (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (owned : candidate.1 = owner)
    (leftFixed : original.application.candidates.lookup candidate = .openable raw)
    (rightFixed : repaired.application.candidates.lookup candidate = .openable raw) :
    (disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
        ((runtime.reactiveApplication leaks).observePlayer original.application owner)
        (original.network.known owner) =
      (disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
        ((runtime.reactiveApplication leaks).observePlayer repaired.application owner)
        (repaired.network.known owner) := by
  have leftLocal : original.application.candidates.lookup (owner, candidate.2) =
      .openable raw := by simpa only [← owned, Prod.mk.eta] using leftFixed
  have rightLocal : repaired.application.candidates.lookup (owner, candidate.2) =
      .openable raw := by simpa only [← owned, Prod.mk.eta] using rightFixed
  simp only [disclosureSubmission, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive_none, Submission.candidateAfter_opening,
    EvidenceRequest.normalize]
  change (⟨⟨.opening event candidate raw, none⟩,
    EvidenceRequest.canonical (original.network.known owner)
      ((EvidenceRequest.owned ⟨candidate, raw⟩).resolve owner
        (fun slot => original.application.candidates.lookup (owner, slot))
        (original.network.known owner))⟩ : WitnessedSubmission graph) = _
  change _ = (⟨⟨.opening event candidate raw, none⟩,
    EvidenceRequest.canonical (repaired.network.known owner)
      ((EvidenceRequest.owned ⟨candidate, raw⟩).resolve owner
        (fun slot => repaired.application.candidates.lookup (owner, slot))
        (repaired.network.known owner))⟩ : WitnessedSubmission graph)
  simp only [EvidenceRequest.resolve, owned, leftLocal, rightLocal, and_self,
    ↓reduceIte, frame.network]

/-- The source disclosure decision is exactly the same physical action on the
two sides when its publication succeeds. Private catalog repairs are invisible
even to the certificate-request normal form. -/
theorem successful_serviceDecision_eq
    (frame : Frame runtime leaks memory owner original repaired)
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
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (value : L.Val payload)
    (stored : binding.get? original.application.config.store = some (.success value))
    (resolved : EventCode.resolveOutput? binding checks true original.application.config.store =
      some (.success value)) :
    let app := runtime.reactiveApplication leaks
    runtime.serviceDecision leaks owner (original.recall owner) (original.observe app owner)
        event (cast (congrArg EventField.Action outputEq.symm) true) =
      runtime.serviceDecision leaks owner (repaired.recall owner) (repaired.observe app owner)
        event (cast (congrArg EventField.Action outputEq.symm) true) := by
  obtain ⟨rightStored, candidate, leftAssociated, rightAssociated, owned,
    leftFixed, rightFixed⟩ := frame.successful_opening leftBinding rightBinding binding value stored
  have rightResolved := (opening_right_facts runtime original.application repaired.application
    frame.publicView event owner payload binding checks candidate ready timely leftAssociated
      value stored rightStored (.success value) resolved).2.2.2
  have left := runtime.serviceDecision_successful_opening leaks original leftRecall owner event
    payload binding checks outputEq codeEq node candidate value leftAssociated owned leftFixed
      resolved
  have right := runtime.serviceDecision_successful_opening leaks repaired rightRecall owner event
    payload binding checks outputEq codeEq node candidate value rightAssociated owned rightFixed
      rightResolved
  exact left.trans ((congrArg (fun submission => (⟨some (.submit submission)⟩ :
    (runtime.reactiveApplication leaks).Action))
      (frame.normalized_opening_eq event candidate ⟨payload, value⟩
        owned leftFixed rightFixed)).trans
        right.symm)

/-- The finite effective menu admits the same normalized successful opening
after repair. Raw payload bounds and known forwarding references are unchanged. -/
theorem normalized_opening_available [Fintype Player]
    (frame : Frame runtime leaks memory owner original repaired) (bounds : MessageBounds graph)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (owned : candidate.1 = owner)
    (leftFixed : original.application.candidates.lookup candidate = .openable raw)
    (rightFixed : repaired.application.candidates.lookup candidate = .openable raw)
    (available : (⟨some (.submit
      ((disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
        ((runtime.reactiveApplication leaks).observePlayer original.application owner)
        (original.network.known owner)))⟩ : (runtime.reactiveApplication leaks).Action) ∈
          (bounds.menu runtime leaks).actions owner (original.recall owner)
            (original.observe (runtime.reactiveApplication leaks) owner)) :
    (⟨some (.submit
      ((disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
        ((runtime.reactiveApplication leaks).observePlayer repaired.application owner)
        (repaired.network.known owner)))⟩ : (runtime.reactiveApplication leaks).Action) ∈
          (bounds.menu runtime leaks).actions owner (repaired.recall owner)
            (repaired.observe (runtime.reactiveApplication leaks) owner) := by
  let app := runtime.reactiveApplication leaks
  have leftKnown := app.known_from_recall original owner leftRecall
  have rightKnown := app.known_from_recall repaired owner rightRecall
  change original.network.known owner = ReactiveApplication.ResponseMenu.knownPackets
    (original.recall owner) (original.observe app owner) at leftKnown
  change repaired.network.known owner = ReactiveApplication.ResponseMenu.knownPackets
    (repaired.recall owner) (repaired.observe app owner) at rightKnown
  have sameKnown : ReactiveApplication.ResponseMenu.knownPackets
      (original.recall owner) (original.observe app owner) =
        ReactiveApplication.ResponseMenu.knownPackets
          (repaired.recall owner) (repaired.observe app owner) := by
    rw [← leftKnown, ← rightKnown, frame.network]
  have allowed := ((bounds.menu_mem runtime leaks owner _ _ _).mp available).1
  rw [frame.normalized_opening_eq event candidate raw owned leftFixed rightFixed,
    sameKnown] at allowed
  apply (bounds.menu_mem runtime leaks owner _ _ _).mpr
  refine ⟨allowed, ?_⟩
  change (⟨some (.submit
    (((disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
      (app.observePlayer repaired.application owner)
      (repaired.network.known owner)).normalizeReactive
        owner (app.observePlayer repaired.application owner)
        (ReactiveApplication.ResponseMenu.knownPackets
          (repaired.recall owner) (repaired.observe app owner))))⟩ : app.Action) = _
  rw [← rightKnown, WitnessedSubmission.normalizeReactive_idempotent]

/-- A successful clean opening remains a legal full-source response after
repair, with the same own-history first-opening test. -/
theorem successful_serviceDecision_retained [Fintype Player]
    (frame : Frame runtime leaks memory owner original repaired) (bounds : MessageBounds graph)
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
    (turn : original.application.publicView.OwnTurn owner event)
    (actor : graph.actor? event = some owner)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (value : L.Val payload)
    (stored : binding.get? original.application.config.store = some (.success value))
    (resolved : EventCode.resolveOutput? binding checks true original.application.config.store =
      some (.success value))
    (response : (runtime.reactiveApplication leaks).Action)
    (originalResponse : response = runtime.serviceDecision leaks owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner) event
        (cast (congrArg EventField.Action outputEq.symm) true))
    (available : response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner))
    (first : runtime.firstSubmission leaks (original.recall owner) response = true) :
    response ∈ bounds.compiledActions runtime leaks owner (repaired.recall owner)
      (repaired.observe (runtime.reactiveApplication leaks) owner) := by
  classical
  have turnSome := original.application.publicView.ownTurn?_of_ownTurn owner event turn
  let app := runtime.reactiveApplication leaks
  obtain ⟨rightStored, candidate, leftAssociated, rightAssociated, owned,
    leftFixed, rightFixed⟩ := frame.successful_opening leftBinding rightBinding binding value stored
  have rightFacts := opening_right_facts runtime original.application repaired.application
    frame.publicView event owner payload binding checks candidate ready timely leftAssociated
      value stored rightStored (.success value) resolved
  have left := runtime.serviceDecision_successful_opening leaks original leftRecall owner event
    payload binding checks outputEq codeEq node candidate value leftAssociated owned leftFixed
      resolved
  have right := runtime.serviceDecision_successful_opening leaks repaired rightRecall owner event
    payload binding checks outputEq codeEq node candidate value rightAssociated owned rightFixed
      rightFacts.2.2.2
  have same := frame.successful_serviceDecision_eq leftRecall rightRecall leftBinding rightBinding
    event payload binding checks outputEq codeEq node ready timely value stored resolved
  have rightAvailable : response ∈ (bounds.menu runtime leaks).actions owner
      (repaired.recall owner) (repaired.observe app owner) := by
    have leftAvailable := available
    rw [originalResponse, left] at leftAvailable
    have moved := frame.normalized_opening_available bounds leftRecall rightRecall event
      candidate ⟨payload, value⟩ owned leftFixed rightFixed leftAvailable
    rw [← right, ← same, ← originalResponse] at moved
    exact moved
  apply bounds.decision_compiled runtime leaks owner (repaired.recall owner)
    (repaired.observe app owner) response _ _ rightAvailable
  · have rightTurn : repaired.application.publicView.ownTurn? owner = some event := by
      rw [← frame.publicView]
      exact turnSome
    have rightReady := (repaired.application.publicView_eventReady event).mpr rightFacts.1
    have turnView : (repaired.observe app owner).application.publicView.ownTurn? owner =
        some event := rightTurn
    have readyView : (repaired.observe app owner).application.publicView.EventReady event :=
      rightReady
    rw [originalResponse, same]
    simp only [MessageBounds.decisionActions, turnView, actor, readyView,
      and_self, ↓reduceIte, node]
    exact Finset.mem_image.mpr ⟨true, Finset.mem_univ _, rfl⟩
  · rw [← frame.firstSubmission response]
    exact first

end Vegas.EventGraphRuntime.BindingMemory.Frame
