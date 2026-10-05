/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingGuardedStep
import Vegas.Pending.ReactiveBindingFrameRounds
import GameTheoryExtensions.Math.Probability.Support

/-! # The actual mixed disclosure response under binding repair

Silence and first successful guarded openings use
the unchanged response on the repaired execution. This identifies the real
legal implementation transition, including private-memory update and the
complete joint observations. Inclusion may still occur later.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

omit [Fintype Player] in
/-- The exact canonical physical response preserves the repaired frame; the
certificate can use owned issuance or any semantic forwarding representative. -/
theorem successful_response_frame
    (frame : Frame runtime leaks memory owner original repaired)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (value : L.Val payload)
    (stored : binding.get? original.application.config.store = some (.success value))
    (resolved : EventCode.resolveOutput? binding checks true original.application.config.store =
      some (.success value)) :
    let app := runtime.reactiveApplication leaks
    let response := runtime.serviceDecision leaks owner (original.recall owner)
      (original.observe app owner) event (cast (congrArg EventField.Action outputEq.symm) true)
    Frame runtime leaks
      (memory.record runtime leaks
        (memory.shadow.inputView runtime leaks (repaired.observe app owner)) response)
      owner (original.respond app owner response) (repaired.respond app owner response) := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  obtain ⟨_, candidate, associated, _, owned, leftFixed, rightFixed⟩ :=
    frame.successful_opening leftBinding rightBinding binding value stored
  have response := runtime.serviceDecision_successful_opening leaks original leftRecall owner
    event payload binding checks outputEq codeEq node candidate value associated owned leftFixed
      resolved
  rw [response]
  let call := disclosureSubmission (.opening event candidate ⟨payload, value⟩)
  let material := call.normalizeReactive owner (app.observePlayer original.application owner)
    (original.network.known owner)
  have callEq : material.call = ⟨.opening event candidate ⟨payload, value⟩, none⟩ := by
    simp only [material, call, disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none]
  have unchanged (execution : app.Execution) : app.submit execution.application owner material =
      execution.application := by
    change submitStep (material.call.register execution.application owner) owner
      material.call.packet = _
    rw [callEq]
    rfl
  apply frame.inert_submission material material (unchanged original) (unchanged repaired)
  have leftEmit := WitnessedSubmission.normalizeReactive_emit runtime leaks original.application
    owner (original.network.known owner) call
  have rightEmit := WitnessedSubmission.normalizeReactive_emit runtime leaks repaired.application
    owner (repaired.network.known owner) call
  change material.emit original.application owner (original.network.known owner) =
    call.emit original.application owner (original.network.known owner) at leftEmit
  change (call.normalizeReactive owner (app.observePlayer repaired.application owner)
    (repaired.network.known owner)).emit repaired.application owner (repaired.network.known owner) =
      call.emit repaired.application owner (repaired.network.known owner) at rightEmit
  rw [show material = call.normalizeReactive owner (app.observePlayer repaired.application owner)
    (repaired.network.known owner) from
      frame.normalized_opening_eq event candidate ⟨payload, value⟩ owned leftFixed rightFixed]
      at leftEmit ⊢
  rw [leftEmit, rightEmit]
  have leftVerified := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr leftFixed
  have rightVerified := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr rightFixed
  simp only [call, disclosureSubmission, WitnessedSubmission.emit, owned,
    leftVerified, rightVerified, and_self, ↓reduceIte, frame.publicView]

/-- A complete finite response law on the clean resolve branch is coupled to
the actual legal implementation. The support premise is an explicit packet
classification; excluded packets are left for the stopped-run evidence branch. -/
theorem resolve_response_coupling
    (frame : Frame runtime leaks memory owner original repaired) (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (coverage : bounds.compiledActions runtime leaks owner (repaired.recall owner)
      (repaired.observe (runtime.reactiveApplication leaks) owner) ⊆
        menu.actions owner (repaired.recall owner)
          (repaired.observe (runtime.reactiveApplication leaks) owner))
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
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
    (available : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
          (original.observe (runtime.reactiveApplication leaks) owner))
    (clean : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        response ∈ ((runtime.reactiveApplication leaks).silentPolicy (original.recall owner)
          (original.observe (runtime.reactiveApplication leaks) owner)).support ∨
        ∃ value, binding.get? original.application.config.store = some (.success value) ∧
          EventCode.resolveOutput? binding checks true original.application.config.store =
            some (.success value) ∧
          response = runtime.serviceDecision leaks owner (original.recall owner)
            (original.observe (runtime.reactiveApplication leaks) owner) event
              (cast (congrArg EventField.Action outputEq.symm) true) ∧
          runtime.firstSubmission leaks (original.recall owner) response = true) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length := by
  classical
  have turnSome := original.application.publicView.ownTurn?_of_ownTurn owner event turn
  let app := runtime.reactiveApplication leaks
  let law := players owner (original.recall owner) (original.observe app owner)
  let updated (response : app.Action) := memory.record runtime leaks
    (memory.shadow.inputView runtime leaks (repaired.observe app owner)) response
  have silentLaw :
      app.silentPolicy (original.recall owner) (original.observe app owner) =
        app.silentPolicy (repaired.recall owner) (repaired.observe app owner) := rfl
  have unchanged (response : app.Action) (supported : response ∈ law.support) :
      memory.repairResponse runtime leaks owner (repaired.observe app owner) response =
        (response, memory.shadow) := by
    rcases clean response supported with silenced | ⟨value, stored, resolved, same, _⟩
    · rcases app.silentPolicy_cases _ _ response silenced with rfl
      rfl
    · obtain ⟨_, candidate, associated, _, owned, fixed, _⟩ :=
        frame.successful_opening leftBinding rightBinding binding value stored
      have actual := runtime.serviceDecision_successful_opening leaks original leftRecall owner
        event payload binding checks outputEq codeEq node candidate value associated owned fixed
          resolved
      rw [same, actual]
      simp only [repairResponse, disclosureSubmission, WitnessedSubmission.normalizeReactive,
        Submission.normalizeReactive_none]
  have retained (response : app.Action) (supported : response ∈ law.support) :
      response ∈ bounds.compiledActions runtime leaks owner (repaired.recall owner)
        (repaired.observe app owner) := by
    rcases clean response supported with silenced | ⟨value, stored, resolved, same, first⟩
    · rw [silentLaw] at silenced
      exact bounds.silent_compiled runtime leaks owner _ _ response silenced
    · exact frame.successful_serviceDecision_retained bounds leftRecall rightRecall leftBinding
        rightBinding event payload binding checks outputEq codeEq node turn actor ready timely
          value stored resolved response same (available response supported) first
  have responseLaw :
      (implementation runtime leaks owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner) =
          law.map (fun response => (response, updated response)) := by
    rw [implementation_respond runtime leaks owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed]
    apply map_congr_on_support _
    intro response supported
    rw [unchanged response supported]
    simp only [updated, record, app, frame.observed]
  have legalLaw :
      (retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner) =
          law.map (fun response => (response, updated response)) := by
    change ((implementation runtime leaks owner reference (players owner)).respond memory
      (repaired.recall owner, repaired.observe app owner)).map _ = _
    rw [responseLaw, PMF.map_comp]
    apply map_congr_on_support _
    intro response supported
    simp only [Function.comp_def]
    have member : response ∈ menu.actions owner (repaired.recall owner)
        (repaired.observe app owner) := coverage (retained response supported)
    rw [ite_eq_left member]
  let coupling := law.map fun response =>
    (original.respond app owner response, repaired.respond app owner response, updated response)
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp]
    rfl
  · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume, ↓reduceIte]
    change law.map _ =
      ((retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner)).map _
    rw [legalLaw, PMF.map_comp]
    rfl
  · intro next supported
    obtain ⟨response, member, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨?_, ?_⟩
    · rcases clean response member with silenced | ⟨value, stored, resolved, same, _⟩
      · apply frame.transport_response response
        intro material
        rcases app.silentPolicy_cases _ _ response silenced with rfl
        simp
      · rw [same]
        exact frame.successful_response_frame leftRecall leftBinding rightBinding event payload
          binding checks outputEq codeEq node value stored resolved
    · rw [app.respond_recall_length]
      omega

end Vegas.EventGraphRuntime.BindingMemory.Frame
