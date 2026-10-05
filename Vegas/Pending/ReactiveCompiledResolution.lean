/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.ReactiveServiceEvaluation

/-! # All retained responses within a resolution phase

The classification ranges over the entire full-source menu. Deferred guards
may fail, and certificate requests remain semantically normalized. Every
retained response preserves the application until the protected inclusion or
expiry, including at histories assigned probability zero by the source profile.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- False is an explicit evidence-free resolution decision. -/
theorem serviceDecision_resolution_false
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq) :
    runtime.serviceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) false) =
      ⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩ := by
  simp only [serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
    cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
    disclosureSubmission_normalize_withhold]
  simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    disclosureSubmission, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive_none, EvidenceRequest.normalize_none]

/-- A resolution sends withholding or the successful typed value selected by
its deferred guards. Its evidence representation is left explicit. -/
theorem serviceDecision_resolution_cases
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (choice : Bool) :
    let response := runtime.serviceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) choice)
    response = ⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩ ∨ ∃ candidate value evidence,
      EventCode.resolveOutput? binding checks true view.application.observation.store =
          some (.success value) ∧
      view.application.publicView.accepted binding.field = some candidate ∧
      candidate.1 = who ∧
      response =
        ⟨some ⟨⟨.opening event candidate ⟨payload, value⟩, none⟩, evidence⟩⟩ := by
  let action := cast (congrArg EventField.Action outputEq.symm) choice
  have shape : reactiveResolutionPacket who event payload binding checks outputEq action
      view.application = .withhold event ∨
      ∃ candidate value, EventCode.resolveOutput? binding checks true
          view.application.observation.store = some (.success value) ∧
        view.application.publicView.accepted binding.field = some candidate ∧
        candidate.1 = who ∧
        reactiveResolutionPacket who event payload binding checks outputEq action
          view.application = .opening event candidate ⟨payload, value⟩ := by
    cases choice with
    | false =>
        exact Or.inl (by simp only [reactiveResolutionPacket, action, cast_cast, cast_eq,
          Bool.false_eq_true, ↓reduceIte])
    | true =>
        cases result : EventCode.resolveOutput? binding checks true
          view.application.observation.store
        with
        | none =>
            exact Or.inl (by simp only [reactiveResolutionPacket, action, cast_cast, cast_eq,
              ↓reduceIte, result])
        | some resultValue =>
            cases resultValue with
            | failure =>
                exact Or.inl (by simp only [reactiveResolutionPacket, action, cast_cast, cast_eq,
                  ↓reduceIte, result])
            | success value =>
                cases associated : view.application.publicView.accepted binding.field with
                | none =>
                    exact Or.inl (by simp only [reactiveResolutionPacket, action, cast_cast,
                      cast_eq, ↓reduceIte, result, associated])
                | some candidate =>
                    by_cases owned : candidate.1 = who
                    · exact Or.inr ⟨candidate, value, rfl, rfl, owned, by
                        simp only [reactiveResolutionPacket, action, cast_cast, cast_eq,
                          ↓reduceIte, result, associated, owned]⟩
                    · exact Or.inl (by simp only [reactiveResolutionPacket, action, cast_cast,
                        cast_eq, ↓reduceIte, result, associated, owned])
  change runtime.serviceDecision leaks who past view event action = _ ∨ _
  rcases shape with withheld | ⟨candidate, value, result, associated, owned, packet⟩
  · left
    simp only [serviceDecision, reactiveDecision, node, withheld,
      disclosureSubmission_normalize_withhold]
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none, EvidenceRequest.normalize_none]
  · let first := WitnessedSubmission.normalizeReactive who view.application []
      (disclosureSubmission (.opening event candidate ⟨payload, value⟩))
    let evidence := (first.normalizeReactive who view.application
        (ReactiveApplication.ResponseMenu.knownPackets past view)).evidence
    refine Or.inr ⟨candidate, value, evidence, result, associated, owned, ?_⟩
    change runtime.serviceDecision leaks who past view event action = _
    simp only [serviceDecision, reactiveDecision, node, packet, disclosureSubmission,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none]
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      evidence, first, disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none]

variable [Fintype Player]

/-- Every retained choice while a resolution is the only ready event is
silence or one first withholding or opening. Under the barrier order a ready resolution is always
the only ready event. -/
theorem MessageBounds.compiled_resolution_cases (bounds : MessageBounds graph)
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (sole : view.application.publicView.SoleReady event)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who past view) :
    response = ⟨none⟩ ∨
      (graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
        runtime.firstSubmission leaks past response = true ∧
        response = ⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩) ∨
      ∃ candidate value evidence,
        graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
        EventCode.resolveOutput? binding checks true view.application.observation.store =
            some (.success value) ∧
        view.application.publicView.accepted binding.field = some candidate ∧
        candidate.1 = who ∧
        runtime.firstSubmission leaks past response = true ∧
        response =
          ⟨some ⟨⟨.opening event candidate ⟨payload, value⟩, none⟩, evidence⟩⟩ := by
  classical
  have permitted := (Finset.mem_inter.mp member).1
  rcases Finset.mem_union.mp permitted with decision | silenced
  · obtain ⟨chosen, first⟩ := Finset.mem_filter.mp decision
    by_cases acting : graph.actor? event = some who
    swap
    · simp only [decisionActions, sole.ownTurn?_foreign acting] at chosen
      exact Or.inl (Finset.mem_singleton.mp chosen)
    simp only [decisionActions, view.application.publicView.ownTurn?_of_ownTurn who event
      (sole.ownTurn acting)] at chosen
    split at chosen
    · rename_i active
      rw [node] at chosen
      obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp chosen
      rcases runtime.serviceDecision_resolution_cases leaks who past view event actor payload
        binding checks outputEq codeEq node choice with withheld |
          ⟨candidate, value, evidence, result, associated, owned, response⟩
      · exact Or.inr (Or.inl ⟨active.1, active.2, first, withheld⟩)
      · exact Or.inr (Or.inr ⟨candidate, value, evidence, active.1, active.2,
          result, associated, owned, first, response⟩)
    · exact Or.inl (Finset.mem_singleton.mp chosen)
  · exact Or.inl (Finset.mem_singleton.mp silenced)

/-- This phase law applies to every retained response, not just the compiler's
selected strategy. No private registration occurs during resolution. -/
theorem MessageBounds.compiled_resolution_application (bounds : MessageBounds graph)
    (who : Player) (execution : (runtime.reactiveApplication leaks).Execution)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (sole : execution.application.publicView.SoleReady event)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who)) :
    (execution.respond (runtime.reactiveApplication leaks) who response).application =
      execution.application := by
  rcases bounds.compiled_resolution_cases runtime leaks who _ _ event actor payload binding checks
    outputEq codeEq node sole response member with rfl | ⟨_, _, _, rfl⟩ |
      ⟨candidate, value, evidence, _, _, _, _, _, _, rfl⟩
  · rfl
  · rfl
  · rfl

/-- An arbitrary finite response roster preserves the application while a
resolution is the only ready event. Passive reads remain in the actual run; only inclusion and
expiry are outside this segment. -/
theorem MessageBounds.compiled_resolution_run_application (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (network : runtime.NetworkPolicy leaks) (visits : List Player)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (sole : initial.application.publicView.SoleReady event)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    final.application = initial.application := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨action, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have same := bounds.compiled_resolution_application runtime leaks who
        (initial.sampledActivation app who sample) event actor payload binding checks
          outputEq codeEq node sole action (covered who _ _ action supported)
      exact (ih _ (by rw [same]; exact sole) reached).trans same

end Vegas.EventGraphRuntime
