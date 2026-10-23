/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.ReactiveService

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

/-- A resolution sends only silence or the successful typed value selected by
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
    response = ⟨none⟩ ∨ ∃ candidate value evidence,
      EventCode.resolveOutput? binding checks true view.application.observation.store =
          some (.success value) ∧
      view.application.publicView.accepted binding.field = some candidate ∧
      candidate.1 = who ∧
      response =
        ⟨some ⟨⟨.opening event candidate ⟨payload, value⟩, none⟩, evidence⟩⟩ := by
  let action := cast (congrArg EventField.Action outputEq.symm) choice
  have shape : reactiveResolutionPacket who event payload binding checks outputEq action
      view.application = none ∨
      ∃ candidate value, EventCode.resolveOutput? binding checks true
          view.application.observation.store = some (.success value) ∧
        view.application.publicView.accepted binding.field = some candidate ∧
        candidate.1 = who ∧
        reactiveResolutionPacket who event payload binding checks outputEq action
          view.application = some (.opening event candidate ⟨payload, value⟩) := by
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
    simp only [serviceDecision, reactiveDecision, node, withheld, Option.map_none]
    rfl
  · let first := WitnessedSubmission.normalizeReactive who view.application []
      (disclosureSubmission (.opening event candidate ⟨payload, value⟩))
    let evidence := (first.normalizeReactive who view.application
        (ReactiveApplication.ResponseMenu.knownPackets past view)).evidence
    refine Or.inr ⟨candidate, value, evidence, result, associated, owned, ?_⟩
    change runtime.serviceDecision leaks who past view event action = _
    simp only [serviceDecision, reactiveDecision, node, packet, Option.map_some,
      disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none]
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      evidence, first, disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none]

variable [Fintype Player]

end Vegas.EventGraphRuntime
