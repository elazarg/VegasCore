/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCompiledResolution
import Vegas.Pending.ReactivePlayerWindow

/-! # Event identities in retained service responses

Only the currently granted event can receive a fresh retained submission.
Waiting, pending replays and normalized evidence requests do not change this
fact. Thus a phase cannot consume another event's first-submission opportunity.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A fresh retained submission names the actual granted event. The statement
is valid at arbitrary local inputs, including exhausted allocators. -/
theorem MessageBounds.compiled_submitted_event (bounds : MessageBounds graph)
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (granted : view.application.publicView.serviceGrant = some event)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who past view) :
    runtime.submittedEvent? leaks response = none ∨
      runtime.submittedEvent? leaks response = some event := by
  classical
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | transport
  · have chosen := (Finset.mem_filter.mp decision).1
    simp only [MessageBounds.decisionActions, granted] at chosen
    split at chosen
    · cases node : nodeView graph event with
      | sample payload distribution outputEq codeEq =>
          rw [node] at chosen
          cases Finset.mem_singleton.mp chosen
          exact Or.inl rfl
      | bind owner payload outputEq codeEq =>
          rw [node] at chosen
          obtain ⟨value, _, rfl⟩ := Finset.mem_image.mp chosen
          cases slot : reactiveFreshSlot view.application with
          | none =>
              left
              simp only [serviceDecision, reactiveDecision, node, slot, Option.map_none]
              rfl
          | some serial =>
              right
              have action : runtime.serviceDecision leaks who past view event
                  (cast (congrArg EventField.Action outputEq.symm)
                    (PublicationResult.success value)) =
                  (runtime.reactiveNormalization leaks).action who past view
                    (runtime.reactiveBinding leaks who event payload (.success value) serial) := by
                simp only [serviceDecision, reactiveDecision, node, slot, Option.map_some,
                  cast_cast, cast_eq]
                rfl
              rw [action, runtime.submittedEvent_normalization]
              rfl
      | resolve owner payload binding checks outputEq codeEq =>
          rw [node] at chosen
          obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp chosen
          rcases runtime.serviceDecision_resolution_cases leaks who past view event owner
              payload binding checks outputEq codeEq node choice with silent |
                ⟨candidate, value, evidence, _, _, _, emitted⟩
          · rw [silent]
            exact Or.inl rfl
          · rw [emitted]
            exact Or.inr rfl
    · cases Finset.mem_singleton.mp chosen
      exact Or.inl rfl
  · rcases (runtime.reactiveApplication leaks).replayPolicy_cases past view response
        (((runtime.reactiveApplication leaks).mem_replayActions_iff _ _ _).mp transport) with rfl |
            ⟨id, rfl⟩ <;> exact Or.inl rfl

/-- An arbitrary retained response roster changes no player's submission
record for another event. Passive samples and all replay choices remain in
the actual execution. -/
theorem compiled_window_other_events (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId)
    (visits : List Player) (initial final : (runtime.reactiveApplication leaks).Execution)
    (granted : initial.application.serviceGrant = some event)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support)
    (observer : Player) (other : graph.EventId) (different : other ≠ event) :
    runtime.eventRecorded leaks (final.recall observer) other =
      runtime.eventRecorded leaks (initial.recall observer) other := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | cons actor rest ih =>
      obtain ⟨middle, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at moved
      change middle ∈ ((initial.environmentStep app (.activate actor)).bind
        (app.invoke players actor)).support at moved
      rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map] at moved
      obtain ⟨sample, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ moved
      let activated := initial.sampledActivation app actor sample
      have publicEq := (runtime.reactive_respond_application leaks activated actor response).2
      have grant : (activated.respond app actor response).application.serviceGrant =
          some event := (congrArg PublicView.serviceGrant publicEq).trans granted
      rw [ih _ grant tail]
      apply runtime.eventRecorded_respond_other leaks activated actor observer response other
      intro _
      rcases bounds.compiled_submitted_event runtime leaks actor (activated.recall actor)
          (activated.observe app actor) event granted response
            (lawful actor _ _ response chosen) with absent | current
      · rw [absent]
        intro impossible
        cases impossible
      · rw [current]
        exact fun equal => different (Option.some.inj equal).symm

end Vegas.EventGraphRuntime
