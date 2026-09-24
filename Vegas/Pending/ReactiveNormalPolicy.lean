/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFiniteResponses
import Vegas.Pending.ReactivePolicyFacts

/-! # The compiler emits semantic normal forms

The compiler never uses failed replays or irrelevant opening metadata as
private storage. Normalization fixes every supported compiled response,
including recovery. Membership in a finite instance additionally requires the
explicit packet and effective-opening bounds.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveDecision_normal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    (runtime.reactiveNormalization leaks).action who past view
        (runtime.reactiveDecision leaks who event choice view.application) =
      runtime.reactiveDecision leaks who event choice view.application := by
  classical
  unfold reactiveDecision
  split
  · rfl
  · cases selected : reactiveFreshSlot view.application with
    | none => rfl
    | some serial =>
        have fresh := reactiveFreshSlot_spec view.application serial selected
        simp [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
          Submission.normalizeReactive, openingEffective, fresh]
  · simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      Submission.normalizeReactive_none]

private theorem prescribed_response_normal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (runtime.prescribedReactiveResponse leaks who policy past intentions view).map
        (fun response => (runtime.reactiveNormalization leaks).action who past view response.1) =
      (runtime.prescribedReactiveResponse leaks who policy past intentions view).map Prod.fst := by
  unfold prescribedReactiveResponse
  split
  · simp only [FinDist.map_pure]; rfl
  · split
    · simp only [FinDist.map_pure]; rfl
    · split
      · split
        · split
          · simp only [FinDist.map_comp, Function.comp_def, reactiveDecision_normal]
          · simp only [FinDist.map_pure]; rfl
        · simp only [FinDist.map_pure]; rfl
      · simp only [FinDist.map_pure]; rfl

private theorem recovery_response_normal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (runtime.recoverReactiveResponse leaks who policy past intentions view).map
        (fun response => (runtime.reactiveNormalization leaks).action who past view response.1) =
      (runtime.recoverReactiveResponse leaks who policy past intentions view).map Prod.fst := by
  unfold recoverReactiveResponse
  split
  · simp only [FinDist.map_pure]; rfl
  · split
    · split
      · split
        · simp only [FinDist.map_comp, Function.comp_def, reactiveDecision_normal]
        · simp only [FinDist.map_pure]; rfl
      · simp only [FinDist.map_pure]; rfl
    · simp only [FinDist.map_pure]; rfl

theorem prescribedReactivePolicy_normal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (runtime.prescribedReactivePolicy leaks who policy past view).map
        ((runtime.reactiveNormalization leaks).action who past view) =
      runtime.prescribedReactivePolicy leaks who policy past view := by
  simp only [prescribedReactivePolicy_apply, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
  apply FinDist.bind_congr
  intro intentions _
  exact prescribed_response_normal runtime leaks who policy past intentions view

theorem recoverReactivePolicy_normal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (runtime.recoverReactivePolicy leaks who policy past view).map
        ((runtime.reactiveNormalization leaks).action who past view) =
      runtime.recoverReactivePolicy leaks who policy past view := by
  simp only [recoverReactivePolicy_apply, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
  apply FinDist.bind_congr
  intro intentions _
  exact recovery_response_normal runtime leaks who policy past intentions view

theorem compileReactivePolicy_normal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (runtime.compileReactivePolicy leaks who policy past view).map
        ((runtime.reactiveNormalization leaks).action who past view) =
      runtime.compileReactivePolicy leaks who policy past view := by
  classical
  unfold compileReactivePolicy ReactiveApplication.Policy.recover
  split
  · exact runtime.prescribedReactivePolicy_normal leaks who policy past view
  · exact runtime.recoverReactivePolicy_normal leaks who policy past view

theorem compiled_response_normal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (supported : response ∈ (runtime.compileReactivePolicy leaks who policy past view).support) :
    (runtime.reactiveNormalization leaks).action who past view response = response := by
  rw [← runtime.compileReactivePolicy_normal leaks who policy past view] at supported
  obtain ⟨original, _, rfl⟩ := FinDist.support_map .. ▸ supported
  exact (runtime.reactiveNormalization leaks).action_idempotent who past view original

end Vegas.EventGraphRuntime
