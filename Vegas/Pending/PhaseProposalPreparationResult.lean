/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalSubmittedBindings
import Interaction.ReactiveCompleteObservation

/-! # Actual fresh preparation repairs at the declared event type -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The actual fresh submission keeps every originally usable value. Only a
missing or mistyped preparation is replaced by a value of this event's type.
No claim is made about the original raw value at unrelated payload types. -/
theorem prepared_binding_result (runtime : EventGraphRuntime graph)
    (left right : State graph) (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (serial : Nat) (opening : Option (Raw L))
    (leftFresh : left.candidates.lookup (owner, .prepared serial) = .fresh)
    (rightFresh : right.candidates.lookup (owner, .prepared serial) = .fresh) :
    let replacement := match opening.bind (fun raw => raw.as? payload) with
      | none => some (⟨payload, L.someValue payload⟩ : Raw L)
      | some _ => opening
    let prepare (state : State graph) (material : Option (Raw L)) :=
      submitStep (Submission.register
        ⟨.commitment event (owner, .prepared serial), material⟩ state owner) owner
          (.commitment event (owner, .prepared serial))
    PreparedBindingResult (prepare left opening) (prepare right replacement)
      (owner, .prepared serial) payload := by
  intro replacement prepare
  let nativeLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
    MessageNetwork.completePendingObservation
  have result (state : State graph) (material : Option (Raw L))
      (fresh : state.candidates.lookup (owner, .prepared serial) = .fresh) :
      (prepare state material).bindingResult (owner, .prepared serial) payload =
        (material.bind fun raw => raw.as? payload).elim .failure PublicationResult.success :=
    runtime.submitted_bindingResult nativeLeaks
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication nativeLeaks) state)
        owner event payload serial material fresh
  have firstFixed : (prepare left opening).candidates.lookup
      (owner, .prepared serial) ≠ .fresh := submitStep_commitment_fixed _ _ _ _
  have secondFixed : (prepare right replacement).candidates.lookup
      (owner, .prepared serial) ≠ .fresh := submitStep_commitment_fixed _ _ _ _
  refine ⟨firstFixed, secondFixed, ?_, ?_⟩
  · cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        refine ⟨L.someValue payload, ?_⟩
        rw [result right replacement rightFresh]
        simp only [replacement, decoded, Option.bind_some, Raw.as?_mk, Option.elim_some]
    | some value =>
        refine ⟨value, ?_⟩
        rw [result right replacement rightFresh]
        simp only [replacement, decoded, Option.elim_some]
  · intro value successful
    rw [result left opening leftFresh] at successful
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        simp only [decoded, Option.elim_none] at successful
        cases successful
    | some original =>
        rw [result right replacement rightFresh]
        simpa only [replacement, decoded, Option.elim_some] using successful

end Vegas.EventGraphRuntime.BindingShadow
