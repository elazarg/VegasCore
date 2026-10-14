/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionPublicRecord
import Vegas.Pending.ReactiveAcceptedOutput
import Vegas.Pending.EventBindingInvariant

/-! # Successful graph outputs exclude public failure evidence -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Vegas.EventGraph

variable {Player : Type} {L : IExpr}

private theorem cast_option_some {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

private theorem isFailure_cast {first second : EventField Player L} (same : first = second)
    (value : first.Value) :
    second.IsFailure (cast (congrArg EventField.Value same) value) ↔ first.IsFailure value := by
  cases same
  rfl

variable [DecidableEq Player] [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Successful binding provenance supplies an accepted handle; successful public
resolution results are not failed publications. -/
theorem OutputSucceeded.not_publicFailure {native : State graph} {event : graph.EventId}
    (succeeded : OutputSucceeded native.config.store event) (valid : native.BindingInvariant) :
    ¬ native.PublicFailure event := by
  classical
  rcases succeeded with ⟨value, stored, good⟩
  intro failed
  cases view : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      have notFailed : (cast (congrArg EventField.Value outputEq) value :
          PublicationResult (L.Val payload)) ≠ .failure := by
        intro bad
        exact good ((isFailure_cast outputEq value).mp bad)
      let ref : FieldRef graph.layout (.binding owner payload) := ⟨.inr event, outputEq⟩
      have read : ref.get? native.config.store =
          some (cast (congrArg EventField.Value outputEq) value) := by
        change cast (congrArg Option (congrArg EventField.Value outputEq))
          (native.config.store (.inr event)) = _
        rw [stored]
        exact cast_option_some _ _
      cases converted : cast (congrArg EventField.Value outputEq) value with
      | failure => exact notFailed converted
      | success opening =>
          rw [converted] at read
          obtain ⟨candidate, accepted, _, _⟩ := valid.success_provenance ref opening read
          rcases failed with missed | publication
          · have acceptedAt : native.publicView.accepted (.inr event) = some candidate := accepted
            rw [native.publicView.missedBinding_of_accepted event candidate acceptedAt] at missed
            cases missed
          · simp only [RecoveryState.publicationFailed, view, Bool.false_eq_true] at publication
  | resolve owner payload binding checks outputEq codeEq =>
      rcases failed with missed | publication
      · simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missed
      · have notFailed : (cast (congrArg EventField.Value outputEq) value :
            PublicationResult (L.Val payload)) ≠ .failure := by
          intro bad
          exact good ((isFailure_cast outputEq value).mp bad)
        have output : native.config.outputs event = some value := stored
        rw [RecoveryState.publicationFailed, view, output] at publication
        cases converted : cast (congrArg EventField.Value outputEq) value with
        | failure => exact notFailed converted
        | success opening => simp only [converted, Bool.false_eq_true] at publication
  | sample payload law outputEq codeEq =>
      rcases failed with missed | publication
      · simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missed
      · simp only [RecoveryState.publicationFailed, view, Bool.false_eq_true] at publication

end Vegas.EventGraphRuntime
