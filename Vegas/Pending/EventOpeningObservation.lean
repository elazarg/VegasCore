/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPolicies

/-! # Resolution packet observation locality -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem resolveOutput_false_ne_success
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (store : Store graph.layout) (value : L.Val payload) :
    EventCode.resolveOutput? binding checks false store ≠ some (.success value) := by
  unfold EventCode.resolveOutput?
  cases bound : binding.get? store with
  | none => simp
  | some result =>
      cases accepted : GuardCheck.allAccepted? checks store .failure <;> simp [accepted]

/-- Resolution packet selection depends only on the effective publication
result and the public accepted handle at the referenced binding. In
particular, a private `false` action and a guard-rejected `true` action both
produce the same canonical withholding packet. -/
theorem resolutionPayload_eq_of_effectiveResult_eq
    (runtime : EventGraphRuntime graph)
    {owner : Player} (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (leftAction rightAction : graph.Action event)
    (leftView rightView : runtime.application.View)
    (accepted : leftView.application.publicView.accepted binding.field =
      rightView.application.publicView.accepted binding.field)
    (effective :
      EventCode.resolveOutput? binding checks
          (cast (congrArg EventField.Action outputEq) leftAction)
          leftView.application.observation.store =
        EventCode.resolveOutput? binding checks
          (cast (congrArg EventField.Action outputEq) rightAction)
          rightView.application.observation.store) :
    runtime.resolutionPayload who event payload binding checks outputEq leftAction leftView =
      runtime.resolutionPayload who event payload binding checks outputEq
        rightAction rightView := by
  unfold resolutionPayload
  generalize leftDisclose :
    cast (congrArg EventField.Action outputEq) leftAction = ld at effective
  generalize rightDisclose :
    cast (congrArg EventField.Action outputEq) rightAction = rd at effective
  cases ld <;> cases rd
  · rfl
  · simp only [ite_true]
    cases rightResult : EventCode.resolveOutput? binding checks true
        rightView.application.observation.store with
    | none => rfl
    | some result =>
        cases result with
        | failure => rfl
        | success value =>
            have impossible := resolveOutput_false_ne_success binding checks
              leftView.application.observation.store value
            exact (impossible (effective.trans rightResult)).elim
  · simp only [ite_true]
    cases leftResult : EventCode.resolveOutput? binding checks true
        leftView.application.observation.store with
    | none => rfl
    | some result =>
        cases result with
        | failure => rfl
        | success value =>
            have impossible := resolveOutput_false_ne_success binding checks
              rightView.application.observation.store value
            exact (impossible (effective.symm.trans leftResult)).elim
  · simp only [ite_true]
    cases leftResult : EventCode.resolveOutput? binding checks true
        leftView.application.observation.store with
    | none =>
        have rightResult := effective.symm.trans leftResult
        rw [rightResult]
    | some leftResultValue =>
        cases leftResultValue with
        | failure =>
            have rightResult := effective.symm.trans leftResult
            rw [rightResult]
        | success value =>
            have rightResult := effective.symm.trans leftResult
            rw [rightResult, accepted]

/-- A withheld private action and a disclosed action rejected by the guards
have identical wire representations. No availability premise is needed here:
the false branch does not inspect the store at all. -/
theorem resolutionPayload_false_eq_rejected
    (runtime : EventGraphRuntime graph)
    {owner : Player} (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (falseAction trueAction : graph.Action event)
    (falseView trueView : runtime.application.View)
    (withholds : cast (congrArg EventField.Action outputEq) falseAction = false)
    (discloses : cast (congrArg EventField.Action outputEq) trueAction = true)
    (rejected : EventCode.resolveOutput? binding checks true
      trueView.application.observation.store = some .failure) :
    runtime.resolutionPayload who event payload binding checks outputEq falseAction falseView =
      runtime.resolutionPayload who event payload binding checks outputEq trueAction trueView := by
  simp [resolutionPayload, withholds, discloses, rejected]

end Vegas.EventGraphRuntime
