/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameStep

/-! # Actual disclosure expiry during private binding repair

Silence at a disclosure settles by the existing public deadline operation.
The two executions keep the same publication failure and service record even
when the underlying private bindings have different meanings.
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

/-- The due resolve command has an explicit deterministic joint law. Its
failure is independent of both hidden bindings and every deferred guard. -/
theorem expire_resolution (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (event : graph.EventId) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (ready : original.application.config.cut.Ready event)
    (entered : Nat) (activated : original.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ original.application.clock - entered) :
    let app := runtime.reactiveApplication leaks
    ∃ left right,
      original.environmentStep app (.application (.expire event)) = PMF.pure left ∧
      repaired.environmentStep app (.application (.expire event)) = PMF.pure right ∧
      Frame runtime leaks memory owner left right := by
  let app := runtime.reactiveApplication leaks
  have rightReady : repaired.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
    exact ready
  have clocks : original.application.clock = repaired.application.clock :=
    congrArg PublicView.clock frame.publicView
  have enteredEq : original.application.activatedAt = repaired.application.activatedAt :=
    congrArg PublicView.activatedAt frame.publicView
  have rightActivated : repaired.application.activatedAt event = some entered := by
    rw [← enteredEq]
    exact activated
  have rightDue : runtime.deadline event ≤ repaired.application.clock - entered := by
    rwa [← clocks]
  let action : graph.Action event := cast (congrArg EventField.Action outputEq.symm) false
  let value : (graph.outputLayout event).Value :=
    cast (congrArg EventField.Value outputEq.symm)
      (PublicationResult.failure : PublicationResult (L.Val payload))
  let left : app.Execution :=
    { original with
      application := original.application.complete event ready action value
      environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .application (.expire event)⟩] }
  let right : app.Execution :=
    { repaired with
      application := repaired.application.complete event rightReady action value
      environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .application (.expire event)⟩] }
  have first : original.environmentStep app (.application (.expire event)) = PMF.pure left := by
    change ((environmentStep runtime original.application (.expire event)).map _).map _ = _
    rw [environmentStep_expire_resolve_eq runtime original.application event ready entered
      activated due actor payload binding checks outputEq codeEq node,
        PMF.pure_map, PMF.pure_map]
  have second : repaired.environmentStep app (.application (.expire event)) =
      PMF.pure right := by
    change ((environmentStep runtime repaired.application (.expire event)).map _).map _ = _
    rw [environmentStep_expire_resolve_eq runtime repaired.application event rightReady entered
      rightActivated rightDue actor payload binding checks outputEq codeEq node,
        PMF.pure_map, PMF.pure_map]
  have visible : (graph.outputLayout event).IsPublic := by rw [outputEq]; trivial
  have paired := frame.complete_unmodified event ready rightReady
    (onlyBindings.public_value_none (.inr event) visible)
    (onlyBindings.public_action_none event visible) action value
  exact ⟨left, right, first, second, { paired with
    service := by
      change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
      rw [frame.service, frame.environment] }⟩

end Vegas.EventGraphRuntime.BindingMemory.Frame
