/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSampleReplay

/-! # Actual admitted packet effects before clear phase installation -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Failed publications are public even when unexposed bindings differ. -/
theorem publicationFailed_congr (left right : State graph)
    (same : left.publicView = right.publicView) (event : graph.EventId) :
    RecoveryState.publicationFailed left event = RecoveryState.publicationFailed right event := by
  cases node : nodeView graph event with
  | bind owner payload outputEq codeEq => simp only [RecoveryState.publicationFailed, node]
  | sample payload law outputEq codeEq => simp only [RecoveryState.publicationFailed, node]
  | resolve owner payload binding checks outputEq codeEq =>
      have visible : graph.fieldPublic (.inr event) := by
        change (graph.outputLayout event).IsPublic
        rw [outputEq]
        trivial
      have observed := congrFun (congrArg (fun view : PublicView graph =>
        view.observation.store) same) (.inr event)
      change graph.publicStore left.config.store (.inr event) =
        graph.publicStore right.config.store (.inr event) at observed
      rw [graph.publicStore_of_public _ _ visible, graph.publicStore_of_public _ _ visible]
        at observed
      change left.config.outputs event = right.config.outputs event at observed
      simp only [RecoveryState.publicationFailed, node, observed]

/-- Inclusion's permanent exclusion update depends only on the public result
and the inherited exclusion set, never on a private accepted binding value. -/
theorem inclusion_exclusion_congr (left right : RecoveryState graph)
    (same : left.excluded = right.excluded) (leftNative rightNative : State graph)
    (publics : leftNative.publicView = rightNative.publicView) (call : Payload graph) :
    (left.inclusionResult call leftNative).excluded =
      (right.inclusionResult call rightNative).excluded := by
  cases call with
  | commitment event candidate => exact same
  | malformed raw => exact same
  | opening event candidate raw =>
      change (if RecoveryState.publicationFailed leftNative event then
        RecoveryState.excludeEvent left.excluded event else left.excluded) = _
      rw [publicationFailed_congr leftNative rightNative publics event, same]
      rfl

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Actual clear survival determines the raw exclusion update before phase
normalization. This is derived from the original physical include outcome. -/
theorem inclusion_clear_of_actual
    (physical : (phaseApplication runtime leaks).Execution) (id : MessageId Player)
    (message : Message Player (CommitAttemptPacket graph))
    (found : physical.network.lookup id = some message)
    (admitted : (message.payload.tokenValid physical.application.attempt &&
      physical.application.allows message.payload.packet.call &&
      !physical.application.current.excludedCall message.payload.packet.call) = true)
    (native : State graph)
    (handled : handle runtime physical.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native)
    (clear : (physical.includePending (phaseApplication runtime leaks)
      id).application.current.excluded = ∅) :
    (physical.application.current.inclusionResult message.payload.packet.call native).excluded =
      ∅ := by
  let raw : PhaseRuntimeState graph := { physical.application with
    current := physical.application.current.inclusionResult message.payload.packet.call native }
  have accepted : (phaseApplication runtime leaks).handle physical.application message =
      some raw.normalize := by
    change physical.application.handle runtime message = some raw.normalize
    simp only [PhaseRuntimeState.handle, admitted, ↓reduceIte, handled, Option.map_some]
    rfl
  have cleared : raw.normalize.current.excluded = ∅ := by
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted, Option.getD_some] using clear
  have same := (PhaseRuntimeState.settle_physical physical.application.phases
    physical.application.generation physical.application.entry
    (physical.application.current.inclusionResult message.payload.packet.call native)
    physical.application.retired).1
  exact same.symm.trans cleared

end Vegas.EventGraphRuntime.PhaseBindingRepair
