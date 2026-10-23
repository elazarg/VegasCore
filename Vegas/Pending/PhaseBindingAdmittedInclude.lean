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

end Vegas.EventGraphRuntime.PhaseBindingRepair
