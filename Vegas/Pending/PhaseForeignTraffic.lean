/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseTraffic
import Vegas.Pending.PhasePreparedBinding

/-! # Foreign private binding choices preserve focal phase traffic

At a shared physical slot, the complete focal traffic does not depend on a
foreign binding's hidden typed result. This statement includes the entire
network, receipts, environmental recall, focal recall and focal phase view.
It does not assert that two independently selected slots coincide.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem foreign_submit_view (state : PhaseRuntimeState graph) (actor focal : Player)
    (different : focal ≠ actor) (material : WitnessedSubmission graph) :
    ((app).submit state actor material).playerView focal = state.playerView focal := by
  apply Prod.ext
  · exact (submitStep_playerView_other (material.call.register state.current.native actor)
      actor focal different material.call.packet).trans
        (material.call.register_other state.current.native actor focal different)
  · exact PhaseCount.submit_publicView state actor material

/-- Foreign preparations with the same actual emitted packet preserve the
whole focal traffic. Their private material and their author's recall may differ. -/
theorem phaseTraffic_foreign_submission (left right : (app).Execution) (focal actor : Player)
    (different : focal ≠ actor)
    (same : phaseTraffic runtime leaks focal left = phaseTraffic runtime leaks focal right)
    (first second : WitnessedSubmission graph)
    (packet : (app).packet ((app).submit left.application actor first) actor
        (left.network.known actor) first =
      (app).packet ((app).submit right.application actor second) actor
        (right.network.known actor) second) :
    phaseTraffic runtime leaks focal (left.respond (app) actor ⟨some first⟩) =
      phaseTraffic runtime leaks focal (right.respond (app) actor ⟨some second⟩) := by
  have network : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall focal = right.recall focal :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun value => value.2.2.2.2) same
  have afterRecall := ((app).respond_recall_other left actor focal different ⟨some first⟩).trans
    (recalled.trans ((app).respond_recall_other right actor focal different ⟨some second⟩).symm)
  have afterViews := (foreign_submit_view runtime leaks left.application actor focal different
    first).trans (views.trans
      (foreign_submit_view runtime leaks right.application actor focal different second).symm)
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments (Prod.ext afterRecall afterViews)))
  change (left.network.submit actor ((app).packet ((app).submit left.application actor first)
    actor (left.network.known actor) first)).2 = _
  rw [packet, network]
  rfl

/-- The same-slot binding branch is independent of the foreign typed result,
even without a freshness, readiness, admission or honesty premise. -/
theorem phaseTraffic_foreign_binding (left right : (app).Execution) (focal actor : Player)
    (different : focal ≠ actor)
    (same : phaseTraffic runtime leaks focal left = phaseTraffic runtime leaks focal right)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat) :
    phaseTraffic runtime leaks focal (left.respond (app) actor
      (phaseBindingResponse runtime leaks actor event payload first serial)) =
    phaseTraffic runtime leaks focal (right.respond (app) actor
      (phaseBindingResponse runtime leaks actor event payload second serial)) := by
  apply phaseTraffic_foreign_submission runtime leaks left right focal actor different same
  have publicEq : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView := congrArg PhasePublicView.native publicEq
  have attempts : left.application.attempt = right.application.attempt :=
    congrArg PhasePublicView.attempt publicEq
  change (left.application.submit actor _).emit actor _ _ =
    (right.application.submit actor _).emit actor _ _
  rw [PhaseCount.emit_after_submit, PhaseCount.emit_after_submit]
  simp only [EvidenceRequest.resolve]
  rw [publicEq, nativePublic, attempts]

/-- Any two foreign typed-result distributions have the same complete focal
traffic effect at a shared physical slot. -/
theorem phaseTraffic_foreign_binding_law (left right : (app).Execution) (focal actor : Player)
    (different : focal ≠ actor)
    (same : phaseTraffic runtime leaks focal left = phaseTraffic runtime leaks focal right)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PMF (PublicationResult (L.Val payload))) (serial : Nat) :
    (first.map fun result => phaseTraffic runtime leaks focal (left.respond (app) actor
      (phaseBindingResponse runtime leaks actor event payload result serial))) =
    (second.map fun result => phaseTraffic runtime leaks focal (right.respond (app) actor
      (phaseBindingResponse runtime leaks actor event payload result serial))) := by
  have constant (execution : (app).Execution)
      (law : PMF (PublicationResult (L.Val payload))) :
      (law.map fun result => phaseTraffic runtime leaks focal (execution.respond (app) actor
        (phaseBindingResponse runtime leaks actor event payload result serial))) =
      PMF.pure (phaseTraffic runtime leaks focal (execution.respond (app) actor
        (phaseBindingResponse runtime leaks actor event payload .failure serial))) := by
    calc
      _ = law.map (fun _ => phaseTraffic runtime leaks focal (execution.respond (app) actor
          (phaseBindingResponse runtime leaks actor event payload .failure serial))) := by
        apply map_congr_on_support _
        intro result _
        exact phaseTraffic_foreign_binding runtime leaks execution execution focal actor different
          rfl event payload result .failure serial
      _ = _ := PMF.map_const _ _
  rw [constant, constant,
    phaseTraffic_foreign_binding runtime leaks left right focal actor different same event payload
      .failure .failure serial]

end Vegas.EventGraphRuntime
