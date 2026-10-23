/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingSchedule
import Vegas.Pending.ReactiveSelectionObservation

/-! # Owner information during an unsettled service window

The owner's actual policy can depend on its entire input and response recall.
When other players respond silently, equal complete focal traffic
induces equal traffic laws through any finite roster. Passive samples, prepared
private material and authentic emitted evidence are retained by this equality.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem bindingTraffic_owner_response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (same : runtime.bindingTraffic leaks owner left = runtime.bindingTraffic leaks owner right)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.bindingTraffic leaks owner
        (left.respond (runtime.reactiveApplication leaks) owner response) =
      runtime.bindingTraffic leaks owner
        (right.respond (runtime.reactiveApplication leaks) owner response) := by
  let app := runtime.reactiveApplication leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall owner = right.recall owner :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView owner = right.application.playerView owner :=
    congrArg (fun value => value.2.2.2.2.1) same
  have observed : left.observe app owner = right.observe app owner := by
    change ReactiveApplication.PlayerView.mk _ _ _ = _
    rw [networks]
    exact congrArg₂ (fun view evidence =>
      (⟨right.network.observe owner, view, evidence⟩ : app.PlayerView)) views receipts
  have packet (submission : WitnessedSubmission graph) :
      app.packet (app.submit left.application owner submission) owner
          (left.network.known owner) submission =
        app.packet (app.submit right.application owner submission) owner
          (right.network.known owner) submission := by
    rw [networks]
    exact runtime.packet_playerView_congr leaks left.application right.application owner _
      submission views
  have afterRecall := app.respond_focal_recall_eq left right owner owner response
    networks observed recalled (fun submission _ => packet submission)
  have afterViews := runtime.reactive_respond_playerView_congr leaks left right owner response views
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments
    (Prod.ext afterRecall (Prod.ext afterViews (congrArg PlayerView.publicView afterViews)))))
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact networks
  | some submission =>
      change (left.network.submit owner (app.packet
        (app.submit left.application owner submission) owner
          (left.network.known owner) submission)).2 = _
      rw [packet, networks]
      rfl

end Vegas.EventGraphRuntime
