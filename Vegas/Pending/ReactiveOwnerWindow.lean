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

theorem bindingTraffic_owner_response (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : ((reactiveApplication timeouts) leaks).Execution) (owner : Player)
    (same : (bindingTraffic timeouts) leaks owner left = (bindingTraffic timeouts) leaks owner
      right)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    (bindingTraffic timeouts) leaks owner
        (left.respond ((reactiveApplication timeouts) leaks) owner response) =
      (bindingTraffic timeouts) leaks owner
        (right.respond ((reactiveApplication timeouts) leaks) owner response) := by
  let app := (reactiveApplication timeouts) leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.logs owner = right.logs owner :=
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
    exact (packet_playerView_congr timeouts) leaks left.application right.application owner _
      submission views
  have afterRecall := app.respond_focal_recall_eq left right owner owner response
    networks observed recalled (fun submission _ => packet submission)
  have afterViews := (reactive_respond_playerView_congr timeouts) leaks left right owner response
    views
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
