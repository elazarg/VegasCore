/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSchedule
import Vegas.Pending.ReactiveSelectionObservation

/-! # Owner information during an unsettled service window

The owner's actual policy can depend on its entire input and response recall.
When other players only replay known packets, equal complete focal traffic
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
    have projected := congrArg (fun view : PlayerView graph =>
      (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
        ReactivePlayerView graph)) views
    change ReactiveApplication.PlayerView.mk _ _ _ = _
    rw [networks]
    exact congrArg₂ (fun view evidence =>
      (⟨right.network.observe owner, view, evidence⟩ : app.PlayerView)) projected receipts
  have packet (submission : WitnessedSubmission graph) :
      app.packet (app.submit left.application owner submission) owner
          (left.network.known owner) submission =
        app.packet (app.submit right.application owner submission) owner
          (right.network.known owner) submission := by
    have submitted := runtime.submit_playerView_congr leaks left.application
      right.application owner submission views
    change submission.emit (app.submit left.application owner submission) owner
        (left.network.known owner) =
      submission.emit (app.submit right.application owner submission) owner
        (right.network.known owner)
    rw [WitnessedSubmission.emit_eq_resolve, WitnessedSubmission.emit_eq_resolve, networks]
    exact congrArg (fun table => WitnessedPacket.mk submission.call.packet
      (submission.evidence.resolve owner table (right.network.known owner)))
        (congrArg PlayerView.candidates submitted)
  have afterRecall := app.respond_focal_recall_eq left right owner owner response
    networks observed recalled (fun submission _ => packet submission)
  have afterViews := runtime.reactive_respond_playerView_congr leaks left right owner response views
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments
    (Prod.ext afterRecall (Prod.ext afterViews (congrArg PlayerView.publicView afterViews)))))
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact networks
  | some transmission =>
      cases transmission with
      | replay id =>
          change (left.network.replay owner id).2 = (right.network.replay owner id).2
          rw [networks]
      | submit submission =>
          change (left.network.submit owner (app.packet
            (app.submit left.application owner submission) owner
              (left.network.known owner) submission)).2 = _
          rw [packet, networks]
          rfl

/-- Any actual owner policy preserves the source-conditioned auxiliary
channel before protected settlement. The other players retain the full replay
law, including unpublished packets and arbitrary passive sampling. -/
theorem owner_window_focal_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player) (owner : Player)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (same : runtime.bindingTraffic leaks owner left = runtime.bindingTraffic leaks owner right) :
    let app := runtime.reactiveApplication leaks
    let players := Function.update (fun _ => app.replayPolicy) owner policy
    ((runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player) left).map (runtime.bindingTraffic leaks owner)) =
      ((runtime.runInteractionPlan leaks players network
        (roster.map ServiceInstruction.player) right).map
          (runtime.bindingTraffic leaks owner)) := by
  intro app players
  induction roster generalizing left right with
  | nil => simpa only [List.map_nil, runInteractionPlan, FinDist.map_pure] using
      congrArg FinDist.pure same
  | cons actor rest ih =>
      have networks : left.network = right.network := congrArg Prod.fst same
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.map_bind,
        FinDist.bind_map, FinDist.bind_bind]
      rw [networks]
      apply FinDist.bind_congr
      intro sample _
      let before := left.sampledActivation app actor sample
      let after := right.sampledActivation app actor sample
      have beforeRecall : before.InputRecall app := leftRecall
      have afterRecall : after.InputRecall app := rightRecall
      have matched := runtime.bindingTraffic_activation leaks left right owner actor same sample
      change (players actor (before.recall actor) (before.observe app actor)).bind _ =
        (players actor (after.recall actor) (after.observe app actor)).bind _
      by_cases acts : actor = owner
      · subst actor
        have recalls : before.recall owner = after.recall owner :=
          congrArg (fun value => value.2.2.2.1) matched
        have views : before.observe app owner = after.observe app owner := by
          have known : before.network = after.network := congrArg Prod.fst matched
          have receipts : before.receipts = after.receipts :=
            congrArg (fun value => value.2.1) matched
          have privateViews : before.application.playerView owner =
              after.application.playerView owner :=
            congrArg (fun value => value.2.2.2.2.1) matched
          have projected := congrArg (fun view : PlayerView graph =>
            (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
              ReactivePlayerView graph)) privateViews
          change ReactiveApplication.PlayerView.mk _ _ _ = _
          rw [known]
          exact congrArg₂ (fun view evidence =>
            (⟨after.network.observe owner, view, evidence⟩ : app.PlayerView)) projected receipts
        rw [recalls, views]
        apply FinDist.bind_congr
        intro response _
        exact ih _ _ (app.respond_inputRecall before owner response beforeRecall)
          (app.respond_inputRecall after owner response afterRecall)
          (runtime.bindingTraffic_owner_response leaks before after owner matched response)
      · have replay := app.replayPolicy_eq_of_network_eq before after actor
          beforeRecall afterRecall (congrArg Prod.fst matched)
        simp only [players, Function.update_of_ne acts]
        rw [replay]
        apply FinDist.bind_congr
        intro response supported
        exact ih _ _ (app.respond_inputRecall before actor response beforeRecall)
          (app.respond_inputRecall after actor response afterRecall)
          (runtime.bindingTraffic_replay leaks before after owner actor matched response
            (app.replayPolicy_cases _ _ response supported))

end Vegas.EventGraphRuntime
