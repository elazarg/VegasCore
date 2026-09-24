/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactiveRecall

/-! # A response alone gives other players no observation

Foreign submissions may register private candidates and append public network
inputs. A player sees them only through the explicit observation or inclusion
steps. Arbitrary forwarding and replay obey the same rule.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactive_response_other_input (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (actor observer : Player) (different : observer ≠ actor)
    (action : (runtime.reactiveApplication leaks).Action) :
    ((execution.respond (runtime.reactiveApplication leaks) actor action).recall observer,
      (execution.respond (runtime.reactiveApplication leaks) actor action).observe
        (runtime.reactiveApplication leaks) observer) =
      (execution.recall observer,
        execution.observe (runtime.reactiveApplication leaks) observer) := by
  apply Prod.ext
  · exact (runtime.reactiveApplication leaks).respond_recall_other
      execution actor observer different action
  · rcases action with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some transmission =>
        cases transmission with
        | replay id =>
            cases found : (execution.network.known actor).find?
                (fun envelope => envelope.id = id) <;>
              simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
            all_goals rfl
        | submit material =>
            have framed := (submitStep_playerView_other
              (material.call.register execution.application actor) actor observer different
                material.call.packet).trans
                  (material.call.register_other execution.application actor observer different)
            have projected := congrArg (fun view : PlayerView graph =>
              (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
                ReactivePlayerView graph)) framed
            change ReactiveApplication.PlayerView.mk (app := runtime.reactiveApplication leaks)
              _ _ _ = _
            exact congrArg (fun observed =>
              (⟨execution.network.observe observer, observed, execution.receipts⟩ :
                (runtime.reactiveApplication leaks).PlayerView)) projected

end Vegas.EventGraphRuntime
