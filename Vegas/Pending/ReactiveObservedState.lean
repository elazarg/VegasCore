/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventHandleObservation

/-! # Observable application transitions

The reactive local observation is the authenticated player view of the
application state, so it suffices for the owner-local packet-handling law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactive_handle_observation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : State graph) (who : Player) (message : Message Player (Payload graph))
    (views : (runtime.reactiveApplication leaks).observePlayer left who =
      (runtime.reactiveApplication leaks).observePlayer right who)
    (sender : message.sender = who) :
    (handle runtime left message).map (fun state => state.playerView who) =
      (handle runtime right message).map (fun state => state.playerView who) :=
  handle_playerView_congr_of_sender runtime left right who message views sender

end Vegas.EventGraphRuntime
