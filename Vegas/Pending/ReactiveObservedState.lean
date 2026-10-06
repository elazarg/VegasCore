/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventHandleObservation

/-! # Observable application transitions

The reactive local observation carries exactly the authenticated player
projection of the application state. The actual reactive observation therefore
suffices for the existing owner-local packet-handling law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The authenticated player projection carried by a reactive observation. -/
def ReactivePlayerView.toPlayerView (view : ReactivePlayerView graph) : PlayerView graph where
  who := view.who
  publicView := view.publicView
  observation := view.observation
  candidates := view.candidates

theorem reactive_playerView_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : State graph) (who : Player)
    (views : (runtime.reactiveApplication leaks).observePlayer left who =
      (runtime.reactiveApplication leaks).observePlayer right who) :
    left.playerView who = right.playerView who :=
  congrArg ReactivePlayerView.toPlayerView views

theorem reactive_handle_observation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : State graph) (who : Player) (message : Message Player (Payload graph))
    (views : (runtime.reactiveApplication leaks).observePlayer left who =
      (runtime.reactiveApplication leaks).observePlayer right who)
    (sender : message.sender = who) :
    (handle runtime left message).map (fun state => state.playerView who) =
      (handle runtime right message).map (fun state => state.playerView who) :=
  handle_playerView_congr_of_sender runtime left right who message
    (reactive_playerView_congr runtime leaks left right who views) sender

end Vegas.EventGraphRuntime
