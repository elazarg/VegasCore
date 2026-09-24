/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventHandleObservation

/-! # Observable application transitions without a strategic scratch cache

Reactive responses never alter the application intention table. Its
initial value remains fixed, so the actual reactive observation suffices for
the existing owner-local packet-handling law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveRememberedInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (table : RememberedActions graph) : (runtime.reactiveApplication leaks).Invariant
      (fun state => state.remembered = table) where
  submit state who material fixed := by
    change (submitStep (material.register state who) who material.packet).remembered = table
    rw [submitStep_remembered, (material.register_facts who state).2.1]
    exact fixed
  handle state message next fixed accepted :=
    (handle_remembered runtime state next message accepted).trans fixed
  environment state command next fixed reached :=
    (environmentStep_remembered runtime state next command reached).trans fixed

def ReactivePlayerView.withRemembered (view : ReactivePlayerView graph)
    (table : RememberedActions graph) : PlayerView graph where
  who := view.who
  publicView := view.publicView
  observation := view.observation
  remembered event := if graph.actor? event = some view.who then table event else none
  candidates := view.candidates

theorem reactive_playerView_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (left right : State graph) (who : Player)
    (views : (runtime.reactiveApplication leaks).observePlayer left who =
      (runtime.reactiveApplication leaks).observePlayer right who)
    (remembered : left.remembered = right.remembered) :
    left.playerView who = right.playerView who := by
  have same := congrArg (fun view => view.withRemembered left.remembered) views
  calc
    left.playerView who = ReactivePlayerView.withRemembered
        ((runtime.reactiveApplication leaks).observePlayer left who) left.remembered := rfl
    _ = ReactivePlayerView.withRemembered
        ((runtime.reactiveApplication leaks).observePlayer right who) left.remembered := same
    _ = right.playerView who := by rw [remembered]; rfl

theorem reactive_handle_observation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (left right : State graph) (who : Player) (message : Message Player (Payload graph))
    (views : (runtime.reactiveApplication leaks).observePlayer left who =
      (runtime.reactiveApplication leaks).observePlayer right who)
    (remembered : left.remembered = right.remembered) (sender : message.sender = who) :
    (handle runtime left message).map (fun state => state.playerView who) =
      (handle runtime right message).map (fun state => state.playerView who) :=
  handle_playerView_congr_of_sender runtime left right who message
    (reactive_playerView_congr runtime leaks left right who views remembered) sender

end Vegas.EventGraphRuntime
