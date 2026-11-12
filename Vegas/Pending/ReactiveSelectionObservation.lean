module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveContinuationObservation

@[expose] public section

/-! # Reconstructing reserved selection from an owner's information

With at most one distinct owner envelope addressed to an event, arbitrary
foreign traffic changes no reserved choice. Its identity is determined by own
output recall and the publicly recorded envelope identities.
-/

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem reactive_respond_playerView_congr
    (left right : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (views : left.application.playerView who = right.application.playerView who) :
    (left.respond ((reactiveApplication timeouts) leaks) who response).application.playerView who =
      (right.respond ((reactiveApplication timeouts) leaks) who response).application.playerView
        who := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact views
  | some material =>
      exact (submit_playerView_congr timeouts) leaks left.application right.application who
        material views

end Vegas.EventGraphRuntime
