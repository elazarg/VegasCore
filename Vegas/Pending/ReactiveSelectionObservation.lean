/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveContinuationObservation

/-! # Reconstructing reserved selection from an owner's information

With at most one distinct owner envelope addressed to an event, arbitrary
foreign traffic changes no reserved choice. Its identity is determined by own
output recall and the publicly recorded envelope identities.
-/

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem reactive_respond_playerView_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (views : left.application.playerView who = right.application.playerView who) :
    (left.respond (runtime.reactiveApplication leaks) who response).application.playerView who =
      (right.respond (runtime.reactiveApplication leaks) who response).application.playerView
        who := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact views
  | some material =>
      exact runtime.submit_playerView_congr leaks left.application right.application who
        material views

end Vegas.EventGraphRuntime
