/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveService
import Vegas.Pending.EventCompletionObservation

/-! # Actual communication likelihood during an opaque binding window

The auxiliary projection retains the complete network, service recall, and
focal private input. Other players' private submission parameters are absent
from this proof projection. They remain in actual runtime recall. A shared
passive sample couples the silent response windows without an assumption
on the observation rule.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Existing native fields sufficient for the silent window's joint law.
This is a proof readout; it is not a player's observation or extra state. -/
def bindingTraffic (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (execution : ((reactiveApplication timeouts) leaks).Execution) :=
  (execution.network, execution.receipts, execution.environmentRecall, execution.logs focal,
    execution.application.playerView focal, execution.application.publicView)

/-- Automatic completion preserves equality of the existing native traffic readout. -/
theorem bindingTraffic_drain (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : ((reactiveApplication timeouts) leaks).Execution) (focal : Player)
    (same : (bindingTraffic timeouts) leaks focal left = (bindingTraffic timeouts) leaks focal
      right) :
    (bindingTraffic timeouts) leaks focal {left with application := left.application.drain} =
      (bindingTraffic timeouts) leaks focal {right with application := right.application.drain}
        := by
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun value => value.2.1) same
  have environments := congrArg (fun value => value.2.2.1) same
  have recalled := congrArg (fun value => value.2.2.2.1) same
  have views := congrArg (fun value => value.2.2.2.2.1) same
  have drained := State.drain_playerView_congr left.application right.application focal views
  exact Prod.ext networks (Prod.ext receipts (Prod.ext environments (Prod.ext recalled
    (Prod.ext drained (congrArg PlayerView.publicView drained)))))

end Vegas.EventGraphRuntime
