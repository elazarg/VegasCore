/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveService

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
def bindingTraffic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (execution : (runtime.reactiveApplication leaks).Execution) :=
  (execution.network, execution.receipts, execution.environmentRecall, execution.recall focal,
    execution.application.playerView focal, execution.application.publicView)

end Vegas.EventGraphRuntime
