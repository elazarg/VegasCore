/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveDisclosure

/-! # Canonical revelation blocks in the existing reactive service

A source revelation chooses a certified opening or silence. Reserved inclusion
then consumes the sole opening packet; silence leaves expiry to resolve the
event. The equations concern actual executions and retain network and recall
effects. They do not restrict the raw response menu or assume player optimality.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The two source choices, using matching owned evidence on the opening branch.
Withholding emits no packet and is completed by the existing expiry command. -/
def canonicalRevealResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) (disclose : Bool) :
    (runtime.reactiveApplication leaks).Action :=
  ⟨if disclose then some (disclosureSubmission (.opening event candidate raw))
    else none⟩

end Vegas.EventGraphRuntime
