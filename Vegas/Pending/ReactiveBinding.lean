/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveSafety
import Vegas.Pending.ReactiveStateInvariant

/-! # Compiled bindings across arbitrary intervening interaction

A compiled response fixes its selected binding before the envelope becomes
observable. Arbitrary later responses, passive leaks, inclusions and application
commands preserve that meaning. If the original packet is eventually included
at an admissible opportunity, it performs exactly that graph action.

The theorem does not coalesce submission with inclusion. Nor does it guarantee
which packet is selected, or that an admissible opportunity remains available.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every operation preserves a previously fixed candidate lookup. -/
theorem fixedCandidateLookupInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (original : State graph) (candidate : Handle graph)
    (fixed : original.candidates.lookup candidate ≠ .fresh) :
    (runtime.reactiveApplication leaks).Invariant (fun state =>
      state.candidates.lookup candidate = original.candidates.lookup candidate) := by
  let app := runtime.reactiveApplication leaks
  constructor
  · intro state actor material same
    exact (runtime.reactive_respond_candidate_fixed leaks (.initial app state) actor
      ⟨some material⟩ candidate (by
        change state.candidates.lookup candidate ≠ .fresh
        rwa [same])).trans same
  · intro state message target same accepted
    exact (handle_lookup_of_not_fresh runtime state target
      ⟨message.id, message.payload.call⟩ candidate (by rwa [same])
      (reactiveHandle_call accepted)).trans same
  · intro state command target same supported
    rw [(environmentStep_tables runtime state target command supported).2]
    exact same

end Vegas.EventGraphRuntime
