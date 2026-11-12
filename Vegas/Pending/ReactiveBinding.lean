module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveSafety
public import Vegas.Pending.ReactiveStateInvariant

@[expose] public section

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
theorem fixedCandidateLookupInvariant (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (original : State graph) (candidate : Handle graph)
    (fixed : original.candidates.lookup candidate ≠ .fresh) :
    ((reactiveApplication timeouts) leaks).Invariant (fun state =>
      state.candidates.lookup candidate = original.candidates.lookup candidate) := by
  let app := (reactiveApplication timeouts) leaks
  constructor
  · intro state actor material same
    exact ((reactive_respond_candidate_fixed timeouts) leaks (.initial app state) actor
      ⟨some material⟩ candidate (by
        change state.candidates.lookup candidate ≠ .fresh
        rwa [same])).trans same
  · intro state message target same accepted
    obtain ⟨native, handled, targetEq⟩ := reactiveHandle_call accepted
    rw [← targetEq, native.drain_tables.2.1]
    exact (handle_lookup_of_not_fresh timeouts state native
      ⟨message.id, message.payload.call⟩ candidate (by rwa [same]) handled).trans same
  · intro state command target same supported
    rw [(reactiveApplication_environment_tables timeouts leaks state target command supported).2]
    exact same

end Vegas.EventGraphRuntime
