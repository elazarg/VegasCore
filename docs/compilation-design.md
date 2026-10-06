# Compilation boundary

The [source compiler](../Vegas/Compile/EventGraphCompiler.lean) lowers a typed
source program to a typed event graph. Observation and readout adapters connect
source histories and values to graph execution. Public samples retain their
conditional kernels; private inputs remain owner-private; binding and resolution
remain distinct actions.

The [pending application](../Vegas/Pending/EventApplication.lean) separates
private candidate material, signed public submission and inclusion. A public
builder controls activations, inclusion, clock advancement and expiry. Player
policies see their own recall, public application state, receipts and genuinely
observed packets. They do not see unsampled pending messages or the builder's
hidden history.

The [canonical client](../Vegas/Pending/ReactiveCanonicalDecision.lean) implements
source FALSE or failed validation by silence followed by
ordinary FALSE expiry. The contract has no withholding packet, so silence is
the only way to withhold. Packet-free resolution expiry is not a
binding-omission charge.
WAIT therefore need not represent a deviation from the source prescription.

A runtime compiler result needs three kinds of evidence: executable source
correspondence, preservation of the information used by strategies, and actual
continuation payoff comparisons. Correct final values establish only the first.
A retained response menu is a proof restriction; it cannot be imposed on raw
players without a valid equilibrium-extension argument.

The [checked calendar stack](se-compilation-stack.md) supplies these edges for
one service. The [asynchronous plan](se-schedule-generalization.md) states how to
extend that result while retaining the baseline semantics.
