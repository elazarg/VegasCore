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
source FALSE, and TRUE whose owner-local validation fails, by an authenticated
evidence-free withholding packet, which completes the resolution with FALSE on
inclusion. The [final-record audit](../Vegas/Pending/ReactiveSettledVerdict.lean)
permits an accepted withholding packet that carries no evidence. Silence is WAIT,
an undecided owner. Expiry of a strategic event without an accepted decision
executes source FALSE or binding failure and records a public decision miss
(`Vegas.EventGraphRuntime.PublicView.missedDecisionBy`), which the
[service audit](../Vegas/Pending/ReactiveServiceAudit.lean) charges like a
binding omission.

A runtime compiler result needs three kinds of evidence: executable source
correspondence, preservation of the information used by strategies, and actual
continuation payoff comparisons. Correct final values establish only the first.
A retained response menu is a proof restriction; it cannot be imposed on raw
players without a valid equilibrium-extension argument.

The [checked calendar stack](se-compilation-stack.md) supplies these edges for
one service. The [asynchronous plan](se-schedule-generalization.md) states how to
extend that result while retaining the baseline semantics.
