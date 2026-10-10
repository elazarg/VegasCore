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

The scheduler's public network view contains the entire pending pool, input
history, ledger and submission counters. A concrete backend with restricted
visibility must implement the chosen command law through its available
observation. The [observation adapter](../Interaction/ReactiveSchedulerObservation.lean)
states this factorization and preserves the complete finite execution law for
every raw player policy. The public pending lottery is one instance: it uses
only the set of pending identifiers. Support restriction alone does not
preserve command probabilities or beliefs.

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

The checked compiler entry point is the failure-aware `SourceProgram`.
The [surface prototype](../Vegas/Language/ToCore.lean) lowers to `SurfaceCore`
and has no verified translation into that entry point. Guard feasibility and
nullable values in the prototype do not specify source publication failures.
Such a bridge needs an explicit interpretation of failure and guard timing.
The separate [reactive graph-policy compiler](../Vegas/Pending/ReactivePolicy.lean)
also has an open observation-reconstruction and decision-realization obligation.
Its implementation is not an additional checked compilation theorem.
The [private-memory facts](../Vegas/Pending/ReactivePolicyFacts.lean) establish
alignment of supported intention memory with positive own recall and retention
through later responses. A recorded silent decision at a ready owned event
therefore suppresses behavioral redraw, including after a consistent recall
suffix. This local guarantee leaves source-observation reconstruction and
whole-service realization as separate obligations.

The [checked calendar stack](se-compilation-stack.md) supplies these edges for
one service. The [asynchronous plan](se-schedule-generalization.md) states how to
extend that result while retaining the baseline semantics.
