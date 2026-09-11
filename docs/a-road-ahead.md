# A road ahead

The event graph and native application form the stable compiler boundary. The
research goal remains a dependency-closed source-to-public-runtime theorem, not
a reduction to the portion currently easiest to state. Several independent
directions build toward it:

- adaptive delivery and inclusion services with explicit liveness assumptions;
- information-flow and deviation simulation for polling, receipts, and replay;
- concrete commitments and randomness with a stated adversary model;
- ledger semantics for clocks, finality, fees, and competing transactions;
- a whole-program VM backend connected to an independently exercised semantics;
- frontend validation against a canonical checked-core artifact.

These directions should remain separate until their proof edges compose over
the same artifact and observation definitions. A runtime can preserve
functional results while exposing strategically useful timing or ordering
signals. Conversely, a useful source construct may be unrealizable for a
particular public runtime without changing the capability assumptions.

## Operational target

The pending-message runtime should model submitted packets, recipient-local
delivery views, public inclusion receipts, a monotone clock, malformed and stale
traffic, replay, and permissionless deadline actions. Submission, delivery,
inclusion, reaction, and clock advancement are distinct events. The scheduler
may adapt to its public history; a fairness contract must say when a timely,
persistently valid request is protected from indefinite postponement and from
premature expiry.

The proof route is deliberately incremental. First obtain per-handler successor
lemmas preserving the completed compiler prefix and source checkpoint. Next
fold them over a whole pure-policy trace and extract one source-local deviation.
Then use finite-distribution linearity for randomized policies. Finally compose
the honest law, deviation mixture, lower-bound transport, and epsilon-Nash
equivalence. The currently checked first-poll and paired delivery/reaction laws
are inputs to this route, not its conclusion.

## Information and strategy

Every runtime decision must be based on information reproducible from the
corresponding source view, or the theorem must explicitly enrich the source
game. Public ordering, receipt timing, rejection, and expiry can all distinguish
source-indistinguishable histories. A scheduler coin independent of player
behavior cannot generally simulate an adaptive ordering policy. The intended
backtranslation is causal over observation histories and uniform in unchanged
opponents.

Utilities require the same care. Public-result theorems cover utilities that
factor through completion and decoded output. Fees, latency, privacy loss, and
trace-dependent preferences need either a richer source outcome or a separate
context bound.

## Feature composition

Application generation combines binding, ideal chance, ordinary public choice,
and conditional publication. Each instruction carries stable identity,
authority, typed reads, guards, and source provenance. Optional timeouts are
source-declared alternatives, not backend-invented failure meanings. Combining
passes must preserve field allocation, binding origins, completed-prefix
invariants, cache agreement, read availability, and noninterference between
ordinary and expiration handlers.

Chance preservation assumes ideal unbiased entropy and controls the sampled
law, not invocation time. A commitment service separates hiding, binding, and
availability. Replacing either ideal service requires a named adversary model
and a theorem at that precise boundary.

## Ledger and VM realization

A public-chain model adds admission, ordering, blocks, receipts, clocks,
finality, balances, fees, reverts, and external effects. A VM backend adds data
encoding, instruction execution, gas, exceptional halts, linking, deployment,
and calls. These layers should be independently reusable and should consume the
same identified application artifact. Component codecs or handler tests do not
establish whole-program execution refinement.

An independently exercised semantics and cross-implementation vectors are
valuable validation, but do not replace the linking and simulation proof. The
final result must identify the deployed bytes and the ledger/network model in
which they execute.

## Frontend integration

A rich frontend may target the checked sequential core, but the matched artifact
must record the exact lowered program, initial environment, feature assumptions,
and identity. Parsing success or a matching hash alone is not semantic
validation. Unsupported frontend constructs should be rejected or lowered by a
separately checked pass.
