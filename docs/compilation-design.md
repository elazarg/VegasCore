# Compilation design

This document describes the checked dependency-driven compilation tower. Its
full-source lowering, ready-event semantics, concrete pending-message service,
exact unilateral-deviation reduction, and same-error Nash correspondence are
kernel checked. [Dependency-driven EventGraph](event-graph-design.md) records
the semantic design and remaining refinement boundaries.

## Semantic interfaces

The source interface is a `SourceProgram` plus an initial typed environment.
Execution produces a terminal source state containing explicit publication
results. Programmer-written payouts are a separate projection, and analysis
supplies utilities. A behavioral policy reads only its source observation and
own action history.

The dependency-driven compiler produces a typed immutable `Vegas.EventGraph`.
Its nodes retain
the source expression code and observation boundary. Bind and resolve are
distinct graph actions: binding fixes a private value or failure without
evaluating a deferred guard; resolution chooses disclosure or failure,
evaluates the deferred checks, and records its publication result. Chance
nodes retain their conditional public kernels.

Sequential compilation adds predecessor barriers to the same event graph.
Concurrent and sequential modes retain the same fields, node code, and payoffs;
their source-to-message guarantees instantiate one mode-parameterized theorem.
Canonical execution supplies the comparison between the dependency choices.
This does not identify their native traffic or timing.

The active native interface is `EventGraphRuntime` over
`Interaction.MessageApplication`.
Private preparation creates ideal candidate material; authenticated public
submissions carry handles or openings, and inclusion authenticates and
validates them. Strategy translation describes prescribed player behavior;
the protocol still admits arbitrary native policies and does not require
players to run generated client software.
The wire policy may adapt to the public pool and environment history. At each
epoch boundary a public order policy adaptively chooses a permutation of all
event IDs. The fixed epoch protocol grants and services every event in that
order, advances the clock once, and checks every expiry. Reserved inclusion,
fixed reaction rounds, and relative expiry delimit the proved runtime contract;
`ServiceFeasible` requires every event deadline to be at least two ticks.

## Honest proof flow

The source compiler proves exact graph execution after decoding. Binding
discipline associates graph cells with their original payload identities. The
native policy compiler prepares canonical candidates, submits graph-directed
commands, and remembers its own command history.

Local continuation equations cover player invocations, adaptive wire actions,
chance steps, waiting, reserved inclusion, clock ticks, and expiry. Coherence,
packet provenance, replay protection, and activation-age invariants ensure an
unfinished event owned by an unchanged compiled player is serviced before its
deadline. Finite-run conservation composes the local equations, while
completion identifies the final native result with the decoded source state.

## Deviation proof flow

An arbitrary focal native policy may submit malformed, repeated, competing, or
unopenable candidates, withhold an opening, and react to delivered pending
traffic. The proof therefore reads accepted immutable values and verified
packets rather than trusting private caches.

The extraction proof identifies each actual phase-changing transition with a
legal graph action. Predrawing jointly fixes the focal player, public wire, and
adaptive order response functions before private initial setup is sampled. For
each pure response triple, replay, reachability, and immutable-prefix results
show that extracted choices depend only on the graph observation at that
decision. Policy completion yields a graph deviation. Source-to-graph
backtranslation then produces one finite source-policy mixture, selected
before setup and leaving every opponent unchanged.

The resulting `eventPendingSimulation` exposes exact honest and deviation laws.
Generic simulation results derive epsilon-Nash equivalence and an
arbitrary-observable guarantee: any real-valued terminal-state bound that holds
against all legal unilateral source deviations holds against every native
replacement as well. Missing native outcomes remain explicit.

## Boundaries

This proof uses ideal opaque commitments and the specific finite epoch service
above. It does not establish computational cryptography, a generalized fair
network, a ledger implementation, or EVM execution. Runtime-only utilities
require a separate observation correspondence. See
[pending deviation extraction](event-pending-deviation.md) and the
[road ahead](a-road-ahead.md).

The `Vegas.Language` surface-syntax prototype lowers to an internal `SurfaceCore`
representation. A verified elaboration to `SourceProgram` is a separate edge;
the prototype's typed lowering alone has no operational or strategic guarantee.
