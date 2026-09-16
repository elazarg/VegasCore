# Compilation design

This document describes the checked ordered tower. The next compiler design
and implementation milestones are specified in
[Dependency-driven EventGraph](event-graph-design.md). Its full-source lowering,
ready-event semantics, and strategic correspondence under adaptive public graph
scheduling are checked. The concrete asynchronous pending-message service has
checked completion and full-source honest outcome laws. Its arbitrary-deviation
and Nash theorems remain open; the ordered theorem does not discharge them.

## Semantic interfaces

The source interface is a `SourceProgram` plus an initial typed environment.
Execution produces a terminal source state containing explicit publication
results. Programmer-written payouts are a separate projection, and analysis
supplies utilities. A behavioral policy reads only its source observation and
own action history.

The compiler produces a typed immutable `Vegas.Graph`. Its nodes retain
the source expression code and observation boundary. Bind and resolve are
distinct graph actions: binding fixes a private value or failure without
evaluating a deferred guard; resolution chooses disclosure or failure,
evaluates the deferred checks, and records its publication result. Chance
nodes retain their conditional public kernels.

The native interface is `GraphRuntime` over `Interaction.MessageApplication`.
Private preparation creates ideal candidate material; authenticated public
submissions carry handles or openings, and inclusion authenticates and
validates them. Strategy translation describes prescribed player behavior;
the protocol still admits arbitrary native policies and does not require
players to run generated client software.
The wire policy may adapt to the public pool and environment history. Reserved
service slots, canonical graph order, and relative expiry delimit the proved
runtime contract.

## Honest proof flow

The source compiler proves exact graph execution after decoding. Binding
discipline associates graph cells with their original payload identities. The
native policy compiler prepares canonical candidates, submits graph-directed
commands, and remembers its own command history.

Local continuation equations cover player invocations, adaptive wire actions,
chance ticks, waiting, and reserved inclusion. Service safety prevents a live
unchanged-player phase from expiring. Finite-run conservation composes the
local equations, while completion identifies the final native result with the
decoded source state.

## Deviation proof flow

An arbitrary focal native policy may submit malformed, repeated, competing, or
unopenable candidates, withhold an opening, and react to delivered pending
traffic. The proof therefore reads accepted immutable values and verified
packets rather than trusting private caches.

The extraction proof identifies each actual phase-changing transition with a
legal graph action. Predrawing fixes focal and wire response functions jointly,
before private initial setup is sampled. For each response pair, replay and
immutable-prefix results show that extracted choices depend only on the graph
observation at that decision. Policy completion yields a graph deviation.
Source-to-graph backtranslation then produces the finite source-policy mixture
while leaving every opponent unchanged.

The resulting `pendingSimulation` exposes exact honest and deviation laws.
Generic simulation results derive epsilon-Nash equivalence and an
arbitrary-observable guarantee: any real-valued terminal-state bound that holds
against all legal unilateral source deviations holds against every native
replacement as well. Missing native outcomes remain explicit.

## Boundaries

This proof uses ideal commitments and bounded ordered service; it is not a
cryptographic or ledger theorem. Runtime-only utilities require a separate
observation correspondence. See [typed-message edge](typed-message-edge.md),
[deviation extraction](pending-deviation-extraction.md), and the
[road ahead](a-road-ahead.md).

The `Vegas.Language` surface-syntax prototype lowers to an internal `SurfaceCore`
representation. A verified elaboration to `SourceProgram` is a separate edge;
the prototype's typed lowering alone has no operational or strategic guarantee.
