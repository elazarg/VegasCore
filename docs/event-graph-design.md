# Event graph design

The compilation path is:

```text
SourceProgram → EventGraph → EventGraphRuntime
```

Source compilation and native execution have separate, graph-relative
correctness edges. The source language is independent of transport; the graph
is independent of source syntax; the backend implements graph events using
runtime-general message semantics from `Interaction`.

## Scheduling is a compilation choice

The graph carries typed events, a topological rank, and predecessor sets.
Execution may complete any ready event. Source-order execution is the canonical
scheduler of this same executor.

There are two dependency choices:

- Concurrent compilation keeps the required public and own-action barriers.
- Sequential compilation adds every earlier event as a predecessor.

Adding barriers changes readiness, not node code, value types, or payoff
interpretation. It makes completion genuinely sequential even when native
players submit premature traffic and service visits events out of order.
Fixing the order of visits alone would not do so: an earlier event might still
await its deadline when a later independent event receives service.

This is a compiler transformation within one representation. It does not assert
that every implementation of an asynchronous graph already enforces sequential
execution, or that native traces in the two modes coincide. The semantic law
compares canonical execution with the dependency-constrained graph. The common
backend theorem applies because the constrained graph retains the required
information barriers.

## What the dependencies protect

The source policy interface exposes preceding public fields, the player's own
bindings, and original own-action history. Expression footprints alone are
therefore insufficient to derive strategic dependencies.

The required ordering certificate `BarrierOrdered` contains three families of
edges: all earlier events before a public event, earlier public events before
later events, and earlier same-owner bindings before later same-owner bindings.
Additional source-ranked edges are allowed. `EventOrder.predecessor_lt` rules
out cyclic or backwards dependencies.

At a ready strategic event, the available visible fields and own actions are
exactly those in its source-ranked prefix. A ready public event is the unique
ready event. Foreign hidden bindings can complete independently.

These statements are graph-level results in `Vegas.EventGraph.BarrierInformation`.
The source compiler constructs their premises. The runtime consumes them without
referring to a source program.

## Small examples

### Independent hidden bindings

```text
commit A.x;
commit B.y;
reveal A.x;
reveal B.y;
```

The first two events may complete in either order. Both precede the prescribed
publication of x. The disclosures remain ordered because B's disclosure policy
may depend on x's published result.

### Information without an expression dependency

```text
sample b ~ fairBool;
commit A.x where true;
```

A may choose x = b despite the constant guard. Reversing these source lines
instead requires keeping the future coin hidden until A's choice is fixed.

### Deferred validation

```text
commit P.x;
commit P.y where x = y;
reveal P.y;
reveal P.x;
```

With mismatching bindings and attempted disclosures, y succeeds because its
reveal does not complete the guard `x = y`; the later x reveal completes it and
fails. Swapping the disclosures changes which publication fails. A storage-level
commutation argument would miss this dependency.

### Own-action memory

An attempted disclosure rejected by validation and intentional withholding can
both publish failure. A later decision may depend on the original intention.
The source, graph, and prescribed native strategy retain that original action.

These examples explain separate information, validation, and recall obligations.
Executable regressions are in the source and event-graph test modules.

## One graph, distinct observations

A configuration contains initial inputs, a predecessor-closed completed cut,
immutable outputs, and chronological completions with their original actions.
A graph player sees public values, its own private bindings and actions, and
completion order. A public graph scheduler sees public values and completion
order, but not hidden binding meanings.

The pending-message target adds actual submission, delivery, inclusion, receipt,
clock, and grant observations. Ideal commitment meanings remain private semantic
state. Arbitrary players may disclose their own values through their traffic;
the theorem fixes the other players to their compiled policies and accounts for
public environment reactions. It does not prohibit a deviator from speaking.

Hiding must hold for the joint observation history, not for each observable
component in isolation. Revealing a mask and a masked secret in different
components can reveal the secret together.

## Operational and strategic results

The canonical source-to-graph law preserves the complete terminal-state
distribution. Canonical graph deviations have a single source-policy preimage
uniform over private setup. Under asynchronous graph scheduling, a finite
mixture of source policies suffices.

The backend compiles graph policies to prescribed native policies, without
requiring participants to execute generated client code. It admits arbitrary
unilateral native replacements, including malformed, premature, repeated,
competing, and unopenable submissions and withholding.

The native exact deviation law is proved against unchanged opponents. Its finite
source-policy mixture is selected before private initial setup. It yields:

- exact honest outcome laws;
- preservation and reflection of same-error epsilon-Nash at compiled profiles;
- arbitrary terminal-source-state lower bounds against unilateral deviations,
  independent of the deviator's preferences.

These claims cover the full source language. They require neither finite payload
domains, universal guard feasibility, nor a failure-dominance premise at this
barrier-preserving ideal edge. They do not identify all target equilibria with
source equilibria or equate full runtime traces.

The [source edge](source-graph-edge.md), [native proof](event-pending-deviation.md),
and [audited results](../Paper.lean) give the owning declarations.

## Native service and completion

The shared runtime uses opaque ideal commitment handles, authenticated messages,
public opening verification, and relative deadlines. Every epoch adaptively
chooses a permutation of all event IDs from the public environment view/history.
Each event receives a grant, three owner calls when owned, configured
wire/reaction rounds, reserved inclusion, and a sample opportunity. The sweep is
followed by one clock tick and expiry checks.

`ServiceFeasible` requires every deadline to be at least two ticks. An event
enabled after its visit in an epoch then receives its next reserved visit before
expiry. Completion holds under arbitrary player policies; unchanged-owner
protection is proved for actual reachable service prefixes. This is a concrete
bounded service, not an unrestricted fairness premise.

The graph-local proof uses commutation and public scheduling. The native proof
additionally uses candidate provenance, actual-history replay, original-action
recall, deadline protection, and joint predrawing of the focal, wire, and order
responses. The native environment is not silently replaced by an ideal graph
scheduler: it observes traffic that the latter does not receive.

## Refinement boundary

The current target assumes ideal commitments and its concrete service.
Computational cryptography, transaction/ledger execution, block production,
fees, finality, and EVM code are separate refinement edges. Ethereum grounds
the roadmap but does not own runtime-general concepts.

A lower implementation must realize operational, observation, and strategic
contracts, including the service needed before deadlines. A trace-sensitive
utility or a broader opportunity for informed failure needs its own comparison.
The [failure note](event-graph-failure-comparison.md) separates that possible
extension from the exact theorem established here. The [road ahead](a-road-ahead.md)
records the next target boundaries.
