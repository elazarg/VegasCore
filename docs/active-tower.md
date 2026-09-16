# Active theorem map

## Source semantics

`Vegas.Source` defines `SourceProgram`, behavioral policies, execution, and
terminal states. `Vegas.Source.Accounting` proves that complete executions
resolve their obligations; `Vegas.Source.Safety` proves retained public guards
are satisfied.

See [source semantics](source-semantics.md) and the
[source rationale](source-design-rationale.md).

## Source to typed graph

`Vegas.Game.GraphCompilation` packages the exact honest decoded-state law,
unilateral deviation backtranslation against unchanged opponents, and
same-error epsilon-Nash equivalence. `Vegas.Game.GraphSetup` transports these
results through a finite private initial law using one policy independent of
the sampled initial state.

The edge covers the full failure-aware source language and requires no finite
action-domain, failure-dominance, or universal guard-feasibility premise. See
[source-to-graph](source-graph-edge.md).

## Typed graph to pending messages

`Vegas.GraphRuntime` is the concrete target. Its state and policies use
the generic `Interaction.MessageApplication`; graph modules prove binding and
opening soundness, history provenance, replay locality, service protection,
progress, honest continuation laws, and unilateral deviation extraction.

`Vegas.Game.GraphMessages` exposes the composed capstones:

- `SourceProgram.Setup.pendingGame_complete` — every supported serviced play
  terminates, including arbitrary player and wire policies.
- `pendingGame_honest_law` — compiled play has the exact source terminal-state
  law.
- `pendingGame_deviation_law` — every unilateral native replacement has one
  finite source-policy mixture chosen before private setup is sampled, with all
  opponents unchanged.
- `pendingGame_deviation_guarantee` — any real-valued terminal-state lower bound
  valid for every legal source deviation survives every native deviation.
- `pendingGame_deviation_utility_bound` — against fixed opponents, some source
  deviation achieves at least the native deviation's expected test value;
  the witness may depend on the profile and test.
- `pendingGame_approximate_nash_iff` — compiled profiles preserve and reflect
  same-error epsilon-Nash for every terminal-state utility.

`Paper.lean` delegates to selected capstones and pins their axioms. The
[typed-message edge](typed-message-edge.md) and
[deviation extraction note](pending-deviation-extraction.md) explain the proof
boundary.

## Outside the theorem

The target assumes ideal commitments, authentication, canonical ordered
service, bounded reaction slots, and relative deadlines. It is not a theorem
about computational cryptography, arbitrary asynchronous fairness, transaction
fees, consensus, a ledger, or the EVM. The [road ahead](a-road-ahead.md) treats
those as separate refinement edges.

The `Vegas.Language` surface-syntax prototype has its own internal elaboration
target. Its connection to this tower has no semantic or strategic theorem yet.
