# VegasCore

VegasCore is a Lean 4 foundation for describing executable games with partial
information and proving that their strategic meaning survives compilation.
The checked compilation path is:

```text
failure-aware SourceProgram
  -> dependency-driven EventGraph
  -> public pending-message runtime
```

The source supports private initial state, dependent public chance, bindings,
explicit disclosure failure, deferred public guards, heterogeneous results,
own-action recall, and terminal payoffs. The compiler preserves honest outcome
laws and translates every unilateral target deviation to a finite mixture of
legal source policies while leaving opponents unchanged. The resulting
pending-message profile preserves and reflects same-error epsilon-Nash.

The native target uses authenticated messages, ideal opaque commitments,
public opening verification, and relative deadlines. Its concrete finite
service runs fixed-shape epochs: a public policy adaptively chooses a
permutation of all events, each event receives its prescribed opportunities,
then the clock advances once and expiry is checked. The strategic theorem
assumes every event deadline is at least two ticks. The wire and order policies
may adapt to their public observations and histories; no generalized fair
network is assumed. The repository does not provide computational
cryptographic security, censorship resistance, ledger refinement, or EVM
deployment.

An arbitrary real-valued observation of the terminal source state may be used
in the deviation guarantee; it need not be a player's declared payoff. Thus a
source lower bound that holds against every legal unilateral source deviation
also holds against every unilateral native deviation, with missing native
outcomes represented explicitly.

`Vegas.Language` is a surface-syntax prototype for typed bindings and nullable
guard notation. It lowers to an internal `SurfaceCore` representation. A verified
elaboration into `SourceProgram` remains to be supplied; the prototype carries
no operational or strategic compilation claim.

Start with the [artifact guide](ARTIFACT.md), [theorem map](docs/active-tower.md),
[module ownership](docs/module-architecture.md), and
[compilation design](docs/compilation-design.md). Semantic details live in the
[source rationale](docs/source-design-rationale.md),
[source semantics](docs/source-semantics.md),
[source-to-graph edge](docs/source-graph-edge.md), and
[typed-message edge](docs/typed-message-edge.md). The
[road ahead](docs/a-road-ahead.md) describes target boundaries still to add.
The [EventGraph design](docs/event-graph-design.md) specifies the asynchronous
compilation boundary. The event-addressed pending-message game has checked
arbitrary-player completion, honest outcome, unilateral-deviation mixture, and
same-error epsilon-Nash theorems under the concrete
[public epoch service](docs/event-service.md). The deviation may use any native
player policy. Its exact source-policy mixture is chosen before private setup,
while the native wire and event-order policies remain public and adaptive.

## Build

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

The pinned `GameTheory` dependency and `GameTheoryExtensions` contain reusable
game-theoretic mathematics. `Interaction` owns runtime-independent message
semantics. `Vegas` owns the source language, typed graph, compiler, and their
correspondence.
