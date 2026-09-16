# VegasCore

VegasCore is a Lean 4 foundation for describing executable games with partial
information and proving that their strategic meaning survives compilation.
The checked compilation path is:

```text
failure-aware SourceProgram
  -> typed immutable Graph
  -> public pending-message runtime
```

The source supports private initial state, dependent public chance, bindings,
explicit disclosure failure, deferred public guards, heterogeneous results,
own-action recall, and terminal payoffs. The compiler preserves honest outcome
laws and translates every unilateral target deviation to a finite mixture of
legal source policies while leaving opponents unchanged. The resulting
pending-message profile preserves and reflects same-error epsilon-Nash.

The native target uses authenticated messages, ideal opaque commitments,
public opening verification, relative deadlines, and a bounded ordered service
plan. These are explicit semantic assumptions. The repository does not yet
provide cryptographic security, censorship resistance, a fair asynchronous
scheduler, ledger refinement, or EVM deployment.

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
The [EventGraph design and implementation plan](docs/event-graph-design.md)
specifies the asynchronous compilation work. Its full-source compiler and
honest outcome law under adaptive public graph scheduling are checked.
The graph-local asynchronous deviation mixture law is also checked; its
source-policy join and the event-addressed pending-message edge remain open.
The end-to-end pending-message theorem above uses ordered service.

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
