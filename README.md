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
Sequential compilation adds predecessor barriers to the same event graph;
both execution modes use the same pending-message runtime and strategic proof.

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

An arbitrary real-valued observation of the public source result may be used
in the deviation guarantee; it need not be a player's declared payoff. Thus a
source lower bound that holds against every legal unilateral source deviation
also holds against every unilateral native deviation, with missing native
outcomes represented explicitly.

`Vegas.Language` is a surface-syntax prototype for typed bindings and nullable
guard notation. It lowers to an internal `SurfaceCore` representation whose
optional `Legal` predicate requires satisfiable commitment guards. This differs
from `SourceProgram`, which admits unsatisfiable guards and represents their
resolution as failure. The prototype has no execution semantics or verified
elaboration into `SourceProgram`; its typed lowering carries no operational or
strategic compilation claim. Its syntax and tests are maintained separately.

Start with the [artifact guide](ARTIFACT.md), [theorem map](docs/active-tower.md),
[module ownership](docs/module-architecture.md), and
[compilation design](docs/compilation-design.md). Semantic details live in the
[source rationale](docs/source-design-rationale.md),
[source semantics](docs/source-semantics.md),
[source-to-graph edge](docs/source-graph-edge.md), and
[pending-message proof](docs/event-pending-deviation.md). The
[scheduling proof](docs/event-graph-scheduling-proof.md) and
[public-opening boundary](docs/event-graph-public-observations.md) explain
the information conditions. The [frontend boundary](docs/compiler-boundary.md)
and [outcome/utility distinction](docs/outcomes-and-utilities.md) describe the
interfaces to richer languages and analyses. The
[road ahead](docs/a-road-ahead.md) describes target boundaries still to add, and
the [auction discussion](docs/auctions-discussion.md) collects open questions on
allocations, private values, and truthfulness.
The [EventGraph design](docs/event-graph-design.md) specifies the asynchronous
compilation boundary. The event-addressed pending-message game has checked
arbitrary-player completion, honest outcome, unilateral-deviation mixture, and
same-error epsilon-Nash theorems under the concrete
[public epoch service](docs/event-service.md). The deviation may use any native
player policy. Its exact source-policy mixture is chosen before private setup,
while the native wire and event-order policies remain public and adaptive.

Subgame perfection requires additional continuation guarantees. The reactive
compiler has a [checked counterexample under uniform inclusion](docs/early-opening-and-spe.md):
an honest source SPE compiles to a policy with a profitable off-path deviation.
The deviation spends a transmission on an early opening instead of repairing
the current binding. The [inclusion investigation](docs/inclusion-and-spe.md)
separates the proved local selection laws from the remaining service and
compiler obligations. Honest SPE preservation under a suitable constrained
service remains open.

## Build

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python scripts/report-open-obligations.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

The pinned `GameTheory` dependency and `GameTheoryExtensions` contain reusable
game-theoretic mathematics. `Interaction` owns runtime-independent message
semantics. `Vegas` owns the source language, typed graph, compiler, and their
correspondence.
