# Compilation and runtime boundary

The [source compiler](../Vegas/Compile/EventGraphCompiler.lean) lowers typed
instructions to an event graph. Source-law and Nash correspondence hold under
their stated public graph schedulers. Concurrent event-graph scheduling is
distinct from partially observed concurrent raw-ledger SE preservation.

The compiled graph is instantiated as an Interaction application, and actual
ledger clients use its translated policies. The
[direct sequential compiler laws](../Vegas/Game/SourceServiceFirstTurnCompletion.lean)
preserve every total observation of the source profile's joint typed terminal
state and public defaults under the actual physical clients. They compare the
same clients with canonical execution of the compiled graph, using the
asynchronous service and timing premises. They need no finite wire catalogue,
equilibrium, audit, utility bound or independent-prior premise.
[Bounded-menu compiler laws](../Vegas/Game/CompilerCorrectness.lean) realize
that observation in every dependency mode satisfying the public-barrier certificate.
The [operational capstone](../Vegas/Pending/GraphRefinement.lean) exposes
finite-path graph refinement of arbitrary raw protocol transitions and
initialized histories. These results and their scope are listed in the
[compiler correctness plan](compiler-correctness-plan.md).
A standalone compiler for arbitrary graph policies is a separate generalization.

The retained raw SE theorems use the sequential forced-exit
controller. Players send authenticated envelopes to a pending network. A
scheduler chooses activations, inclusion, clock advances and expiry; the
application records included envelopes and executes its permitted transitions.
Policies observe their actual recall and the specified reception rule.

Service hypotheses concern every legal raw history. They guarantee opportunities,
protected inclusion for the specified sole event identifier, deadlines and
completion. Theorems quantify over supplied relative event durations, not only
one calendar. The count audit separately assumes authentic evidence and
conditional coverage adequate for the stated deposit inequality.

These operational premises must be derived for a concrete deployment. In
particular, timely inclusion alone does not establish evidence availability,
and an engine step is not automatically elapsed blockchain time. The
[open-problems guide](sequential-se-open-problems.md) describes these interfaces
and the positive-latency regression.
