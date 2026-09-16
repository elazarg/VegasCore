# Module architecture

| Package | Responsibility |
| --- | --- |
| `GameTheory` | Pinned probability and game-theory foundation |
| `GameTheoryExtensions` | Reusable simulations, mixtures, utility transport, and predrawing |
| `Interaction` | Message pools, authenticated histories, policies, inclusion service, and ideal commitments |
| `Vegas.Foundation` | Shared typed contexts, values, visibility, guards, and result interfaces |
| `Vegas.Expr` | Concrete typed expressions, distributions, and finite-value instances |
| `Vegas.Source` | Failure-aware sequential source syntax, semantics, accounting, and safety |
| `Vegas.Graph` | Typed immutable graph syntax, semantics, observations, and binding discipline |
| `Vegas.EventGraph` | Dependency-driven typed events, cut-based execution, observations, and scheduler-parametric games |
| `Vegas.Pending` | Graph-directed pending-message runtime, strategy compilation, service, and correctness |
| `Vegas.Compile` | Source-to-graph construction and correspondence proofs |
| `Vegas.Game` | Strategic composition across source, graph, setup, and native runtime |
| test libraries | Executable regressions and theorem instances |
| `Paper` | Direct paper-visible theorem restatements and axiom pins |

Production libraries do not import tests or the paper audit. Generic
game-theoretic results do not depend on Vegas. `Interaction` is independent of
Vegas source syntax. Neither graph representation depends on the backend or
on the other representation; `Vegas.Pending`
imports the graph, not source syntax or its compiler. The boundary checker
enforces these directions and keeps the prototype frontend out of the verified
compiler and shared expression modules.

The active IR is `Vegas.Graph`. It retains typed expressions,
observations, bindings, resolution results, and chance kernels. The native host
in `Vegas.Pending` executes that graph directly. Source-to-graph composition
belongs in `Vegas.Game`, above the backend theorem.

`Vegas.EventGraph` supplies the operational interface for dependency-driven
compilation. It has no source compiler or pending-message strategic edge yet.
Its source-order execution and other scheduling instances share one runner;
the [EventGraph plan](event-graph-design.md) separates source correspondence,
schedule-independent semantic effects, and asynchronous strategic guarantees.

`Vegas.Language` prototypes surface notation for typed bindings and nullable
guards. Its internal `SurfaceCore` representation and side conditions live in
`Vegas.Language`; the concrete expression language in `Vegas.Expr` is shared
with source and backend tests and has no frontend dependency. Connecting the
prototype to `SourceProgram` requires a verified elaboration edge; type-correct
lowering alone does not establish semantic refinement.

Concrete cryptography, ledgers, block production, and virtual machines belong
in separate target packages with their own execution semantics and refinement
theorems. The current `Interaction` service assumptions must be discharged,
not silently identified with a real network.
