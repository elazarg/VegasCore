# Module architecture

| Package | Responsibility |
| --- | --- |
| `GameTheory` | Pinned probability and game-theory foundation |
| `GameTheoryExtensions` | Reusable simulations, mixtures, utility transport, and predrawing |
| `Interaction` | Message pools, authenticated histories, policies, inclusion service, and ideal commitments |
| `Vegas.Foundation` | Shared typed contexts, values, visibility, guards, and result interfaces |
| `Vegas.Source` | Failure-aware sequential source syntax, semantics, accounting, and safety |
| `Vegas.Graph` | Typed immutable graph semantics and its pending-message host |
| `Vegas.Compile` | Source-to-graph construction and correspondence proofs |
| `Vegas.Game` | Strategic composition across source, graph, setup, and native runtime |
| test libraries | Executable regressions and theorem instances |
| `Paper` | Direct paper-visible theorem restatements and axiom pins |

Production libraries do not import tests or the paper audit. Generic
game-theoretic results do not depend on Vegas. `Interaction` is independent of
Vegas source syntax; graph-specific adapters and proofs remain in `Vegas.Graph`.

The active IR is `Vegas.Graph`. It retains typed expressions,
observations, bindings, resolution results, and chance kernels. The native host
executes that graph directly. Source-to-graph composition belongs in
`Vegas.Game`, above the backend theorem.

`Vegas.Language` prototypes surface notation for typed bindings and nullable
guards. `Vegas.Core` supplies its internal elaboration target. Connecting this
frontend to `SourceProgram` requires a verified elaboration edge; type-correct
lowering alone does not establish semantic refinement.

Concrete cryptography, ledgers, block production, and virtual machines belong
in separate target packages with their own execution semantics and refinement
theorems. The current `Interaction` service assumptions must be discharged,
not silently identified with a real network.
