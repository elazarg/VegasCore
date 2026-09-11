# Library and proof boundaries

| Library | Responsibility |
| --- | --- |
| `GameTheory` | Pinned probability and game-theory foundation |
| `GameTheoryExtensions` | Runtime-independent simulation and equilibrium transport |
| `Interaction` | Native message pool, delivery, receipts, policies, and ideal commitment service |
| `Vegas` | Sequential source language, event graph, compilation, and native adapters |
| retained tests | Executable witnesses and regressions |
| `Paper` | Direct theorem restatements and explicitly admitted targets in `Paper.lean` |

Production libraries do not import tests or the paper audit. Generic
game-theoretic results do not import Vegas. Interaction owns reusable message
semantics and does not depend on Vegas source syntax.

Within Vegas, `Core` defines source programs and written-order execution,
`EventGraph` defines the dependency graph and its execution, and `Compile`
connects them and emits retained native applications. `Game` contains only
the focused adapters used by those applications.

The application compiler is organized by proof responsibility rather than by
a second runtime hierarchy. Plan/allocation modules construct the instruction
inventory; binding, sample, public-choice, and conditional-publication modules
prove their local image and successor laws; policy modules establish controller
locality and cache/provenance invariants; service and prefix modules compose
actual message runs; outcome modules decode completed states. Feature-specific
modules should depend on the shared plan and native application definitions,
not duplicate them.

Ownership boundaries are semantic. Vegas owns source guards, source-declared
fallbacks, application instruction identity, and source/graph correspondence.
Interaction owns generic pending messages, histories, observations, and service
steps. GameTheoryExtensions owns reusable outcome simulation and equilibrium
transport. A future ledger or VM library should own its independent execution
model; Vegas integration should contain only lowering and correspondence for
Vegas artifacts.
