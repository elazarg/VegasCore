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
connects them to the active sealed-message protocol. `Game` contains the
focused policy and strategic adapters. The former fused application-plan
development is outside this active dependency graph in `archive/fused/`.

The active compiler is organized by proof responsibility: source/graph
construction, sealed rule generation, decoding, native refinement, and source
reconstruction. A new runtime feature should add a separate interaction or
compiler edge with explicit state/observation and correspondence laws; it
must not silently replace a sealed rule with a fused cleartext endpoint.

Ownership boundaries are semantic. Vegas owns source guards, source-declared
fallbacks, application instruction identity, and source/graph correspondence.
Interaction owns generic pending messages, histories, observations, and service
steps. GameTheoryExtensions owns reusable outcome simulation and equilibrium
transport. A future ledger or VM library should own its independent execution
model; Vegas integration should contain only lowering and correspondence for
Vegas artifacts.
