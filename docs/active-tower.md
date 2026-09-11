# Active compilation tower

This is the current proof boundary. Each layer is game-bearing when it has
players, observations, or policies; the layers below it do not acquire
strategic meaning merely by being executable. A later runtime can add detail by
introducing a new edge and proving its own correspondence laws.

| Layer | Owner | Active artifact | What is proved now |
| --- | --- | --- | --- |
| Probability and game forms | `GameTheory` | `FinDist`, `GameForm`, profiles | The pinned library's probability and equilibrium definitions. |
| Runtime-independent transport | `GameTheoryExtensions` | `MixtureSimulationOn`, `QuitTransfer` | Honest observation-law transport; finite-mixture unilateral-deviation transport implies expected-utility bounds and exact Nash/ε-Nash preservation/reflection. A supplied source-quit utility law rules out a target quit when source play strictly improves on it. |
| Vegas semantic substrate | `Vegas.Foundation` | typed environments, visibility, values, obligations | Type/visibility and finite-domain infrastructure. No strategic preservation claim. |
| Checked source | `Vegas.Core` | `VegasCore`, `WFProgram`, `SourceBehavioralPolicy`, `sourceGameForm` | Intrinsically typed sequential source syntax; guarded source policies; written-order source execution and payoff evaluation. Nullable `yield` supplies an explicit `Option.none` value. |
| Graph compilation | `Vegas.EventGraph` | canonical graph, finite configurations, graph execution | Typed source nodes, dependencies, declared reads, reachable graph prefixes, and terminal graph-to-written-source correspondence. |
| Sealed native protocol | `Interaction` | message pool, ideal commitment service, `SealedProgram`, policy runner, timed adapter | Commit and reveal are separate protocol actions. Arbitrary finite native traffic—including malformed payloads, retries/replay, delivery, inclusion, and withholding—either stutters or takes a valid graph step. Hiding is proved for protected pre-disclosure traffic. The timed adapter proves clock/expiration operational correspondence; it does not itself assert liveness or source quit. |
| Vegas compiler edge | `Vegas.Compile` | `SealedCompilation`, sealed decode/refinement/source modules | One sealed rule per graph node; native prefixes decode to reachable graph states; terminal prefixes reconstruct a written-order source run with matching bindings and payoffs. The policy runner has the same support-level source theorem. |
| Strategic adapter | `Vegas.Game` | `SealedCompilation.StrategicCertificate` | A concrete target game may supply an honest law and a finite-mixture backtranslation; generic transport then gives the Nash/ε-Nash theorems. The certificate is an explicit obligation, not an automatic consequence of prefix refinement. |

## Current strategic gap

The active code does **not** yet instantiate a `StrategicCertificate` for the
pending-message policy game. This is the remaining end-to-end deviation proof:
for every considered player policy (which may inspect that player's visible
inbox, public ledger, sent messages, receipts, and recorded local history),
construct a finite mixture of source behavioral policies with the same observed
outcome law against unchanged opponents and environment policy. The runtime
kernel already records malformed input as a rejected, state-preserving action;
the missing theorem is the resolution/backtranslation law that maps such a
stutter—or a fair timeout after it—to the source program's explicit nullable
quit (`Option.none`). Once that law and the rest of the deviation mixture are
proved, `SealedCompilation.StrategicCertificate` discharges the equilibrium
conclusion without changing the source language.

## Deliberate non-claims

The tower currently has no cryptographic reduction, authenticated identities,
block-production/fairness theorem, public mempool scheduler theorem, EVM
execution/refinement theorem, or contract settlement theorem. Those are future
runtime edges. The `archive/fused/` directory contains the former fused
application-plan development as readable research material; its results are not
imported by the active tower or counted by `Paper.lean`.
