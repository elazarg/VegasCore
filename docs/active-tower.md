# Active compilation tower

This is the current proof boundary. Each layer is game-bearing when it has
players, observations, or policies; the layers below it do not acquire
strategic meaning merely by being executable. A later runtime can add detail by
introducing a new edge and proving its own correspondence laws.

| Layer | Owner | Active artifact | What is proved now |
| --- | --- | --- | --- |
| Probability and game forms | `GameTheory` | `FinDist`, `GameForm`, profiles | The pinned library's probability and equilibrium definitions. |
| Runtime-independent transport | `GameTheoryExtensions` | `MixtureSimulationOn`, `UtilitySimulation`, selective-stopping bounds | Exact observation-law simulation transports arbitrary observation utilities. Utility-specific deviation bounds compose and imply same-error Nash/ε-Nash equivalence at compiled profiles. Selective-stopping bounds require a continuation comparison at the information used to stop. |
| Vegas semantic substrate | `Vegas.Foundation` | typed environments, visibility, values, obligations | Type/visibility and finite-domain infrastructure. No strategic preservation claim. |
| Checked source | `Vegas.Core` | `VegasCore`, `WFProgram`, `SourceBehavioralPolicy`, `sourceGameForm` | Intrinsically typed sequential source syntax; guarded source policies; written-order source execution and payoff evaluation. Nullable `yield` supplies an explicit `Option.none` value. |
| Graph compilation | `Vegas.Compile`, `Vegas.Game.SourceGraph` | canonical graph, declared-read policy runner, `WFProgram.sourceGraphSimulation` | Typed source compilation; exact whole-program terminal-environment law; uniform single-policy backtranslation of every unilateral declared-read graph deviation, with opponents unchanged. A concrete certificate proves Nash and same-error ε-Nash equivalence at compiled profiles for all checked core programs and finite player sets. |
| Graph strategic presentation | `Vegas.EventGraph.Strategic` | behavioral frontier game and canonical declared-read policy game | Under `CommitInformationLocal` and one ready commitment per player, compiled canonical policies preserve the complete observed outcome law of every behavioral profile; every unilateral canonical replacement is exactly one behavioral graph deviation. This is an event-graph theorem, not yet a source-language or message-runtime theorem. |
| Sealed native protocol | `Interaction` | message pool, ideal commitment service, `SealedProgram`, policy runner, timed adapter | Commit and reveal are separate protocol actions. Arbitrary finite native traffic—including malformed payloads, retries/replay, delivery, inclusion, and withholding—either stutters or takes a valid graph step. The environment sees the full pending pool; player views expose their own inbox/sent messages and the public ledger. Hiding is proved for protected pre-disclosure traffic. The timed adapter proves clock/expiration operational correspondence; it does not itself assert liveness or source quit. |
| Vegas compiler edge | `Vegas.Compile` | `SealedCompilation`, sealed decode/refinement/source modules | One sealed rule per graph node; native prefixes decode to reachable graph states; terminal prefixes reconstruct a written-order source run with matching bindings and payoffs. The policy runner has the same support-level source theorem. |
| Strategic adapter | `Vegas.Game` | `SealedCompilation.StrategicCertificate` | A concrete target game may supply an honest law and a finite-mixture backtranslation; generic transport then gives the Nash/ε-Nash theorems. The certificate is an explicit obligation, not an automatic consequence of prefix refinement. |

## Current strategic gap

The backend admits homogeneous commit/reveal programs with unrestricted guards,
including multistage choices whose information includes earlier public values
and their owner's prior commitments. Nonempty choice-information sets are
justified by the reachable-store invariant, not erased from the source.
Samples, nontrivial validation guards, and disclosures of initial private
fields still require further compiler support.

The active code does **not** yet instantiate a `StrategicCertificate` for the
pending-message policy game. This is the remaining end-to-end deviation proof:
for every considered player policy (which may inspect that player's visible
inbox, public ledger, sent messages, receipts, and recorded local history),
construct a finite mixture of source behavioral policies with the same observed
outcome law against unchanged opponents and environment policy. Seeing a
pending opening before inclusion is not by itself an information leak: a
sealed rule cannot take the corresponding graph step until its prerequisites
are included. A deviator may pre-submit a later message, but the backtranslation
must show that this is equivalent to choosing that source action when the
corresponding source observation becomes available. This causal pending-message
lemma is still unproved. The runtime kernel already records malformed input as
a rejected, state-preserving action; a separate resolution law must map such a
stutter—or a fair timeout after it—to the source program's explicit nullable
quit (`Option.none`). Once these laws and the rest of the deviation mixture are
proved, `SealedCompilation.StrategicCertificate` discharges the equilibrium
conclusion without changing the source language. The graph theorem has this
same exact-deviation shape after backtranslation; its single-ready hypothesis
does not hold automatically for graphs with multiple simultaneously ready
commitments.

For selective quitting, exact outcome-law simulation and Nash preservation
are separate targets. The latter can use `UtilitySimulation` if every runtime
deviation is no better than a legal source deviation. The native fixed-opening
utility bound is checked, but its whole-program continuation instance is not.
The current timeout adapter supplies a final-failure status, not the source
program's quit continuation; missing commitments also need a resolution rule.

The source-to-declared-read-graph strategic edge is discharged independently of
these pending-message obligations. Its full source-environment outcome law
allows samples, validation guards, and heterogeneous fields. This does not
extend the admitted fragment of the sealed backend or grant its policies the
same information boundary as the graph kernels.

## Deliberate non-claims

The tower currently has no cryptographic reduction, authenticated identities,
block-production/fairness theorem, public mempool scheduler theorem, EVM
execution/refinement theorem, or contract settlement theorem. Those are future
runtime edges. The `archive/fused/` directory contains the former fused
application-plan development as readable research material; its results are not
imported by the active tower or counted by `Paper.lean`.
