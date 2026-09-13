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

`SealedCompilation.compilePolicy` implements a written-source policy in the
native principal-scoped interface. Local reconstruction reads only initial
source-visible inputs, public application events, and the owner's registration
history. The checked registration-memory invariant holds under arbitrary
opponent and environment policies. Fresh registrations use exactly the
declared-read source kernel; occupied slots publish an opaque handle without
resampling. Every emitted opening already satisfies the public publication
barrier, and no compiled-policy packet is a cleartext commitment.

These local policy laws are not the whole-program honest or deviation law.
The mathematical coupling and its remaining Lean obligations are described in
[pending-message-strategic-proof.md](pending-message-strategic-proof.md).

`SealedFragment.replay` evaluates the shared native runner with assigned honest
values and fixed deterministic deviator/environment policies. Its checked
`replay_eq_iff` characterizes each full execution by exactly the honest
registration coordinates it records. This holds for every finite invocation
schedule and thus for every invocation prefix. It concerns proof-facing records,
including private commands; it does not expose those records to players. The
support-transfer and registration-origin lemmas also allow randomized native
deviator and environment policies. The knowledge-indexed native relation
preserves public observations, pool operations, and validation receipts while
allowing unknown registered values to differ. The compiled-policy comparison
and submission barrier supply its local policy premises. Whole-run
read-boundedness, kernel agreement, and the probability coupling remain to be
proved.

The backend admits homogeneous commit/reveal programs with unrestricted guards,
including multistage choices whose information includes earlier public values
and their owner's prior commitments. Nonempty choice-information sets are
justified by the reachable-store invariant, not erased from the source.
Samples, nontrivial validation guards, and disclosures of initial private
fields still require further compiler support.

The active code does **not** yet prove whole-program strategic preservation for
the pending-message policy game. The immediate coupling must give the actual
native execution marginal and a source marginal that is a finite mixture of
legal source deviations, against unchanged opponents. The deviator may use its
inbox, public ledger, sent messages, receipts, and local command history; the
environment may use all pending payloads. Extraction must preserve the dependence
between honest draws rather than resample them after disclosure.

An inclusion check alone cannot protect against observing a pending opening.
The compiled policy checks the publication barrier **before submission**:
every source-earlier commitment is already bound. Consequently, replay before
the focal choice is bound can encounter only honest openings already available
in that choice's source view. The needed whole-run read-boundedness theorem
connects this local barrier to the extracted source policy.

For selective quitting, exact outcome-law simulation and Nash preservation
are separate targets. The latter can use `UtilitySimulation` if every runtime
deviation is no better than a legal source deviation. The native fixed-opening
utility bound is checked, but its whole-program continuation instance is not.
The current timeout adapter supplies a final-failure status, not the source
program's quit continuation; missing commitments also need a resolution rule.
The mathematical note specifies one concrete resolving extension: per-node
relative deadlines, nullable defaults, and continued execution of the same
program outcome code. It gives service and termination bounds and constructs
the source/native coupling for the nullable, unique-direct-reveal fragment.
That extension and the whole-program proof are not implemented in Lean.
Malformed messages are rejected without a source step. Fair deadline resolution
must implement the programmer's quitting settlement; a rejected attempt alone
does not do so. In particular, withholding a committed `some a` cannot be
identified with a full source environment where its deterministic reveal copied
`none`. The coupling must retain the locked source choice and compare its legal
continuation with the runtime settlement. Ordinary ex-ante strict dominance of
the source quit action does not establish this comparison at finer stopping
information. The immediate final interface is the existing `UtilitySimulation`,
not an assumed exact-outcome `StrategicCertificate` for selective quitting.

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
