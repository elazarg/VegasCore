# Artifact and validation guide

## Reproduction

Use the pinned Lean toolchain and dependency revisions:

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

Do not run `lake update` when reproducing a revision. The cache only accelerates
the subsequent kernel-checked build.

## What is checked

| Boundary | Owning code |
| --- | --- |
| Source execution and safety | `Vegas/Source/` |
| Source legal-history interfaces, pure policies, and continuation laws | `Vegas/Source/CommitmentInterface.lean`, `Vegas/Source/ProtocolEvaluation.lean`, `Vegas/Source/SetupProtocolEvaluation.lean` |
| Source pure SPE characterization, including private setup | `Vegas/Game/SourceSubgame.lean`, `Vegas/Game/SetupSubgame.lean` |
| Source behavioral policies, continuation laws, and SPE characterization | `Vegas/Source/ProtocolBehavioralPolicy.lean`, `Vegas/Source/SetupProtocolBehavioral.lean`, `Vegas/Game/BehavioralSubgame.lean` |
| Conditional behavioral SPE preservation and reflection at proper roots | `GameTheoryExtensions/Protocol/BehavioralContinuation.lean` |
| Conditional pure SPE preservation and reflection at proper roots | `GameTheoryExtensions/Protocol/Continuation.lean` |
| Proper reactive subgames after two deterministic initial responses | `Interaction/ReactiveSubgamePrefix.lean` |
| Honest source SPE whose compiled graph policy fails SPE under uniform, at-most-once inclusion | `VegasTests/ReactiveEarlyOpeningSPE.lean` |
| Immutable authorization at original submission, with conditional exclusion at every legal continuation | `Interaction/ReactiveAuthorization.lean`, `Vegas/Pending/ReactiveAuthorization.lean` |
| Authorized unfinished packets belong to the sender's current ready owned event under source information discipline | `Interaction/ReactiveRecallInvariant.lean`, `Vegas/Pending/ReactiveAuthorizationProgress.lean` |
| Premature packets in the early-opening witness remain unauthorized; fresh later openings are authorized | `VegasTests/ReactiveAuthorization.lean` |
| Source to typed graph and canonical single-policy correspondence | `Vegas/Compile/EventGraphCanonical.lean`, `Vegas/Compile/EventGraphDeviation.lean` |
| Sequential completion by dependency barriers | `Vegas/EventGraph/Sequential.lean` |
| Message transport and player policies | `Interaction/MessageApplication.lean`, `Interaction/MessageApplicationPolicies.lean` |
| Event-addressed runtime and service | `Vegas/Pending/EventApplication.lean`, `Vegas/Pending/EventService.lean` |
| Binding from authenticated submission through arbitrary native continuations | `Vegas/Pending/EventCommitmentBinding.lean` |
| Multiplayer native action protocol, policy equivalence, and bounded native execution | `Vegas/Pending/NativeProtocol.lean`, `Vegas/Pending/NativeProtocolPolicy.lean`, `Vegas/Pending/NativeProtocolEvaluation.lean`, `Vegas/Pending/NativeProtocolSafety.lean` |
| Fresh candidates at every native prefix and direct construction of typed binding material | `Vegas/Pending/EventFreshCandidates.lean`, `Vegas/Pending/EventBindingAction.lean` |
| Full-source honest law under adaptive public graph scheduling | `Vegas/Compile/EventGraphScheduling.lean` |
| Full-source asynchronous deviations and Nash correspondence | `Vegas/Compile/EventGraphDeviation.lean`, `Vegas/Game/EventCompilation.lean` |
| Asynchronous pending-message service and arbitrary-player completion | `Vegas/Pending/EventService.lean`, `Vegas/Pending/EventServiceCompletion.lean` |
| Asynchronous pending-message deviation reduction | `Vegas/Pending/EventDeviationLaw.lean`, `Vegas/Pending/EventStrategicLaw.lean` |
| Full-source pending-message deviations and Nash correspondence | `Vegas/Game/EventMessageStrategic.lean` |
| Initial-parameter/public-result joint laws and Bayesian Nash correspondence | `Vegas/Source/InitialState.lean`, `Vegas/Game/ParameterOutcomes.lean` |
| Two-player zero-sum source Nash value equals every native coarse-correlated value under the paper service | `Vegas/Game/ZeroSum.lean`, `GameTheoryExtensions/Core/ZeroSum.lean` |
| Finite decision tables preserve every legal continuation law | `GameTheoryExtensions/Protocol/FiniteInformation.lean` |
| Correlated mixtures of independently trembled finite plans retain an action-probability floor after recall conditioning | `GameTheoryExtensions/Protocol/TremblingPlans.lean`, `GameTheoryExtensions/Math/Probability/Tremble.lean` |
| Finite zero-sum saddle existence with L1 feature penalties and a security-based penalty bound | `GameTheoryExtensions/Analysis/ZeroSumRegularization.lean` |
| Identical normal-form CE correspondence does not imply SE outcome preservation | `GameTheoryExtensionsTests/CorrelatedSequentialGap.lean` |
| Zero-sum Nash equilibria can have equal expected payouts and different payout laws | `GameTheoryExtensionsTests/ZeroSumOutcomeLaws.lean` |
| Auction failure of dominance, including every faithful translation | `Vegas/Examples/CommitRevealAuction.lean` |
| SE separation for accepted named evidence, with literal declared and compiled settlement payoffs | `VegasTests/SelectiveAssociationSourceEquilibrium.lean`, `VegasTests/SelectiveAssociationSettlement.lean`, `VegasTests/SelectiveAssociationPayoffSeparation.lean` |
| Native SE with empty passive observation, all legal information sites and whole-policy deviations | `VegasTests/SelectiveAssociationRestrictedEquilibrium.lean`, `VegasTests/SelectiveAssociationRestrictedPrefixPosterior.lean`, `VegasTests/SelectiveAssociationRestrictedBeliefs.lean` |
| Isolated passive-observation change defeats preservation of that SE's payout law | `VegasTests/SelectiveAssociationRestrictedSeparation.lean` |
| Generic simulation and equilibrium transport | `GameTheoryExtensions/` |
| Paper-visible theorem selection and axiom pins | `Paper.lean` |

The proved capstones are universally quantified proofs, not conclusions
inferred from tests.

The [selective-association comparison](docs/selective-association-proof-contract.md)
keeps the compiled application, service calendar, deadlines, selector and full
bounded raw menus fixed. Empty passive observation admits a sequential
equilibrium giving Alice expected payout zero. Under the specified passive leak,
every sequentially rational assessment gives her at least one half. Therefore
even arbitrary, payoff-dependent strategy and belief translations cannot match
that equilibrium's Alice payout law. The positive proof uses one common fully
mixed Bayes sequence and checks every legal information site, including off-path
sites. Payouts are the program's signed integer settlement expressions. This
finite comparison does not establish general source-to-native SE preservation
or a result for unrestricted packets and unbounded interaction.

The source protocol and generic continuation-transfer results do not establish
native SPE preservation. Recovery has checked initialized execution laws and
local incentive guarantees, but
[`ReactiveEarlyOpeningSPE.lean`](VegasTests/ReactiveEarlyOpeningSPE.lean) proves
that the current compiler fails SPE under the specified uniform service.
The [counterexample guide](docs/early-opening-and-spe.md) explains the exact
scope, completion facts, and profitable deviation. Whole-service continuation
laws and a contract sufficient for positive native SPE preservation remain open.
The [combined service design](docs/reactive-spe-service.md) records the checked
authorization consequences and the remaining enforcement and continuation
obligations. No authorization-enforcing backend or native SPE preservation
theorem is claimed by these conditional results.
`VegasTests/SourceProtocol.lean` and
`VegasTests/SetupProtocol.lean` check information-set closure on hidden source
prefixes; `GameTheoryExtensionsTests/ContinuationTransfer.lean` proves that the
atomic irreversible-failure example has no uniform continuation-law certificate.
`VegasTests/BehavioralProtocol.lean` checks mixed binding admission with an
infinite player universe and retention of bindings after a prefix.
`VegasTests/EventService.lean` and the source/event-graph tests are concrete
execution regressions.
`VegasTests/ParameterOutcomes.lean` checks a private-bit example with identical
public marginals and different type-dependent utilities.
`VegasTests/InFlightCommitment.lean` checks binding before inclusion: reading
another pending message permits a new candidate but cannot change a transmitted
handle. `Vegas.Paper.native_commitment_binding` audits the general invariant.
The same regression checks private memory without preparation commands,
exactly one recall entry per action, and the immutable meaning of direct
submissions. Both competing packets remain includable. The native action
protocol's application cache is proved empty at every legal initialized history.
The initial-play command-service capstones do not yet cover this native game;
its source-policy compiler and continuation correspondence remain open.

## Interpretation

The native theorem concerns decoded terminal source states. Missing native
outcomes remain an explicit `Option` case. Utilities or observations of network
traffic, latency, fees, receipts, or other runtime-only data require an
additional correspondence contract.

The commitment service is ideal. Authentication, opaque commitment behavior,
relative deadlines, reserved inclusion, and a fixed finite epoch protocol are
part of the proved target model. Every epoch uses a publicly and adaptively
chosen permutation of all events, followed by one clock tick and expiry sweep;
`ServiceFeasible` requires every deadline to be at least two ticks. Wire and
order policies may adapt to public histories. This is not a generalized fair
network theorem, and the artifact establishes neither computational
cryptography nor an EVM/ledger implementation.

`Vegas.Language` is a surface-syntax prototype with an internal `SurfaceCore`
elaboration target. Its optional `Legal` predicate demands satisfiable guards;
`SourceProgram` instead admits unsatisfiable guards with failure-aware
resolution. Connecting the two requires an explicit semantic elaboration,
including deferred guard checks and publication results. The prototype has no
execution semantics and is outside the verified strategic tower.

`Paper.lean` is a self-contained capstone audit. Its statements delegate to
repository results and pin their proof dependencies; supporting lemmas remain
in their owning modules. The pins contain only `propext`, `Classical.choice`,
and `Quot.sound`. No library module or paper capstone contains a proof
admission.
The asynchronous graph compiler preserves and reflects same-error Nash at
compiled source profiles for utilities of the public source result, which is
what an outcome is. Its unilateral deviation witness is one source-policy
mixture chosen before private setup, and that deviation law is the stronger
statement, over decoded terminal source states. The graph-local scheduling theorem is separately audited.
The value-only source game also has a joint-law certificate for any fixed
reading of initial data paired with public results. Its audited Nash theorem
supports Bayesian utilities without retaining later private commitment choices.
Persistent private inputs carry ordinary values and no publication obligations.
The compiler preserves owner observations without generating commitment handles
or extra events. `Vegas.Examples.PrivateValueAuction` checks reporting under an
arbitrary finite joint valuation prior; `VegasTests.PrivateInputs` checks source
access restrictions and native resource absence. The design is documented in
[private inputs](docs/private-inputs.md).
Approximation is ex ante; no same-error interim or unrestricted native dominance
claim is implicit in it.
The asynchronous pending-message game has checked completion, full-source
honest outcome, exact unilateral-deviation mixture, and same-error Nash laws
under the concrete public epoch service. The finite source-policy mixture is
chosen before private setup, leaves every opponent unchanged, and covers any
native unilateral player policy. The public wire and adaptive order response
functions are jointly predrawn in the proof; they are not restricted to fixed
command traces.
Read the [active theorem map](docs/active-tower.md) for the
formal boundary and [event-pending deviation proof](docs/event-pending-deviation.md)
for the central adversarial argument.
