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
| Source to typed graph and canonical single-policy correspondence | `Vegas/Compile/EventGraphCanonical.lean`, `Vegas/Compile/EventGraphDeviation.lean` |
| Sequential completion by dependency barriers | `Vegas/EventGraph/Sequential.lean` |
| Message transport and player policies | `Interaction/MessageApplication.lean`, `Interaction/MessageApplicationPolicies.lean` |
| Event-addressed runtime and service | `Vegas/Pending/EventApplication.lean`, `Vegas/Pending/EventService.lean` |
| Binding from authenticated submission through arbitrary native continuations | `Vegas/Pending/EventCommitmentBinding.lean` |
| Multiplayer atomic-response protocol, policy equivalence, and bounded native execution | `Vegas/Pending/ResponseProtocol.lean`, `Vegas/Pending/ResponseProtocolPolicy.lean`, `Vegas/Pending/ResponseProtocolEvaluation.lean`, `Vegas/Pending/ResponseProtocolNative.lean` |
| Full-source honest law under adaptive public graph scheduling | `Vegas/Compile/EventGraphScheduling.lean` |
| Full-source asynchronous deviations and Nash correspondence | `Vegas/Compile/EventGraphDeviation.lean`, `Vegas/Game/EventCompilation.lean` |
| Asynchronous pending-message service and arbitrary-player completion | `Vegas/Pending/EventService.lean`, `Vegas/Pending/EventServiceCompletion.lean` |
| Asynchronous pending-message deviation reduction | `Vegas/Pending/EventDeviationLaw.lean`, `Vegas/Pending/EventStrategicLaw.lean` |
| Full-source pending-message deviations and Nash correspondence | `Vegas/Game/EventMessageStrategic.lean` |
| Initial-parameter/public-result joint laws and Bayesian Nash correspondence | `Vegas/Source/InitialState.lean`, `Vegas/Game/ParameterOutcomes.lean` |
| Auction failure of dominance, including every faithful translation | `Vegas/Examples/CommitRevealAuction.lean` |
| Generic simulation and equilibrium transport | `GameTheoryExtensions/` |
| Paper-visible theorem selection and axiom pins | `Paper.lean` |

The proved capstones are universally quantified proofs, not conclusions
inferred from tests.
The source protocol and generic continuation-transfer results do not establish
native SPE preservation. Source/native continuation laws, response compilation,
policy recovery, and proper-root coverage remain open. `VegasTests/SourceProtocol.lean` and
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
