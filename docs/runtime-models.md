# Native public-message runtime

`Interaction` supplies the active runtime model: a public message pool,
principal-scoped commands, polling histories, receipts, delivery/inclusion
choices, and an explicit ideal commitment service.

`Vegas/Compile/SealedCompiler.lean` connects checked source programs and their
event graphs to this model. The strict edge emits one rule per graph node, so a
commit and its later reveal remain separate protocol phases. Retained game
adapters expose bounded native policy games for the sealed-message
applications.

The former fused application image and its proofs are archived under
`archive/fused/`; they are not an active compiler edge or evidence for
commitment hiding or public in-flight-message results.

Finite supported native runs,
including replay of observed messages, decode to reachable graph prefixes.
Terminal decoded prefixes reconstruct written-order source executions and
matching decoded public results. This exact prefix decoding applies to the
untimed runtime and before the first timeout in the resolving runtime.
Post-timeout settlement instead uses public-result correspondence. Ideal
hiding results concern the declared ideal service and observation boundary.

## Strategic results

The preceding source-to-graph edge has an instantiated simulation:
`WFProgram.sourceGraphSimulation` preserves the full source outcome law and
exactly backtranslates arbitrary declared-read graph policies. Its Nash and
epsilon-Nash corollaries are end-to-end to that graph runner, not to this
message runtime. It supplies the source side of the pending-message proof.

The actual pending-message round game has a constructed source/native coupling.
Its native marginal is the actual round driver, while its source marginal is a
finite mixture of legal unilateral source deviations against unchanged
opponents. Under timely service, all-compiled play has the exact original source
outcome law. For arbitrary unilateral native deviations, the strategic result
is utility domination and same-error Nash preservation/reflection, not exact
source/native outcome equality after timeout.

`RoundModel.isεNash_iff_of_checkpointDominance` accepts normal utility agreement
and comparisons at the actual first-timeout information. For programmed payout
utilities, `RoundModel.isεNash_iff_of_sourcePayoutBound` derives those premises
from timely service and a source-only `VegasCore.QuitPayoutBound`: every legal
source outcome is at or above the player's bound and every legal outcome
recording that player's configured default is at or below it. This theorem is
currently for the homogeneous, no-sample sealed fragment whose guards accept
every runtime value.
The candidate-service host also has end-to-end utility simulation and same-error
equilibrium correspondence under the source-only uniform bound.
`SealedCompilation.candidatePayoutSimulation` composes the independently proved
source/graph and graph/candidate edges. Its native policies admit competing and
unopenable commitments, malformed traffic, and arbitrary withholding. The
graph-level certificate supports public-field utilities; the source composition
in `SourcePublicCandidate.lean` supports arbitrary interpretations of the public
terminal source environment. The registered host's finer conditional incentive
criteria have not been transferred to the candidate host.
For the candidate host, `candidate_public_approximate_nash_iff`
compares legal source quitting settlements with supported unilateral continuations
against the fixed opponents, when their earlier public source environments agree.
The comparison is pointwise, and the backend proves the required joint prefix
relation. A global quitting cap and equal fixed-opponent support floor are
sufficient special cases. These theorems do not establish nontrivial guard validation, chance compilation,
heterogeneous sealed values, or concrete cryptographic/ledger refinement.
The authoritative inventory and remaining boundaries are in
[the active tower](active-tower.md).

## Pending-message and timeout boundary

The active runtime retains pending messages, recipient-local polling, public
receipts, delivery/inclusion choices, reactions, deadlines, and replay. The
strict compiler's operational theorems cover arbitrary finite native actions
through these mechanisms and reconstruct every terminal decoded prefix in the
written-order source semantics. The resolving adapter adds a public clock and
explicit expiration transitions. It retains the exact source-prefix guarantee
before timeout and supplies a legal source realization of completed public
settlement after timeout; these need not be the same private source realization.

The current delivery model deliberately exposes a recipient's delivered pool
to its policy, and the environment sees the full pending pool. Inclusion still
checks graph prerequisites, and the ideal service table is not part of either
observation. The checked causal backtranslation accounts for these public
observations and retains already registered commitments in the legal source
completion used at first timeout. A delivered or malformed packet does not by
itself take a source step.

`SealedResolution` supplies relative per-node deadlines, installs configured
defaults, and continues executing later nodes. The fixed adaptive wire may make
delivery and inclusion choices from its public observation. `RoundModel`'s
finite total and budget ensure completion. Its `Timely` premise adds roster
coverage, reserved periodic service capacity, a sufficient window, and a
whole-period schedule to exclude honest timeouts. It is not a
censorship-resistance result for an arbitrary scheduler.

The native `SealedTimeout.resolved_policy_utility_bound` covers arbitrary
randomized policy continuations of a locked disclosure checkpoint, assuming
resolution. Its utility observes only the fixed opening or expiration. The
compiled two-player regression gives an exact selective-withholding threshold
in that separate single-checkpoint adapter. That adapter freezes protocol
acceptance and does not implement the continuing `SealedResolution` settlement.

The compiled release barrier is stronger than checking the arriving opening:
the public readiness test requires earlier commitments to be complete before
an opening is submitted. `SealedShape.resolvingAcceptanceLaw_read_bound`
proves that future hidden values do not affect the focal player's local input
through first acceptance or timeout. In the current registered-handle service,
`SealedFragment.opening_barrier_trace` additionally fixes every earlier
commitment at the opening-ready snapshot and preserves its value through the
complete policy trace.

Local handler validity alone supplies no liveness. The resolving driver adds
the explicit service assumptions above; malformed traffic, withholding, and
wire choices remain part of the modeled behavior. Censorship tolerance beyond
that service contract, concrete cryptography, and blockchain realization
require additional models and proofs. See [the active tower](active-tower.md)
for the exact current feature and theorem boundary.
