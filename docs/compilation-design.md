# Compilation design

VegasCore compiles one checked sequential source artifact into an event graph
and then into focused native public-message applications.

## Artifact boundary

Every compiler output retains the code needed by its consumer: typed fields,
node identities, dependencies, guards, rational probability tables, and payoff
expressions. Hashes and source maps can record provenance, but they do not
replace a semantic correspondence proof.

For an edge from source artifact `s` to target artifact `t`, keep four
obligations distinct:

- execution: target steps decode to source steps or justified stuttering;
- observation: target-visible information is simulated by the declared source view;
- strategy: admitted target choices can be translated without unavailable information;
- outcome: decoded terminal results and utilities satisfy the stated law.

An edge may prove only a subset. Support preservation is not progress, and
conformance tests are not refinement.

## Strategic intermediate representation

The end-to-end strategic theorem must compose two independently usable edges:

```text
checked source --strategic correspondence + graph certificates--> event graph
event graph   --native deviation simulation + resolution bounds--> message runtime
```

The backend consumes a graph and explicit structural, information, and resolution
conditions, not a source program or a proof that the graph is a compiler image.
Its unchanged opponents are arbitrary declared-read graph policies. Native
deviations are translated directly to graph policies; source backtranslation
belongs to the outer composition. Outcome interpretation and utility bounds must
also cross that boundary explicitly. `UtilitySimulation.trans` supplies the
generic composition; exact source/graph mixture simulation supplies its first
edge through `MixtureSimulationOn.toUtilitySimulation`.

One checked graph information condition is `Graph.PublicPrefixReadable`: every
commit decision declares the public node outputs preceding it in canonical graph
order. `ToEventGraph.compile_publicPrefixReadable` proves this for source compiler
outputs. Ordinary graph well-formedness only validates declared reads and does
not imply this condition, as `VegasTests.GraphPublicPrefix` demonstrates. This
condition is sufficient for the present disclosure-based extraction, not a claim
that every possible backend must require it.

`SealedFragment.commitPolicyOfDisclosures` consumes that condition directly.
`runOfDisclosures_consistent` proves its realizations agree with the extracted
choices against arbitrary unchanged graph opponents. Candidate extraction in
`SealedFragment.extractedCandidateCommitPolicy` returns this ordinary graph
policy and proves its local accepted-opening law. The source adapters delegate
to these constructions and certify the information premise.

`CommitRestriction` supplies optional legal choices at declared graph inputs.
`runPolicyNodes_restriction_expect` proves an exact change-of-law identity for
the actual graph executor under any ready node order, including samples,
dependent policies, and restrictions of zero original probability. The reference
profile leaves unselected kernels unchanged; weighting its normalized execution
by the original forced-choice probabilities computes the restriction event mass.
No second evaluator or source reconstruction is used.

`SealedFragment.candidateReplay_graph_likelihood` applies this identity to
recorded candidate preparations and arbitrary graph profiles.
`restrictedGraphRun_candidateReplay_prefix` proves that every reference graph
realization reproduces the full native replay prefix, including zero-mass cases.
The source compiler certifies that recorded-choice restriction commutes with
policy compilation; its reference-prefix theorem delegates to the graph result.

`SealedFragment.candidateGraphRun_accepted` reconstructs every openable
accepted value in pre-timeout replay from the complete graph realization.
`candidateGraphRun_registration_kernel` and
`restrictedCandidateGraphRun_registration_kernel` identify honest native
preparations with arbitrary graph kernels at their declared reads, including
throughout zero-mass reference cylinders.
`candidateGraphRun_replay_prob_eq_product` evaluates the graph replay mass as
a product of those native checkpoint probabilities, with unchanged graph
opponents. The product is indexed by actual graph nodes; no source decision
positions or source execution factorization occur in that proof.

`Graph.commitPositions` indexes native preparation factors by actual graph
commitments. `candidateReplay_registration_factor` compares each invocation
with its replay checkpoint using the same graph site and declared reads.
`candidateGraphRun_native_prefix_law` identifies the full native law through
first timeout. `candidateGraphCoupling` attaches the actual native continuation,
retains both marginals and their joint prefix/full-trace law, and proves
public-field agreement on normal completion.
`exists_randomized_candidate_graph_coupling` lifts this construction to arbitrary
randomized player and environment policies with unchanged graph opponents.
The source prefix and randomized-coupling results delegate to these backend
theorems; source outcome and payout transport occur only in their source adapters.
The stopped-round graph coupling preserves these marginals at the actual native
stopping boundary and transports normal public-field agreement to that boundary.

The strategic factoring is incomplete. Some backend modules still transitively
import mixed source/backend modules. More importantly, exclusion of a first
honest timeout under deadline-relative service must be established for the
candidate host. The all-compiled honest law must also be stated and proved
for arbitrary graph profiles; its existing source-profile theorem and honest
host embedding do not by themselves supply that independent backend law.
Legal resolution defaults
and the quitting utility bound need graph
formulations with compiler certificates, rather than a hidden source-image
premise. Only after those laws are proved can the candidate backend expose a
`UtilitySimulation` and the source-to-runtime theorem delegate to composition.
The existing source-relative results remain checked; they do not establish this
independent graph/backend certificate.

## Active lowering

The event graph is the shared dispatch artifact. The strict native edge in
`Vegas.Compile.SealedCompiler` installs one sealed-message rule per graph node
over the `Interaction` pool. Commit packets carry only an opaque handle;
opening packets carry the claimed value and are accepted only after the
corresponding commitment. Correctness is stated against actual graph
reachability and source reconstruction, avoiding a parallel operational
machine hierarchy.

The former `ApplicationPlan` public-choice image was a fused optimization
experiment, not a commitment-preserving lowering. Its source and proofs are
archived outside the build roots; it is outside the active compiler claims.

Probability tables denote exact finite laws. A concrete entropy mechanism,
cryptographic commitment scheme, concrete delivery service, or blockchain
backend would be a further artifact with its own proof edge.

## Commitment capability boundary

Source-site identity, candidate identity, and transported-message identity have
different roles. The protocol binds a site to an immutable candidate through
acceptance; a candidate may be prepared independently of that acceptance and
submitted in several messages. A site-indexed accepted-handle map need not
prohibit deliberate reuse of a candidate at compatible sites. Domain separation
is a protocol policy, not an automatic consequence of binding.

Acceptance need not certify that the sender can open a candidate. The opening
verifier's meaning must nevertheless remain fixed: accepting a currently absent
handle and later interpreting a new registration as its opening would permit
late value selection. An unopenable candidate needs a legal source failure
interpretation when it resolves. This does not license assuming extractability
or a well-typed hidden value for every arbitrary target candidate. Site-specific
typing and guard checks belong to authenticated opening validation, together
with a proof of the source continuation used on failure.

`SealedResolution.host` keeps the program rules, transport, clock, and policy
interface fixed while instantiating preparation and message admission. The
registered service admits canonical pre-registered site handles; the candidate
service admits competing and unopenable candidates. Both instantiate public
event provenance and timeout-settlement invariants. Source public-settlement
reconstruction consumes these public invariants without a service parameter.
Private candidate immutability is a separate arbitrary-policy theorem.

`SealedResolution.hostRoundDriver` supplies the same clock boundary and public
completion test to both hosts. `HandlerRecords` states the handler's successful
public effect: one event followed by a readiness refresh, with private catalog
updates unrestricted. Both handlers satisfy it. The shared `runRounds_complete`
proof therefore gives clock-driven termination under arbitrary policies in both
hosts, with no message service or preparation premise. The source compiler
discharges the enabled-rule and backward-dependency conditions, yielding
`candidateRuntime_runRounds_complete` at every sufficient round budget. This
result permits defaults; timely service is needed separately to exclude an
honest player's first timeout.

`MessageApplication.RoundDriver.runRounds_eq_tracePolicies` identifies stopped
rounds with the first completed boundary of the full native trace, or the budget
boundary if no earlier boundary completes. This shared readout theorem applies
to any message application and round driver; it has no
clock, service, or completion-persistence assumption. Both sealed hosts use this
same interface.

The compiled policies' complete finite-execution laws agree between hosts by
`SealedCompilation.candidatePolicies_law`. The compiler supplies the preparation
invariant needed for this embedding; the environment-policy retyping is
surjective and erases no observations. This law also covers delayed and timed-out
runs. Both hosts instantiate `MessageApplication.RoundDriver`; its completion
test and bounded loop are shared, and `candidateRounds_law` transports the full
honest execution law through early stopping. Under deadline-relative service,
`candidate_honest_round_payout_law` proves normal completion and the original
source payout law in the candidate driver. The candidate service's completed-round
deviation utility bound remains to be established.
The public acceptance/disclosure barrier is
independent of private registration, but that information-flow fact and a
source settlement witness alone do not provide the required strategy law.
`SealedFragment.candidateAcceptanceLaw_read_bound` proves that the focal input
and candidate catalog at first acceptance or timeout depend only on
source-earlier honest disclosures. Both commitment services use the common
policy-trace coupling lemma; the candidate relation does not equate hidden
openability. Fixed-response replay extracts the selected candidate's opening
through declared graph reads under `PublicPrefixReadable`.
`extractedCandidateSourcePolicy` is the legal source adapter to that graph policy.
`candidateGraphRun_consistent` discharges input agreement at every supported
complete graph realization, including compiled source profiles.
The registered and candidate hosts share graph-disclosure policy and execution
constructors, with source law adapters; they do not define separate evaluators.
Accepted candidate meanings remain fixed through arbitrary native suffixes.
The prefix law extends to the randomized full-trace coupling described below;
completed-round incentive comparison remains a separate step.
The legal fallback used for an absent or unopenable selection still requires
the source failure/incentive argument; constructing a source policy does not
establish that strategic comparison.

The kernel comparison uses only the values that contribute to player-side
store reconstruction: included openings and own cached values at accepted
handles. It does not require every accepted candidate to be openable.
`PreparedCandidateOwner` derives an honest owner's cache/catalog agreement
from its generated submissions, while leaving other players unrestricted;
retained-message safety includes the pool, ledger, inboxes, and sent history.
`CandidateOpeningInvariant` ties successful pre-timeout openings to accepted
handles. Together they discharge the runtime premises of
`candidate_registration_kernel`. `candidateGraphRun_accepted` proves
the accepted-value correspondence at every checkpoint in the pre-timeout
replay. It uses one common first-timeout snapshot: public selection persists,
and each accepted handle already has its immutable meaning. This retains the
focal player's extracted choices without treating unaccepted preparations as
graph decisions. Generated honest submissions name their graph sites,
and their actual caches retain their assigned graph values.
`candidateGraphRun_registration_kernel` therefore identifies the
fresh honest draw with the original graph kernel without an input-agreement
premise. Graph likelihood uses `CommitRestriction`: a partial map of owner/site
coordinates fixes selected choices, while all other kernels remain unchanged.
The candidate catalog supplies its openable honest graph slots to this map.
This projection is only a graph-event constraint;
fresh and unopenable candidates remain distinct in the native execution.
`restrictedCandidateGraphRun_replay_prefix` proves that every normalized
reference realization reproduces the full candidate prefix.
`candidateReplay_graph_likelihood` computes the graph prefix mass
as the expected forced-choice likelihood, including zero-mass cylinders and
dependent honest choices.
`restrictedCandidateGraphRun_registration_kernel` extends the original-kernel
comparison throughout the reference law. The shared policy-checkpoint theorem
uses actual invocation provenance to locate every opening's preparation strictly
before the cutoff. `candidateGraphRun_replay_prob_eq_product` evaluates
the graph prefix mass as a finite product of those native preparation
probabilities. `candidateReplay_registration_factor` compares those checkpoint
probabilities with actual invocation probabilities using the same graph reads.
The native likelihood calculation counts only openable tracked handles:
successful fresh preparation multiplies the potential by one factor, while
acceptance preserves it even when fixing an unopenable candidate. Both hosts
share the finite-product algebra and stopped-trace likelihood induction.
`candidateReplay_prefix_prob_eq_product` proves native trace mass equal to the
graph product. `candidateGraphRun_native_prefix_law` consequently
identifies the whole native prefix law through first timeout, with unchanged
opponent graph policies. Its fixed focal/environment functions may depend on
their full declared histories and observations; no positive-mass or service
premise is assumed. This is not a completed-outcome or Nash theorem.

Continuation is a shared message-runner construction, `MessageApplication.couplePrefix`.
It retains the graph realization and runs the unused native invocation suffix from
the selected prefix's complete state, preserving the exact joint prefix/full-trace
law. The candidate instantiation proves pointwise public-field agreement
with that retained graph on normal completion. Shared joint predrawing then lifts
the result to arbitrary randomized focal and environment policies in
`exists_randomized_candidate_graph_coupling`. Its graph mixture is fixed before
execution and retains every original opponent kernel. Source outcomes and
public payout agreement are transported by the source adapter. The same continuation and
joint-predrawing APIs are used by the registered host.

`exists_randomized_candidate_round_graph_coupling` reads this same coupling at
the driver's first completed round boundary, or at budget exhaustion. Its native
marginal is the actual stopped driver; its graph marginal is unchanged. Shared
host persistence proves that unused traffic cannot change a normally completed
public result. The graph fragment also certifies termination within
`nodeCount * (window + 1)` rounds, without service. The source adapter
`exists_randomized_candidate_round_source_coupling` transports the graph marginal
to written-source deviations and normal settlement to the programmed payout.

This supplies the probability part of the arbitrary-deviation argument, including
actual post-timeout execution and native stopping. The candidate round driver
still needs timely-service first-timeout attribution. The source settlement
condition can then be applied to the actual
completed native payout. Neither coupled marginal alone establishes that bound.

Candidate handles are owner-scoped identifiers. A pending handle can acquire
its private value until acceptance; an unprepared accepted handle becomes
permanently unopenable. A concrete service must justify its embedding into
these semantics, including owner scoping and the binding point. No trace
equivalence with immutable payloads fixed at submission is claimed.

## Current boundary

The direct mathematical argument for the pending-message strategic edge is in
[pending-message-strategic-proof.md](pending-message-strategic-proof.md).
It constructs a causal coupling with a legal source completion, followed by an
informed-quitting utility bound. Current theorem scope is recorded in
[active-tower.md](active-tower.md). For payout-valued utilities, the uniform
source-only `QuitPayoutBound` discharges the runtime comparison; more general
source continuation criteria still need corresponding proofs.

The written-source-to-declared-read-graph edge has a concrete strategic
certificate, `WFProgram.sourceGraphSimulation`. Its honest law compares the
actual graph runner with `denoteSource`; its arbitrary unilateral-deviation
law reconstructs one source policy without changing the opponents. Terminal
decoding preserves every source binding. Nonterminal graph states remain
undecoded, and the complete law proves that they are never returned. The edge
supports all checked core programs, including samples and validation guards,
and needs a finite player set but not finite action types. Nash and epsilon-Nash
equivalence follow at compiled graph profiles.

The event-graph edge now has a checked strategic theorem at its narrow exact
frontier. `Vegas.EventGraph.Strategic.deviation_law` and its Nash corollary
compare the graph's full behavioral presentation with the canonical
declared-read policy presentation. Under declared-read information locality
and one ready commitment per player, every canonical unilateral replacement
has the exact law of one behavioral graph replacement (not merely a mixture),
for every profile and every observation utility. This presentation theorem is
graph-level. Its hypotheses still need to be connected to checked compilation
to extend the concrete source certificate to arbitrary behavioral-frontier
policies. Neither graph theorem instantiates a message runtime.

The generic GameTheory `MixtureSimulationOn` packages exact honest-law and
finite-mixture obligations and transports all utilities of the chosen
observation. Supplying one remains an explicit proof obligation for any target;
it is not an instantiated sealed-compiler theorem. The actual pending-message
round game instead has the utility-specific conditional result described below.

The pending-message edge has an explicit causal information obligation.
`deliver` places the selected packet in the recipient's pool, and the recipient
policy sees that pool. This extra observation is not automatically a strategic
counterexample: inclusion still checks the graph prerequisites, so a pending
opening cannot produce its graph step early. A strategic proof must also
account for information obtained before inclusion. The compiled submission
barrier and native-history read bound discharge this obligation for the
admitted sealed fragment. A runtime that lets an accepted action depend on a
payload unavailable at its source decision, or lets a scheduler inspect hidden
service values, needs a stronger source observation or a separate argument
about the resulting information and incentives.

For quitting, two strategic interfaces serve different conclusions. An exact
`MixtureSimulationOn` transports every utility of the chosen source observation.
`UtilitySimulation` instead bounds the deviator's expected utility by a legal
source deviation for the utilities under analysis. It composes and implies
same-error Nash preservation and reflection at compiled profiles, but does not
by itself transport another player's worst-case guarantee.

Selective withholding requires a comparison at the information available when
the player withholds, with existing commitments fixed. Comparing always
quitting with continuing before the extra observation does not establish that
comparison. `FinDist.selective_stopping_bound` proves the quantitative rule:
if feasible continuation exceeds quitting by a margin at every supported
stopping state, then arbitrary randomized selective stopping loses at least
that margin times its stopping probability. Weak domination suffices for a
nonprofitability bound; a positive margin makes positive-probability stopping
strictly worse. The continuation values must be those of the whole program,
not merely a payment associated with the current message.

`SealedTimeout.resolved_policy_utility_bound` instantiates this reasoning with
the actual native runner after a fixed commitment. It concerns the monitored
disclosure result and assumes resolution. The adapter's expiration freezes
protocol acceptance; it neither installs a source `none` nor runs a source
continuation. The continuing `SealedResolution` runtime separately implements
missing-commitment and missing-opening resolution. Its public settlement has a
legal source realization, and the source-only payout bound constructs its
concrete utility simulation. More general conditional source continuation
criteria remain separate obligations.

The compiled opening barrier is checked independently of that resolution
problem. `SealedFragment.opening_barrier_trace` proves that when the public
opening-readiness condition first holds, every earlier commit node has a fixed
ideal-service value that persists to the end of the same actual policy trace.
All player and environment policies may randomize and adapt to their declared
observations. The theorem does not assert that readiness is ever reached or
that later quitting has the law of an earlier source decision.

No active theorem establishes general adaptive scheduling equivalence,
censorship resistance, cryptographic hiding, gas behavior, or EVM execution.

## Source and ownership constraints

Fallback behavior belongs to the source language. A timeout may select a source
choice only when the checked source artifact declares that alternative and its
guard. Compilation must not invent a nullable result, termination, or default
merely to make a runtime resolve. Ownership is likewise preserved: ordinary
choices remain owner-authorized; permissionless expiration is a separately
declared resolution action; binding openings must match the recorded binding
origin and verifier.

Feature extensions must compose over the same graph artifact. Each new runtime
detail—timeouts, public delivery, cryptographic commitments, ledger admission,
or VM execution—adds a separately typed target and a proof edge. It may not
silently fuse source nodes or invent source outcomes; the edge must state its
observation, progress, and strategic obligations explicitly.
