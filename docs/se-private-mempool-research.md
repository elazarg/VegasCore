# Concurrent SE preservation with private mempool observations

Concurrent preservation without complete pending observation remains unproved
and unrefuted here, even with the current reserved-service assumptions retained.
The finite results in this survey do not establish a weakening of the current
runtime theorem. A separate [ledger-publication construction](se-private-mempool-proof-routes.md)
gives a finite hand preservation proof for a compiler that inserts deterministic
public padding before later commitment blocks. It retains concurrent commitments,
individual failure rules and private mempool reception. Its compiler and proof
adapters have not been implemented in Lean.

One proposed replacement for complete pending observation is to keep
unseen submissions **latent**, aggregate their probabilities inside each actual
player information set, and compare the resulting deviation gains with mixtures
of legal source deviations. The existing SE limit theorem already accepts such
mixtures. A second route is to prove that a complete-observation construction,
including its perturbations, factors through the smaller actual observations.

The deductions and diagnostics below establish narrower facts, identify exact
missing adapters, and specify how a genuine counterexample could be found.

The [mathematical foundations](se-private-mempool-mathematics.md) give full finite
proofs: private-noise preservation, the obstruction to limit-only coarsening,
sharp posterior transport, conditional error control, simultaneous completion
and exact finite decision procedures. The
[compiler and incentive analysis](se-private-mempool-compilation.md) separates
rollback from the runtime observation model and examines absorbing-abort
compilation, waiting, penalties and the cost of payoff floors. These are
mathematical research results, not newly checked runtime preservation theorems.

## Keep the target and information boundary explicit

The objective is the intended commit–reveal game implemented on an idealized
realistic blockchain. Rollback, the enlarged source game for silence and other
recovery machinery are means toward that objective. The unchanged implementation
is one useful comparison, not a requirement on every solution.

That comparison keeps the source game, selected source SE, joint
initial law, `.concurrent` graph, phase rollback/exit semantics, reserved service
prior, deadlines, utility floor and funded audit fixed. Change only pending
observation. Preserve the same initialized joint law of inputs, typed terminal
state, public result and realized net payoffs, with no on-path exclusions or
charges. The current graph permits concurrent commitments between public
barriers; it does not permit arbitrary concurrent reveals. A counterexample
using concurrent reveals or a content-adaptive builder would not answer this
first question. See [the precise concurrent contract](se-concurrent-mechanization.md).

The publication construction addresses a different, concrete compiler choice:
the ledger actually records earlier opening payloads before a new binding
becomes available. It does not declare private mempool contents public.

Players may use their private inputs, own actions, receipts, ledger observations
and the messages their own observation process actually delivers. The proof may
inspect hidden global variables; the strategies may not. No public signal is
added merely because a proof needs to distinguish two hidden histories.

A useful progression of models is:

| Model | Observations available to a player | Purpose and limit |
|---|---|---|
| Ledger-only | Own recall and the existing ledger/application view; no pending leaks | First exact weakening in the current observation API; isolates loss of archive knowledge without adding random observation transitions |
| Private subsampling | At each activation, each available packet is received with a fixed receiver-specific probability; reception remains private | A finite selective-visibility model in the current API; probabilities remain fixed throughout the SE consistency sequence |
| Stateful gossip | Local delivery queues, packet ages, prior receptions and routing state determine private arrivals | Models persistent delays and correlated reception; needs observation-process state beyond the current stateless kernel |
| Private relay | Some recipients can see an envelope while other players cannot | Useful observation pattern; a strategically adaptive relay/builder requires a separate service analysis |
| Inclusion-gated encryption | Plaintext becomes available after an actual inclusion/decryption condition | Protocol redesign with cryptographic and availability assumptions, not simply deletion of the observation hypothesis |

These distinctions reflect deployed interfaces. Geth exposes a node's pending
and queued transactions and allows pool limits, replacement and expiry;
Flashbots Protect sends transactions through a private mempool. These sources
do not supply a deterministic global dissemination bound.
[Geth transaction-pool API](https://geth.ethereum.org/docs/interacting-with-geth/rpc/ns-txpool),
[Geth pool configuration](https://geth.ethereum.org/docs/fundamentals/command-line-options),
[Flashbots Protect](https://docs.flashbots.net/flashbots-protect/overview).

The current
[`Interaction.MessageNetwork.ObservationRule`](../Interaction/MessageNetwork.lean)
takes only the observer and current pending list. It can represent private
subsampling and recipient-dependent rules, but not arbitrary persistent gossip
state or packet-age dependence. The receiver retains learned envelopes. Adding
a hidden transport state is different from adding player observations or
exposing observation samples to the scheduler.

The carrier also retains every submitted envelope pending or in the ledger;
complete-observation readback uses that invariant. Eviction of one node's local
copy can be modeled as loss of that node's visibility while another copy remains
available. Disappearance from the service itself changes retention/delivery
semantics, not just the leak rule. Neither a local-mempool observation model nor
the references above validate the reserved service's processing guarantees.

## Complete observation has three proof roles

The field in
[`Vegas.ReservedConcurrentImplementation.Operational`](../Vegas/Game/ConcurrentRawSequentialPreservation.lean)
is an equality to
[`Interaction.MessageNetwork.completePendingObservation`](../Interaction/CompletePendingObservation.lean).
It selects every pending identifier deterministically. At an actual activation,
foreign submitted envelopes are in the player's leaked view or the ledger;
own submissions are in recall. This is additional pre-inclusion observation,
not a consequence of ledger consensus.

| Role | Exact use | Replacement obligation |
|---|---|---|
| Archive readback | [`Vegas.EventGraphRuntime.PhaseProposal.observedSourceArchive_eq_submitted`](../Vegas/Game/PhaseProposalSourceArchive.lean) identifies the locally observed typed archive with all submitted publication proposals | Prove only relevant archive material is observable, or integrate over unobserved archives |
| Information and policy alignment | [Canonical source-information comparisons](../Vegas/Game/PhaseProposalNativeSourceInformation.lean) and [the physical source query](../Vegas/Game/PhaseProposalQuery.lean) use that readback | Derive source comparisons from actual local information; prescriptions cannot select a hidden archive |
| Replay and probability accounting | [Raw replay](../Vegas/Game/QualifiedBinding/RawReplay.lean) uses deterministic activation successors; [likelihood accounting](../Vegas/Game/QualifiedBinding/Likelihood.lean) gives nonsample environment steps mass one | Carry observation probabilities and sum over private observation histories; replay uniqueness cannot be assumed |

The policy dependence is visible in
[`Vegas.SourceProgram.Setup.ProposalRecoveryComponent`](../Vegas/Game/ProposalRecoveryPrescription.lean):
its key contains source recovery information and a typed proposal archive.
[`Vegas.SourceProgram.Setup.proposalRecoveryPooledDomainLaw`](../Vegas/Game/ProposalRecoveryPools.lean)
allows distinct optimized weights at distinct archive keys. There is no
established theorem that those weights can all be chosen archive-independent.

The deterministic-replay premise actually fails for a nondegenerate private
observation kernel. Fix a state containing one foreign pending envelope and
activate a receiver who does not know it. If receiving and not receiving each
have positive probability, the two successors have different private leaked
views, but the same pending pool, application and receipts. Consequently their
scheduler observations coincide while the executions differ. The current
[`Interaction.ReactiveApplication.Execution.observeEnvironment`](../Interaction/ReactiveApplication.lean)
does not expose private leak samples. Neither observation branch has mass one.
This is a direct semantic obstruction to those replay lemmas, not to SE
preservation. Publishing the samples would change the information model and
would not repair the intended theorem.

## Route one: integrate over hidden archives

### A finite sufficient condition with a short proof

Fix a perturbation index \(n\), player, and actual native information set
\(I\). Let \(r^N_n(h)\) and \(r^S_n(g)\) be native and source reach masses.
For this calculation assume all histories in \(I\) are regular. Suppose their
projection has the following **summed** fiber identity:

\[
 \sum_{h\in I:\,\pi(h)=g}r^N_n(h)
   =c_{n,I,J(g)}r^S_n(g),\qquad c_{n,I,J}\ge0,
\]

where \(J(g)\) is the player's source information set. Let
\(M^S_n(J)=\sum_{g\in J}r^S_n(g)\) and assume the total mass
\(Z=\sum_J c_{n,I,J}M^S_n(J)>0\). Dividing by \(Z\) gives

\[
 \pi_*\mu^N_n(\cdot\mid I)
 =\sum_J w_{n,I,J}\,\mu^S_n(\cdot\mid J),\qquad
 w_{n,I,J}=\frac{c_{n,I,J}M^S_n(J)}{Z}.
\]

Thus one native site may correspond to a mixture of source sites. No player
needs to observe the mixture component. This is an elementary finite
calculation, not a new checked Lean theorem. The existing
[`GameTheory.Protocol.InformationModel.bayesBelief_projection_of_proportional_reach`](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean)
provides the single-source-site version; the mixture requires aggregation.
Applying this calculation only to the regular portion of a site gives its
regular conditional posterior. Recovering a bound for the entire site then
requires a separate bound on the conditional mass and payoff effect of
irregular histories.

If, additionally, **each actual native local alternative** has its continuation
gain bounded by the same mixture of legal source deviation gains, plus a
uniform error \(\eta_n\to0\), then this is exactly the kind of comparison
accepted by
[`GameTheory.Protocol.InformationModel.sequentialEquilibrium_of_copied_comparisons_limit_of_lawError`](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean).
That theorem also requires the common consistent target limit, source
convergence/rationality, initialized-law convergence and optimality at any
uncopied sites. It has finite-history hypotheses; the capstone's broader nature
scope needs its existing finiteness/restriction reductions as well.

**The missing work is the producer, not a new SE limit principle.** Hidden
archives, candidate meanings and private transport randomness can all remain
proof variables. Their summed weights must satisfy the fiber identity or a
suitable gain comparison under the actual observation kernel.

### What does not follow from this calculation

A posterior over hidden histories is not automatically a mixture of **source
Bayes posteriors**. Selecting a source action separately at each hidden state
would give the simulated player information it does not possess. The fiber
coefficients above are constant within each source information set; arbitrary
history-dependent coefficients do not have that property. Alternatively, a
signed-gain comparison must account for the resulting likelihood tilt.

Even content-blind packet reception can convey information. Suppose a hidden
bit determines whether there are one or two relevant pending messages, with
equal prior probability. Independently receive each with probability \(q\).
After receiving none,

\[
 P(\text{two}\mid\text{none})
 =\frac{(1-q)^2}{(1-q)+(1-q)^2}
 =\frac{1-q}{2-q}.
\]

At \(q=1/2\), this is \(1/3\), not \(1/2\). Receipt probabilities do not
depend on the message contents, yet absence changes beliefs about the hidden
state. Independence of the observation coins from inputs does not remove this
selection effect.

The [posterior-gain covariance APIs](../GameTheoryExtensions/Math/Probability/KernelPosteriorGain.lean)
can express such effects. Their runtime inputs still need to be proved. A
fixed chance of missing a packet cannot be charged as a vanishing tremble
error; the mempool law is fixed, while only behavioral perturbations vary.

### Observation randomness in replay

A finite observation kernel can be represented using hidden random choices.
Replay may retain their outcomes as internal annotations, transport them by a
measure-preserving map where available, and sum them out. It must use the
actual transition probabilities, rather than the current mass-one identity.
For independent per-packet reception, packet-renaming symmetry is a possible
local coupling. Extra hidden packets still contribute missed-reception factors;
their cancellation must be proved or their posterior effect retained.

An annotation may help distinguish replay histories without being visible to
the scheduler or any player. This repairs a proof representation, not a game
observation. For stateful gossip, the same accounting must preserve the hidden
transport state's correlations across activations; resampling a fresh unrelated
delivery process at each block is not valid.

## Route two: descend a construction through smaller observations

Here is a second finite sufficient argument. Consider the same game tree,
chance laws and payoffs with fine and coarse information partitions. Both
information models have perfect recall, their legal action menus agree, and
the coarse decision sets are antichains.
Suppose there is a common fully mixed sequence \(\sigma_n\) such that:

1. Every player's policy at every \(n\) is constant on each coarse information
   set, including off-path sets.
2. Under the fine Bayes assessments, every local deviation gain is at most
   \(\eta_n\), uniformly, where \(\eta_n\to0\).
3. Its initialized joint observation law converges to the selected source law.

For a coarse site \(I\) partitioned into fine sites \(J\), its Bayes belief
is the reach-weighted mixture of the fine Bayes beliefs. Since the same local
alternative is legal throughout \(I\), and the profile factors through coarse
information, its local gain satisfies

\[
 G_n(I,a)=\sum_{J\subseteq I}
       P_n(J\mid I)G_n(J,a)\le\eta_n.
\]

A common convergent subsequence of the finite assessments supplies coarse
consistency and local optimality; perfect recall gives sequential rationality.
The initialized law is unchanged because the strategies and underlying
transition laws are unchanged. This is a paper proof of a sufficient finite
inheritance statement, not an implemented Vegas adapter.

The condition applies to the **whole sequence**, not just its limit. Fine
perturbations that vary with hidden archives may generate beliefs that cannot
arise from any coarse legal sequence. Also, changing from complete observation
to stochastic leaks is not literally just coarsening the present game tree:
first one must couple or represent the private observation randomness on a
common underlying tree, with the correct law.

The practical experiment is to constrain completion weights to depend only on
actual local observations, then prove the required gain bounds. Existing
[common-best component results](se-correlated-prior-research.md#first-target-a-common-best-choice-not-a-common-full-belief)
may help. Requiring a common near-best action at every fine site is sufficient
but stronger than optimality under their coarse posterior mixture. Failure of
that intersection is not a counterexample to coarse SE existence.

## Route three: local errors and one legal consistency sequence

Geffner and Halpern construct consistent beliefs for communication protocols
that favor certain explanations of observed errors, using carefully separated
tremble rates. Their mediator-implementation results include a synchronous
threshold \(n>3k\), and the cited full version treats an asynchronous case with
\(n>4k\). This shows that private/asynchronous communication does not by itself
rule out SE implementation. Their protocols, communication primitives,
termination and scheduler treatment differ from Vegas.
[Communication games, sequential equilibrium, and mediators](https://arxiv.org/html/2309.14618).

The proposed application is to construct beliefs at a player's **actual
private** mempool view, rather than first making all proposals public. Where
the runtime admits suitable information-preserving repairs, progressively
rarer earlier mistakes can make a locally observed anomaly unlikely to imply
an unrelated harmful mistake elsewhere. This needs a repair for each relevant
observation fiber, including canceled attempts and unusable preparations.

The communication theorem is not a drop-in result: a single mempool envelope
may be observed by several recipients, whereas independently addressed messages
allow different perturbations. Reception and scheduler probabilities in Vegas
are fixed; the proof must not perturb them to favor desired explanations.
Only legal player actions receive trembles.

For finite instances, use the existing
[power-certificate soundness](../GameTheoryExtensions/Analysis/Protocol/PowerCertificate.lean)
and [completeness](../GameTheoryExtensions/Analysis/Protocol/PowerCompleteness.lean)
to test the desired beliefs against one shared set of action exponents and
positive coefficients. Positive fixed reception probabilities enter leading
coefficients; impossible receptions remove histories. A contradiction in these
constraints rejects that belief prescription, not every possible preserving SE.

The broader [USI/MSI results](se-preservation-research-survey.md#sufficient-information-and-preservation-of-se-payoffs)
are useful comparison tools, but their factorization conditions cannot be
inferred from causal or content-blind gossip. They concern SE payoff sets;
preserving this selected initialized joint law requires additional work.

## Protocol alternatives that use the ledger for public facts

**Ledger barriers.** Enable a source-dependent choice only after the ledger
contains the effective public data on which that source choice depends.
Concurrent hidden commitments can remain concurrent. This is a realistic
kind of service condition to investigate, and the current phase structure
already provides relevant barriers. The missing argument concerns private
knowledge of ineffective or stale openings across retries, not merely the
honest public-store progression.

Publishing every old submission is neither necessary by definition nor an
automatic solution. Arbitrarily late stale envelopes can appear after a
barrier. The proof must identify a closed set of relevant disclosures and show
that the rest cannot change the needed continuation gains, or model their
private effects explicitly. A contract cannot erase plaintext already leaked.

**Suppress ineffective disclosure in the prescribed client.** The existing
[opening encoder](../Vegas/Game/SourcePhaseClientOpening.lean) and
[`Vegas.sourcePhase_effective_disclosure_foreign_information`](../Vegas/Game/SourcePhaseDisclosure.lean)
provide concrete local facts: an ineffective opening can be represented by
silence while preserving the stated source information. This is useful input
to an observation-faithful compiler. It does not exclude adversarial openings
or fully mixed off-path mistakes and does not establish concurrent SE.

**Inclusion-gated plaintext.** Threshold-encrypted mempools aim to release
plaintext after a commitment to inclusion/order. This could align effective
disclosure with the ledger. Shutter's research describes this design and the
additional trust/liveness assumptions; it also identifies the danger of
decrypting transactions that were not included. Epoch-wide release is therefore
not interchangeable with inclusion-gated release.
[Shutter encrypted-mempool research](https://docs.shutter.network/docs/shutter/research/the_road_towards_an_encrypted_mempool_on_ethereum).
This is a separate protocol proposal requiring authorization and a new adapter,
not a claim about the existing plaintext runtime.

## What can be refuted cleanly

### A necessary-information diagnostic

Let \(\theta\) be a fair bit publicly revealed before a source decision. The
decision maker chooses \(a\in\{0,1\}\), receiving \(1[a=\theta]\).
The source SE has \(a=\theta\) surely. Suppose a candidate implementation
instead requires that decision before ledger publication; a pending message
reveals the bit with probability \(1-\delta\), independently of its value,
and otherwise produces an erasure. There is no other informative observation
or communication channel before the decision.

On erasure, every legal mixed choice is independent of \(\theta\), so its
success probability is \(1/2\). Hence **every** implementation policy has
\(P(a=\theta)\le1-\delta/2\). For \(\delta>0\), no policy can preserve the
source joint law, even before imposing equilibrium. The total-variation
distance from that law is at least \(\delta/2\), witnessed by the event
\(a=\theta\). This is an elementary finite impossibility proof for that
implementation, not a Vegas counterexample: it would require showing that
the actual phase rules permit this premature decision. The existing public
barriers are specifically relevant to excluding it.

This diagnostic rules out the proposition that eventual delivery or
arbitrarily reliable pre-decision visibility is enough for **exact** universal
preservation when indispensable source information can still be absent.
Waiting for actual ledger disclosure removes this particular obstruction.

### Why almost-public is not automatically sufficient

Rubinstein's electronic-mail game demonstrates that long finite hierarchies
of mutual knowledge can have different equilibrium implications from common
knowledge. Halpern and Moses analyze which communication assumptions allow
different forms of group knowledge. These warn against replacing a public fact
by high-probability dissemination without an incentive argument; neither is
a counterexample to the reserved-service phase runtime.
[The Electronic Mail Game](https://arielrubinstein.org/papers/32.pdf),
[Knowledge and Common Knowledge in a Distributed Environment](https://groups.csail.mit.edu/tds/papers/Halpern/JACM90.pdf).

### Search for a genuine finite runtime obstruction

Use the actual concurrent-binding runtime with two or three players, Boolean
values, a correlated finite initial law, one retry opportunity, and a fixed
reserved tape satisfying all resource conditions. Vary only a supported private
observation kernel. Track the joint input/output law, not merely expected payoffs.
Promising hard cases involve an opening observed by one surviving player but
not another, followed by a rollback and fresh commitments. First determine
whether that situation is possible under the actual guards and service.

For a concrete finite rational instance with a specified rational target joint
law, a complete mathematical search can
in principle enumerate strategy and belief support patterns. For each pattern:

1. Shared action orders must satisfy the finite linear equalities/strict
   inequalities selecting the leading histories at every information set.
   Homogeneity permits integer scaling of feasible rational orders.
2. Positive leading coefficients, limit strategy probabilities and beliefs
   satisfy the polynomial ratio/normalization constraints from actual reaches.
   Fixed chance probabilities, including reception, remain coefficients.
3. Sequential rationality and the exact selected joint law impose further
   polynomial constraints on these finite variables.

The power-completeness theorem justifies considering such certificates for
finite menus and histories. This is a proposed finite decision procedure,
not an implemented compiler or a practical complexity bound. A bounded
exponent search, one failed support pattern, or one failed compiled strategy
is insufficient to exclude all preserving SEs. A successful refutation needs
an exhaustive argument or a direct incentive/information obstruction, plus
the actual runtime realization and all retained hypotheses.

## Recommended proof order and ownership

| Owner | Bounded task | Acceptance criterion |
|---|---|---|
| Vegas research | Ledger-only observation with the existing reserved service | Either a real preservation producer for the current phase semantics, or a realized counterexample retaining every other capstone premise |
| Vegas information/probability layer | Replace one-source-site readback by summed fibers or signed gain comparisons | Actual local policies, actual conditional probabilities, all legal deviations, one common sequence |
| GameTheory/local extensions | Reuse the mixture-capable SE limit consumer; add a finite information-coarsening adapter only when consumed | A producer instantiates it; no hypothesis merely restates the desired preservation |
| Interaction plus Vegas adapter | Private subsampling, then stateful gossip accounting | Observation randomness stays private; replay masses and correlations are retained rather than assumed away |
| Vegas protocol design | Ledger barriers or inclusion-gated plaintext if needed | Explicit additional service/crypto premises and a proved information correspondence; no silent change to the current target |
| Multitubes | Optional latent-kernel/observable transport example after a useful instance exists | A compositional result with the actual information and gain obligations; no new dependency needed merely to express mixtures |

The ledger-only case should precede noisy gossip: it isolates the archive
problem while retaining deterministic observations. The noisy case then tests
the genuinely new replay probabilities. A theorem for either must retain the
actual initialized joint law and sequential consistency; a Nash-only port or
an honest-path simulation is useful evidence but does not close this gap.

Relevant bibliography keys in `overleaf/vegas-paper.bib` are
`GethTxpoolDocumentation`, `FlashbotsProtectDocumentation`,
`ShutterEncryptedMempoolResearch`, `Rubinstein1989ElectronicMail`,
`HalpernMoses1990Knowledge`, `GEFFNER2024105890`,
`TangSubramanianTeneketzis2026`, and `HalpernPassSeeman2016`.
The last source's computational representation approach is discussed in
[the literature note](commit-reveal-research/literature.md); its computational
equilibrium notion and implementation hypotheses remain distinct from this
finite ideal-runtime question.
