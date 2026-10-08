# Candidate ledger interfaces and their mathematical results

This catalog compares alternatives. **It does not designate any alternative as
the VegasCore model.** A result in one row does not inherit the assumptions or
conclusion of another. All new results here are written mathematics, not new
Lean theorems. Proofs and complete source/target games are in the linked tracks.

Start with the physical question: who controls submission and release, what
others learn before their decisions, how long publication may take, and what
an actual deviation costs. Then choose the preservation claim. “Preserves”
below means implements every selected source equilibrium outcome unless a row
explicitly says it reflects all target equilibria.

## Interfaces worth comparing

| Candidate interface | Model reminder | Result or status | Main unresolved obligation |
| --- | --- | --- | --- |
| Public plaintext with observation windows | Owners know their values and can send or wait. Inclusion and recipient delivery have separate bounds. Stale and rejected plaintext remains known. | A physically intelligible candidate; complete observation can help particular disclosure games. No general theorem for this interface. | Timing, early proofs, retries and logical failure can disclose information absent from the source. |
| Ciphertexts selectively released after final admission | Envelopes and fees are visible. Only finalized, authorized ciphertexts are decrypted; excluded inputs stay sealed when the source requires secrecy. Owners may still know their plaintext. | Candidate release mechanism, not a complete preservation theorem. | Final admission, available honest key holders, release transport, metadata and owner-originated plaintext channels. |
| Causal ledger barriers | A successor cannot update the contract before its predecessor is final. Premature packets can nevertheless be read. | Controls application order. The early-proof counterexample shows why this alone does not control information. | Opacity or credible deterrence for premature disclosure; source-compatible receipt and deadline behavior. |
| Private intake and mandatory public dispatch | Players choose exactly source actions through private intake. A funded service emits padded envelopes and original observation increments; waiting is public chance with a finite budget. | Exact SE preservation, including retained private state: paper theorem. | A restricted mediated interface. Extra physical actions and side channels need a separate extension proof. |
| Audited first departures | An exact retained game is embedded in a larger finite action space. Its histories are uncharged. Every first excluded action leaves evidence with a uniform collection probability under every later strategy. | A finite deposit supports SE extension under the existing abstract completion theorem. | Derive the evidence and collection floor from the physical service. Accepted late calls are not automatically offences. |
| Fresh collateral for separately evidenced actions | Each future offence has an unused tranche, with automatic or probabilistic collection. The number of tranches and their funding are finite and specified. | Useful enforcement interface for local comparisons; see the service track. | Source-compatible extra messages, off-path consistency and complete-game composition still need proof. |
| One capped escrow already charged | A prior charge exhausts the only penalty. Later actions cannot cause additional collection. | Increasing that escrow cannot deter a subsequent positive-gain action by itself. | This is a local obstruction; a dirty suffix reached only through a deterred departure does not refute forward preservation. |
| Fixed finite game with noisy chance and costs | Actions, observations and recall stay fixed. Chance errors are uniformly small at every source-compatible history; payoff errors are uniformly bounded. | Every source SE has exactly consistent approximate target assessments: paper theorem. | Prove this fixed-game representation for physical messages, fees, retries and newly reachable histories. |
| Fixed positive chance support and strict pure incentives | Same finite actions and information; no new chance branch. A pure source SE has a positive conditional action margin at every decision. | The same pure policy is a target SE for sufficiently small chance and payoff errors: paper theorem. Its outcome law is close, not generally identical. | Mixed equilibria, new observations, added actions and rare newly enabled branches are outside this result. |
| Source explicitly includes service failures | The abstract game has the same specified failure, abort and observation branches as its implementation. | Candidate way to avoid comparing a failure-prone service to guaranteed abstract publication. | Failures affected by bids, timing or private service knowledge must be represented faithfully, rather than replaced by an unrelated fixed coin. |
| Eventual publication without a fixed physical deadline | The source has finitely many logical steps, but physical execution can wait longer for service. | Candidate alternative to finite-horizon exact-law obstruction. No general SE theorem here. | Termination, discounting, costs of locked funds and equilibrium analysis of an unbounded physical game. |

The first four mechanisms and their disclosure proofs are in
[Information and release](information-and-release.md). Enforcement mechanisms
and finite-horizon limits are in
[Service and enforcement](service-and-enforcement.md). Robustness conditions
and error bounds are in
[Preservation and robustness](preservation-and-robustness.md).

Some rows describe transport, some describe enforcement, and some describe the
entire mathematical game. They can be combined only after their actions,
observations, costs and failure rules have been shown compatible.

## Simplifications and small producer tests

These results clarify model choices without introducing a new adopted runtime.
The [decision note](model-decisions.md) explains which details can be erased,
which can be bounded, and which remain outside a theorem's scope.

| Candidate | Model reminder | Result and scope |
| --- | --- | --- |
| Full remembered auxiliary observations | Finite chance-only processing; source menus, logical kernels and utilities unchanged at every runtime record. Each player's full auxiliary replay channel is constant across its compatible hidden source histories. | Paper exact forward SE preservation, with retained secrets and correlated private observations. One common consistency sequence; whole adaptive policies covered. No extra submissions, fees, strategic producer or coalition guarantee. [Proof and failures](observation-abstraction.md). |
| Discounted bounded public waiting | Post-funding additive utility; fixed logical settlement horizon; bounded extra physical wait and terminal fees/financing bills. No new menus, private signals or admission choices. | Paper exact logical-law and consistency preservation, with regret at most twice the uniform utility error. Strict pure all-site margins larger than that error give exact SE. Entry, nonlinear cash utility and raw actions are separate. [Bound and counterexamples](costs-and-scope.md). |
| Enough block capacity with delivery and finality bounds | Every permitted workload fits; work-conserving blocks have bounded gaps; plaintext reaches all observers within a public bound. | Paper inclusion bound and complete-observation lemma when physical emission cutoff precedes the irreversible decision by enough slack. Restricted single-phase application under its separate assumptions; no general sequence theorem. [Model and limits](honest-producer-models.md#candidate-one-enough-capacity-and-bounded-delivery). |
| One-slot fee-maximizing production | Independent competing load; fixed-fee independent opening identifiers; bounded but unequal observer delays; restricted scheduled observations and an explicitly collectible terminal audit. | Paper mandatory-opening negative at high late reliability and the stated forfeit/audit thresholds, with actual accepted-call fees. Producers need no collusion. Not a native theorem, unrestricted bidding model or lawful-refusal negative. [Complete interface and proof](honest-producer-models.md#candidate-two-one-opening-slot-and-maximum-fee-revenue). |

Source-independent runtime information can still predict costs or the loss of
an action. The observation-channel theorem therefore needs execution and utility
conditions as well as secrecy. Its tests use the full remembered record: two
individually uninformative packets can jointly disclose a hidden value. A fixed
cash fee also need not cancel under nonlinear utility over wealth. These are
complete finite counterexamples in the linked notes, not warnings inferred from
a hypothetical native attack.

**Auditable public fee policy.** The fixed bid in the producer comparison is a
restricted assumption, not an implication of auditability. A public bidding
rule can permit variable actual fees. If every first fee-rule departure has
authentic persistent evidence and fresh collection probability at least alpha
under every later policy, additive base rewards in [L,U] and retained total
fees at most F give the conditional bound K>=(U-L+F)/alpha. This is a paper
incentive lemma; structural source fidelity, funding and consistent completion
are additional requirements. It covers included departures, not merely dropped
packets. Controlled bids can also generate new signaling equilibria even with
identical inclusion. [Policy, proof and scope](fee-policy.md).

## Operational information and accepted late actions

These results distinguish physically present observations from changes in
strategic information. They also distinguish a protected restricted game from
the full submission game; a positive in the former is not a positive in the
latter.

| Result | Interface reminder | Conclusion and boundary |
| --- | --- | --- |
| Compositional exact preservation | Finite perfect-recall source; bounded sure runtime processing; source actions may have uncharged implementation aliases. Every alias preserves conditional logical execution and utility. One fixed full-support alias rule makes the full remembered observation channel equal across each source information set. Excluded raw actions satisfy the actual structural, soundness and uniform first-departure collection premises. | Paper clean-game constructor plus checked audit-extension theorem; collateral depends on public utility and collection bounds before the builder and equilibrium. Exact forward implementation, not reflection or a native RAW instantiation. [Proof and local necessity test](universal-preservation-criterion.md). |
| Protected serial native play | Canonical value-only opaque bindings; effective openings; every instruction waits for its serial predecessors. Source decisions occur once at protected opportunities; other activations offer silence. Actual pending packets, private samples, receipts and own recall remain observable. | Paper exact SE preservation with retained secrets, lawful source withholding and nonuniform bounded waits. Actual public input coupling supplies the information argument. Late sends, retries, malformed packets and the guarded-intention adapter remain outside the result. [Primitive argument](native-observation-criterion.md). |
| Actual first-ready native restriction | Well-formed intended mandatory-action source; every legal guard-accepting commitment value is available. The actual serial runtime keeps its adaptive clock and activation commands, private catalogues, pending samples and complete recall. Owners use canonical packets at their first ready responses; all other physical responses offer only silence. | Independently reviewed paper exact SE preservation and initialized joint parameter/result/net-payoff law for every declared timely contract scheduler. One copied policy works across that class. Adaptive stopped-prefix replay and local continuation adapters are proved on paper, with checked ingredients identified separately. This is a strict physical restriction, not preservation in the full raw menu; late sends, retries and other extra packets remain excluded. [Proof and exact scope](native-protected-execution.md), [API and remaining-obligation map](native-foundation-obligations.md). |
| Full native raw menu with two late openings | Actual serial program: Alice opens an immutable initial bit, Bob binds and opens an answer. Alice also knows an uncertified private label. Native candidate preparation, malformed calls, aliases, evidence, extra identifiers and every bounded raw response are available. Fixed D>max(R,1), K_A>R, K_B>1; authentic complete traffic audit, or its explicitly bounded partial-coverage variant. | Independently reviewed paper negative. For every fixed collateral configuration above those thresholds and partial pending-observation probability in (0,1), an explicit sufficiently reliable late builder admits no SE preserving the selected source joint parameter/result/net-payoff law. The builder satisfies the all-history timely contract and optional all-view late-packet blindness; leaks are author-only. Remaining tasks are Lean formalization. Not target-SE nonexistence, PBE impossibility or a deployed-chain theorem. [Native construction and proof](native-late-action-analysis.md). |
| One late fixed-value opening | Finite sender types, one immutable disclosure, protected Open or Defer followed by one Send/Never choice; receiver acts only after resolution. Sender gross reward in [0,R], failure forfeit D and additional failed-send charge c. Type-blind success/failure channels beyond the disclosed value. | Paper exact source-outcome implementation if q_min D-(1-q_min)c>R for a public lower success bound. Includes q=1 and q approaching one; no failure floor. D is intrinsic if withholding is lawful, and funding/costs are explicit exclusions. [Complete consistent construction](admission-information-boundary.md#a-complete-one-late-disclosure-positive). |
| Serial late immutable openings across a whole program | Finite serial mandatory-opening source with correlated retained secrets; protected opaque binding choices. Each opening has one late Send/Never callback. Successful prefixes preserve source chance; first failure is publicly marked. Gross reward is bounded by R_i and total failure deductions by N_i D_i+K_i. | Reviewed paper exact forward SE preservation when D_i>R_i and D_i[1-N_i(1-q_min)]>R_i+(1-q_min)K_i. Constants precede the builder; no failure floor, and full off-path consistency is proved using actual entry priors. One physical callback and clean/dirty information separation are substantive restrictions. [Theorem and proof](serial-late-release.md#paper-preservation-theorem). |
| The same serial interface with reconstructible exact success odds | At the callback, the owner knows exact scalar odds q(p,v); after success every later strategic player recovers the recorded callback state p, late route and public v. The other menus, loss bounds and omissions remain those of the serial interface. | Reviewed paper preservation for all q in [0,1] if D_i>R_i and D_i²-(N_i+1)R_iD_i-R_iK_i>=0. Reliable callbacks copy Send; unreliable routes receive arbitrary rational completion and cannot profit at the protected root. No native public-odds adapter or common policy under unspecified laws. [Separate theorem](serial-late-release.md#a-second-interface-publicly-reconstructible-success-odds). |
| Late opaque binding with failure erasure | Protected or one late binding choice; value-independent opaque admission. Failed attempted values have a coherent common continuation preserving all menus, chance, observations and utilities; private own recall remains. Mandatory openings retain one late fixed-value opportunity. | Reviewed paper exact forward SE preservation under the serial success/loss bound. At failure the actual attempted-value draw is ancillary, so a quotient continuation equilibrium lifts with identical failure payoff for every value. Native transferable candidate evidence prevents assuming this adapter. [Complete proof](late-binding-erasure.md#paper-theorem). |
| Absorbing first-publication failure | Same serial protected/one-late binding and opening menus. First failure ends every further utility-relevant protocol action; settlement ignores a failed attempted value and deductions are at most D_i+K_i. | Reviewed paper exact preservation for any q_min>0 and D_i>[R_i+(1-q_min)K_i]/q_min, independent of phase count. A proposed stopping/settlement variation, with outside utility and recovery excluded; protected service and physical menus still need their own implementation. [Corollary and scope](late-binding-erasure.md#a-simple-absorbing-failure-variation). |
| Several delivery decisions for immutable openings | Serial mandatory-opening source; protected bindings and protected Open. Defer permits any finite owned Send/Wait/Retry control problem with private service learning. Operational dynamics ignore retained private types beyond the public source past and current opening. Failure ends play; the owner's failure utility is route independent and nonpositive, and successful delivery has no extra charges. | Reviewed paper exact SE and unconditional source law, with no late-success floor. A common operational policy is constructed consistently at every off-path control site; it can depend on the service law. An extra delivery-dominance property yields a common policy across a class. Native mode-dependent dead/duplicate packet accounting and other raw messages are excluded. [Theorem and accounting boundary](delivery-control-preservation.md). |
| The protected interface with delivery costs | Keep the preceding finite immutable-opening controls and fixed failure baseline. Nonnegative operational bills are settled at phase resolution, remain paid on success and abort, and have a public total funding cap; protected initialized transport is free. One fixed policy wins one-shot comparisons at every legal state for both endpoints of the source payoff range. | Paper exact SE and source law. With probability difference Delta q and cost difference Delta c, the endpoint tests are D_i Delta q>=Delta c and (D_i+R_i)Delta q>=Delta c. Pointwise tests give belief-uniform control; a common class policy is possible if the tests hold across the class. This is a conditional operational-cost criterion, not a proof for the actual global audit or arbitrary fee market. [Cost corollary](delivery-control-preservation.md#a-cost-variant-with-a-common-optimal-delivery-policy). |
| Source-independent physical abort | Fixed-stage finite source, original menus and conditional source chance; finite exogenous service and ancillary remembered receipts. Absorbing abort utility ignores source choices and later logical draws, though it may depend on immutable initial parameters. No added timing or submission actions. | Reviewed paper exact SE with exact delivered joint source law, and unconditional distinguishable-abort error 1-p. Conditional checkpoint bounds give p>=product(q_k), without independent checkpoints. This weaker outcome target is explicitly distinct from unconditional preservation; action/public-coin-dependent survival and strategic abort payoffs admit strict counterexamples. [Proof and boundaries](exogenous-abort-preservation.md). |
| Controlled delivery without protected sure inclusion | Fixed-stage source; choose each logical action once, then transport its canonical packet with arbitrary finite Send/Wait/Retry controls. All source actions share a value-blind mechanical service, including explicit carriers for lawful withholding. Every physical abort gives each player the same utility no greater than every source outcome, with actual funded settlement. | Reviewed paper exact SE and delivered joint source law. A service-specific policy selected before the source equilibrium maximizes whole-game completion and achieves at least any public fallback's reliability; conditional stage bounds give p>=product(q_k). Independent hidden service with a stated prior fits. Current silent FALSE, owner-specific audit charges, fees, full raw messages and permanent chain halt without settlement are excluded. [Global consistency and fallback guarantee](whole-game-delivery-preservation.md). |
| Persistent serial delivery jobs with monotone opportunities | Retain the preceding value-blind source, utility and observation interface. Jobs remain pending, copies are idempotent, opportunities are exogenous, and earlier readiness or submission never removes a later callback or inclusion opportunity. These properties hold from every legal state. | Reviewed paper common-policy corollary: first eligible submission and persistent rebroadcast supports the exact target SE and delivered source law for every service in this class, without its exact inclusion law. Completion dominates every fallback pathwise. Opportunity feedback, eviction, control-dependent priority and costs are excluded. [Policy and proof](whole-game-delivery-preservation.md#a-common-delivery-policy-under-persistent-monotone-opportunities). |
| Failure penalties depend on whose stage fails | Two mandatory stages; the first owner can deliver promptly or delay its own successful delivery so the second stage fails. Abort utility varies with the failing owner, even when every abort payoff is below the corresponding source payoff. Service ignores source data. | Complete reviewed paper negative: every target SE can have zero completion although a fallback has positive, potentially high completion. Large own-failure forfeits do not prevent shifting failure to another player. This is an explicit alternative settlement/service game, not a native embedding. [Two-stage games](whole-game-delivery-preservation.md#the-knowledge-and-realism-boundaries). |
| A late callback chooses a fresh binding value | Opaque x/y choice; one late callback; public protected/late route; private labels. Failure utility depends on the locally attempted value even if it was not admitted. | Complete paper nonpreservation at high inclusion reliability for a selected source SE. This wider full-history utility interface is not the native typed-readout game; failure rewards independent of the attempted value remove this example's preference mechanism. [Game and proof](admission-information-boundary.md#changing-the-binding-value-is-a-different-one-late-game). |

The local information necessity result in the compositional note is exact for
a forced observation refinement before one decision, over all bounded utility
functions: an informative refinement can destroy preservation of a selected
action law. It does not characterize multiplayer compilers or prove that every
sufficient clause in the positive theorem is independently necessary.

The late-action results explain why near-certain admission is not itself an
obstruction. In the fixed-value one-opportunity positive, successful replies
remain source replies and extra base gain is at most R times failure
probability. In the two-opportunity timing negative, rare-failure preferences
can sort types between opportunities and change successful replies by a fixed
amount. An inclusion estimate alone does not distinguish these cases.

A second negative weakens a different premise: let late delivery depend on a
hidden source bit unknown to the sender, even though the opening and every
failure payoff are value independent. Successful delivery then selects that
bit, forcing a receiver response that makes deferral profitable for every
fixed finite forfeit at sufficiently high reliability. This is a complete
paper SE negative for correlated source/service state, not a native public
scheduler embedding. [Game and exact boundary](late-binding-erasure.md#why-value-independent-failure-utility-alone-is-insufficient).
The same fixture has a preserving weak PBE when Bayes' rule is required only
at information sets reached with positive probability. Its late reply uses a
fair off-path belief that no SE tremble sequence permits. Stronger PBE
definitions and general native PBE preservation are not established by this
contrast.

## A checked boundary for the asynchronous comparison

The settle-late game has a machine-checked uniform-order impossibility. Fix
a positive reward scale, a forfeit above that scale and a capped audit charge
above half that scale. For each pending-observation probability strictly
between zero and one, every sufficiently high late-inclusion probability below one
admits no target SE with the intended outcome law. The game includes blind
retries, raw signals, a listener packet and visible inclusion serials. This is
a checked abstract game; its native embedding is not yet machine checked.
It does not cover audit charges at or below half the reward scale, nor does it
refute choosing collateral after fixing a known service.
[Exact quantifiers and the remaining positive direction](quantifier-orders.md).

The [native two-late proof](native-late-action-analysis.md) separately constructs
the source setup, full bounded raw menu, public scheduler and actual settlement
at paper level. Its stronger deposit bounds control all extra native packets;
its likelihood proof allows arbitrary type-dependent deferral trembles. This
settles the mathematical native obstruction for that explicit configuration,
while leaving the owner's checked proof obligations unchanged.

Exact knowledge of the selected service is a separate issue. The current
fixed-scheduler model evaluates a specified chance process. A new paper
extension of the negative comparison allows a hidden independently drawn
inclusion rate, with any finite common prior above the bad threshold, provided
no pre-inclusion observation reveals that rate. The positive public-bound
comparison and the restricted public-delay proof also have hidden-service
versions. None of these adopts a miner model; the common-policy and Bayesian
preservation questions remain distinct.
[Player knowledge, miner assumptions and proofs](miner-assumptions.md).

## Positive statements with their scopes

**Collateral for the known settle-late builder.** Keep the finite comparison's
signals, blind retry, listener packet and partial pending observation. Fix
its sole-opening inclusion probability q<1 before choosing collateral. Equal
forfeit and capped audit amounts D=c=K with K>R/(1-q) force the intended law in
every target SE and weak PBE. Any deferred continuation risks at least one of
the two deductions with probability 1-q; sufficiently large K makes its value
negative, while protected opening and silence have nonnegative value. This is
a complete paper proof for the same abstract game as the checked uniform-order
negative, not a native-runtime theorem. Both deductions need funding, and costs
of that capital are outside the game's utility.
[Proof, sharper bound and quantifier distinction](quantifier-orders.md#a-positive-paper-argument-for-the-same-fixed-q-comparison).

**Exact public dispatch.** For a finite perfect-recall game retaining private information,
suppose players retain exactly their source menus and observations. Insert
bounded public random waiting whose law depends only on the recoverable
source-public past. Give the service mandatory padded dispatch and no extra
player timing choices or utility costs. Every source SE then has an exact
preserving target SE. The proof derives history likelihoods from the scheduling
kernels, constructs one global consistency sequence and proves continuation
optimality. It allows correlated private state across phases.
[Proof and interface](information-and-release.md#paper-theorem-source-preserving-dispatch-and-public-random-delay).

**Finite first-departure enforcement.** Suppose that exact retained game is
structurally embedded in a larger finite game without changing retained
observations or transitions. All retained histories are audit-clean; their
utilities have lower bounds. Target base utilities have upper bounds. Every first
excluded action has an actual collection probability bounded below, regardless
of later behavior. The existing finite consistent-completion theorem then
provides a deposit chosen before the equilibrium and an extension for each
retained SE. This is a conditional mathematical route to full preservation,
not evidence that the current audit charges every useful timing deviation.
[Conditions and enforcement](service-and-enforcement.md).

Its computed deposit must also fit the declared capital budget. A small
collection probability can make the finite bound economically unusable;
finiteness alone establishes no affordability or willingness to participate.

**Incremental early-disclosure charges in a complete small game.** A sender
knows a fair committed bit, and a receiver guesses before the lawful final
opening. Both receive one for a correct guess; final withholding costs the
sender more than one. Add an early authentic proof that has no contract effect
but reaches the receiver. If every such early disclosure costs a certainly
collected additional amount at least one, every source SE is implementable.
A charge strictly above one also forces every target SE to have a source law.
The bound is fixed before selecting the source guessing strategy. A private
uncharged copy or an already spent charge invalidates it.
[Proof and sharper selected-policy threshold](information-and-release.md#paper-contrast-an-incremental-disclosure-charge-repairs-this-game).

**Approximate sequential preservation with costs.** Keep one finite full tree,
action menus, observations and perfect recall. Perturb chance kernels uniformly
at all source-compatible histories, including deviations, and terminal utilities
uniformly over all outcomes. New chance branches may become possible. Every
selected source SE has target assessments with exactly consistent beliefs,
vanishing whole-continuation regret, converging logical laws and controlled
utility error. A slowly selected source tremble sequence handles rare decisions;
newly reachable decisions receive a rational completion.
[Proof and bounds](preservation-and-robustness.md#primitive-uniform-guarantees-and-approximate-se).

**Exact stability under strict pure incentives.** Keep the same finite game,
information and positive chance support. Suppose a pure source SE has a strict
conditional margin at every decision, including off-path decisions. Small
chance and utility perturbations then admit a target SE using that same pure
policy. Its consistent target beliefs need not equal the old beliefs, and
its initialized law generally has a small error.
[Proof and quantitative condition](preservation-and-robustness.md#strict-pure-se-with-retained-private-information).

**Approximate reflection of all exact equilibria.** Keep one finite perfect-recall
tree, the same players, node ownership, action menus and information sets, and
the same positive chance support. With chance and utility errors tending
to zero, every target SE approaches the set of source SE assessments. Logical
outcome laws approach the source equilibrium-law set uniformly. This does not
make every selected source SE approachable by exact target SEs.
[Proof and uniform corollary](preservation-and-robustness.md#an-asymptotic-reflection-theorem-with-fixed-chance-support).

## Negative statements and what they actually exclude

| Claim that fails | Complete comparison and conclusion | Scope |
| --- | --- | --- |
| Contract rejection preserves secrecy | A sender knows a fair committed bit. A receiver guesses before final opening. Both benefit from a correct guess. A free authentic early proof changes no contract state but lets every target SE achieve correctness one, versus source correctness one half. | No target SE or weak PBE preserves the selected source law in this finite game. Not a native-runtime embedding. |
| Any informative metadata is harmless | A compulsory free signal changes a receiver's posterior about a hidden event. Pick a safe payoff between its prior probability and a higher posterior. The source always chooses Safe; every target SE guesses on some signal outcomes. | An informative observable can break universality over bounded utility functions. It need not affect every fixed game. |
| Any positive publication fee fixes early disclosure | In the fair-bit game, an early fee below one half still gives every target SE correctness above one half. | Game-specific quantitative obstruction. An independently collectible charge can repair it. |
| A huge already-spent escrow deters future actions | A later useful action causes zero additional collection after an unavoidable fixed charge. Its conditional net gain stays positive at every escrow size. | Local comparison, or the service track's specified comparison game. Not a counterexample merely because a deterred dirty branch contains it. |
| Successful own publication guarantees safe concurrency | A resource-heavy valid opening succeeds for its owner but makes another owner's publication miss its deadline. The first owner benefits from that failure and chooses the heavy action in every target SE. | A fully public finite capacity comparison. Own-failure forfeits cannot punish another player's failure; no actual-runtime embedding is asserted. |
| Tiny costs preserve each exact source equilibrium | One player has two tied source actions. An arbitrarily small fee on one makes only the other optimal, at logical-law distance one from the selected costly-action source equilibrium. | Exact selected-equilibrium preservation fails; approximate regret can still be tiny. |
| Honest initialized fidelity is enough for SE | A sender's source In action keeps its type hidden and is deterred by rational rejection. A target In action discloses the favorable type, making entry profitable. Honest Out transcripts agree. | No preserving weak PBE or SE, despite a preserving Nash profile with an incredible threat. |
| Forward preservation excludes extra equilibria | Two players coordinate without seeing each other's action. An added public coin lets them coordinate perfectly on its value; all source equilibria remain implementable, but this correlated law is new. | Forward preservation does not imply reflection, even for source-independent public randomness. |
| Small monetary errors imply small payoff-law TV | A common deterministic fee moves payoff zero to a nearby negative value. Logical law is unchanged, payoff error is tiny, but payoff-law TV is one. | Choice of metric, even in a game with no strategic decisions. |
| Eventual delivery implies exact publication by a fixed deadline | A finite physical execution has positive probability of no service. Its terminal readout can remain unfinished, while the selected source terminal law is complete. | Exact law equality fails even without incentives. No claim that every chain has the specified outage probability. |

Disclosure results are proved in the [information track](information-and-release.md).
Costs, conditional incentives and equilibrium-direction distinctions are proved
in the [robustness track](preservation-and-robustness.md). Collection and timing
conditions are examined in the [service track](service-and-enforcement.md).

## A concrete next theorem to pursue

The [reviewed protected restriction](native-protected-execution.md) and
[full native negative](native-late-action-analysis.md) locate the current
mathematical boundary. Further work should test which concrete public service
or settlement properties exclude the two-late mechanism, and whether the same
native fixture has a preserving weak PBE. Neither question calls for another
general equilibrium-existence framework. A proposed runtime change must be
identified as a separate interface before making a positive claim about it.

The most useful combined target is a **finite source-compatible dispatch
interface with an explicit extension to additional submissions**:

1. Faithful messages and public timing are derived from source-public history
   and preserve source-private observations, even while old secrets persist.
2. Required publication has a declared service guarantee; ordinary service
   failure is either absent, source-visible, or quantified as approximation.
3. Every extra action either simulates a lawful source continuation or has a
   physically evidenced, sufficiently collectible first-departure charge.
4. All relevant costs enter a bounded utility comparison.
5. One consistency construction and continuation proof cover the combined
   game, including dirty histories, rather than only separate components.

This is an operational research target. It does not assume the desired beliefs
or equilibria as backend properties. Its difficult questions are whether useful
physical interfaces establish the information and attribution clauses, and
which clauses can be weakened without losing the declared preservation target.

Plaintext windows and selective encrypted admission are two candidate routes
to investigate. Neither is promoted to a universal answer. The next handoffs
and independent tasks are recorded in the [workflow](workflow.md).
