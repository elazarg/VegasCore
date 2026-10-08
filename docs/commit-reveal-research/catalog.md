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

## A checked boundary for the asynchronous comparison

The settle-late game has a machine-checked uniform-order impossibility. Fix
a positive reward scale, a forfeit above that scale and a capped audit charge
above half that scale. For each pending-observation probability strictly
between zero and one, every sufficiently high late-inclusion probability below one
admits no target SE with the intended outcome law. The game includes blind
retries, raw signals, a listener packet and visible inclusion serials. This is
a checked abstract game, not yet an embedding into the full compiled runtime.
It does not cover audit charges at or below half the reward scale, nor does it
refute choosing collateral after fixing a known service.
[Exact quantifiers and the remaining positive direction](quantifier-orders.md).

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
