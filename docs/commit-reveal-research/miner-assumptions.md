# Miner behavior and what players know

The primary research target chooses compiler parameters and collateral before
selecting a builder. The builder must satisfy a publicly stated service
specification. Calculating collateral for a fully known builder is a contrast,
not the intended deployment assumption. No candidate below replaces the
project's adopted runtime or specifies a miner protocol for it.

## Universal service guarantees and player knowledge differ

A universal theorem tests every service allowed by its assumptions. Selecting
a counterexample after seeing the collateral is a mathematical quantifier;
it does not mean that a miner chooses a hostile algorithm during play or
colludes with a player. A benign fixed configuration can defeat a universal
claim. However, the counterexample still has to obey the declared miner and
network assumptions. An arbitrary scheduler allowed by a broad interface is
not automatically an implementation of independent honest miners.

The current runtime fixes a scheduler as a chance kernel of the environment's
public history and view. It is not a strategic miner with a utility function,
nor an explicitly hidden choice between scheduler kernels. Players do not
observe future random commands; the equilibrium calculation nevertheless uses
the game's specified chance probabilities.
[Current service contract](../../Vegas/Pending/ReactiveAsyncContract.lean).

Let B be a public specification and let S(B) be the class of allowed services.
Collateral C(B) can depend on that specification and the program, but not on
the selected service or source equilibrium. Three different claims remain:

| Claim | What players may rely on | Required conclusion |
| --- | --- | --- |
| Pointwise preservation | The chosen game's transition probabilities, with random realizations unobserved. | For every service in S(B) and every source SE, some preserving target SE exists. Its strategy and beliefs can depend on the service. |
| One policy for the public specification | Only the advertised properties and the observed execution. | For each source SE, one observation-based policy supports preservation in every allowed service, with service-specific consistent beliefs. |
| Bayesian service uncertainty | A specified common prior over persistent hidden service types, followed by learning from observations. | Preservation in the single game containing that hidden type; no requirement that its policy be an equilibrium conditional on each unobserved type. |

A single assessment for all services is stronger than one policy and usually
unnecessary: observing a receipt can change beliefs differently under different
service laws. Conversely, a pointwise existence theorem does not give players
who know only bounds an implementable common policy.

Bounds alone do not determine Bayesian expected utility. One must either state
a prior, quantify over a family of priors, or explicitly require comparisons
valid for every compatible conditional law. Independently redrawing an unknown
service every round discards the learning and correlation caused by a
persistent hidden service; that is a different game.

## What standard blockchain assumptions supply

There is no single standard implication from “non-colluding miners” to a
transaction-ordering or inclusion distribution. The following layers should
be stated separately.

**Protocol honesty and bounded faults.** Honest participants follow the
specified consensus algorithm; an explicit fraction of hash power or stake
may deviate. The Bitcoin-backbone analysis combines bounded adversarial hash
power with synchronization assumptions to establish ledger persistence and
liveness. Those are security assumptions, not a derivation that every
economically motivated miner follows the protocol.
[Original analysis](https://iacr.org/archive/eurocrypt2015/90560288/90560288.pdf).

**Network timing and availability.** A synchronous model supplies delivery
bounds. In partial synchrony such bounds may be unknown, or start holding
only after an unknown stabilization time. Consequently partial synchrony
alone does not provide an unconditional deadline from the start of a game;
that deadline observation is our inference from the model.
[Dwork, Lynch and Stockmeyer](https://groups.csail.mit.edu/tds/papers/Lynch/MIT-LCS-TM-270.pdf).

**Voting availability and finality.** PoS analyses such as Gasper separately
assume sufficient honest stake and synchronization for progress, and analyze
probabilistic liveness. Finality and inclusion service are distinct proof
obligations. A block's confirmation does not specify which pending game calls
its producer chooses to put in that block.
[Gasper analysis](https://eips.ethereum.org/assets/eip-2982/arxiv-2003.03052-Combining-GHOST-and-Casper.pdf).

**Transaction selection and economic behavior.** A producer can choose which
transactions to include and how to order them; fees and extractable value can
affect those choices. Independent profit seeking therefore need not produce
random ordering, payload independence or equal inclusion probabilities.
[Ethereum's MEV documentation](https://ethereum.org/developers/docs/mev/).

For this project, non-collusion could mean no private agreements with game
players, no access to their secrets except through allowed messages, and no
private payment channel. It does not exclude public priority fees, knowledge
of publicly visible openings, shared congestion, or a producer's own financial
interest. This proposed definition must be distinguished from the stronger
assumption that producers have no utility depending on the game outcome.

An economic candidate could specify independent producers maximizing declared
block revenue under validity and capacity constraints, with no utility term
for a particular player's win. Its tie-breaking freedom and observation rules
must be explicit. That is a candidate miner model, not a consequence of merely
being non-colluding or a claim that consensus enforces this optimization rule.

## A public collection bound removes the need to know an exact rate

Here is a paper example in the mandatory-opening finite comparison from
[Collateral and service quantifiers](quantifier-orders.md). Nature draws a
finite hidden builder type independently of the sender's bit and label. Its
sole-opening inclusion probability is q_theta; players need not observe it.
The public specification states q_theta<=1-delta for one delta>0. The other
menus, protected inclusion, exposure law and monetary deductions remain those
of that comparison. There is no extra signal about the sender's label on the
protected path.

Choose D=c=K>R/delta before selecting the builder type. After protected deferral,
signals and duplicate openings trigger a charge, no opening triggers forfeiture,
and a sole opening fails with probability at least delta. The conditional risk
bound holds under every posterior over builder types and every later policy.
Thus a deferred policy pays at most R-K delta<0. A protected opening followed
by silence pays at least zero, and an extra post-protected signal pays at most
R-K<0. Every SE therefore follows the intended protected path, where Bayes'
rule leaves the private label uniform and the listener chooses Safe.

The finite Bayesian game has perfect recall and hence an SE. The same law
conclusion holds for weak PBE. This direct paper proof is uniform over all
finite common priors supported by the public bound; it needs no exact rate.
It is not a new checked or native-runtime theorem. Both deductions must be
funded, and capital costs are absent from this utility model.

The crucial limitation is that a lower bound on late-failure risk is an
additional service property, not a standard consequence of honest miners.
Ordinary liveness points toward successful inclusion; it supplies no such
upper bound on the best late success probability. General enforcement can
instead use a uniform gain-to-collection ratio, but still needs actual evidence
and collection under all allowed later actions.

## Unknown public waiting can also preserve source incentives

There is a cleaner exact positive for the restricted public-dispatch interface.
Each hidden scheduler type is independent of source secrets and draws bounded
public waiting tokens using only recoverable source-public history and earlier
public tokens. Required source actions, observations and utilities are unchanged;
players have no additional timing or submission choices.

For a source tremble's history weight w(h) and a public wait transcript tau,
the Bayesian target's marginal reach weight is

\[
w(h)\sum_\theta\pi(\theta)L_\theta(h,\tau).
\]

At a copied source decision, the summed likelihood factor is identical across
its compatible hidden histories, so it cancels in Bayes' rule. Erasing waiting
also preserves continuation utility. The lifted source strategy can ignore
the waiting tokens even when players learn about the scheduler type from them.
The usual common consistency sequence therefore proves exact SE preservation
for every finite independent prior over these scheduler types.

This is a paper extension of the
[public dispatch proof](information-and-release.md#paper-theorem-source-preserving-dispatch-and-public-random-delay).
It allows retained private state, but its closed action interface excludes
uncertain admission, extra packets, action-dependent fees and discounting.
An audited raw-runtime extension still needs a common-information and
completion argument; its new-site policies may depend on the prior.

## The negative comparison also survives a hidden inclusion rate

The checked fixed-rate negative does not by itself prove a negative for a
Bayesian hidden service. There is, however, a separate paper extension for the
same mandatory-opening finite game.

Fix R>0, D>R, c>R/2 and the exposure probability lambda in (0,1). Let t be
the checked inclusion threshold in [the quantifier analysis](quantifier-orders.md#what-the-checked-theorem-says).
Nature independently draws a hidden Q from any finite common prior supported
strictly inside (t,1). Q affects only the final inclusion lottery. It affects
no earlier observations, menus, fees or signals, and is not revealed before
the sender's last decision. Exposure and listener packet cost stay fixed.

**Proposition, paper proof.** This Bayesian implementation game has no SE
with the intended outcome law. Exact knowledge of realized Q is unnecessary.
The conclusion holds for every such finite common prior, but it is not a
definition of SE without probabilities or a new checked theorem.

Let

\[
\bar q=\mathbb E Q,\qquad
\bar r=\mathbb E[Q/(1+Q)].
\]

The marginal chance process gives a sole opening probability bar q and each
duplicate opening probability bar r, with neither included probability
1-2 bar r. In general bar r is not bar q/(1+bar q); directly applying the
checked fixed-q theorem at the mean would therefore be invalid. Nevertheless
0<bar r<1/2, so the duplicate lottery has the same positive support.

The generalized proof has four steps:

1. Under every fully mixed player profile, each pre-inclusion history has
   likelihood independent of Q. Its posterior remains the prior. Taking one
   SE consistency limit preserves this fact even at off-path information sets.
   Thus sender conditional expectations use bar q. Sequential rationality
   alone would not justify this posterior assertion.
2. The strict comparisons eliminating raw signals, duplicate openings and
   permanent withholding depend on a sole opening's success probability and
   the pathwise charge for extra packets. Their parameter inequalities are
   affine in q and hold at bar q>t. A duplicate always creates a dropped
   packet, regardless of the value of bar r.
3. The consistency argument comparing type weights at the listener's two
   successful-observation information sets still applies. Duplicate-lottery
   coefficients appear only multiplied by duplicate-action probabilities
   tending to zero. The decisive products tend to bar q squared and zero,
   respectively. The same label exclusion and rational guessing follow.
4. Once these extra actions are excluded, opposite timing preferences and
   the profitable protected deferral calculation involve only bar q. The
   checked inequalities at bar q then contradict a preserving SE.

This is a paper generalization of the explicit weighting and payoff proofs in
[SettleLateConsistency](../../Vegas/Examples/LateLeak/SettleLateConsistency.lean),
[SettleLateTurns](../../Vegas/Examples/LateLeak/SettleLateTurns.lean) and
[SettleLatePreservation](../../Vegas/Examples/LateLeak/SettleLatePreservation.lean).
The altered retry law and hidden-type adapters have not been checked in Lean.
Two independent mathematical reviews inspected these dependencies.

The common prior is specified in each Bayesian game. Quantifying over all
priors with the stated support gives a uniform negative without fixing an
exact realized rate; it does not supply an ambiguity-based equilibrium notion.
The proof establishes an SE negative, not a weak-PBE negative: unrestricted
off-path beliefs about Q need not remain at the prior.

This proof does not cover learning about Q before sending, Q-dependent
exposure, service correlated with source-private labels, or strategic miners.
Those change the game and need analysis. It also supplies no honest-miner
implementation or complete native packet embedding. The service is exogenous
and independent of source secrets in this comparison, but that fact alone
does not certify a standard miner selection algorithm.

## The native questions to keep separate

1. Does the checked negative comparison arise under a declared honest-miner,
   network, transaction-selection and player-observation model?
2. Does a public service specification give collection and information bounds
   strong enough for one policy, rather than merely separate equilibria for
   fully specified schedulers?
3. If service types are hidden, which common priors and observations are part
   of the game, and what learning occurs before later decisions?
4. Do the guarantees cover bids, replacements, retries and shared capacity, as
   well as prescribed calls? Which fees and financing costs enter utility?

The constants-before-builder requirement is common to these questions. The
remaining choice is the declared service class and the player's uncertainty
model, not permission to choose collateral after inspecting the selected miner.
