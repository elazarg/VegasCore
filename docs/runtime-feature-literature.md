# Literature for restoring isolated runtime capabilities

This note supports the [runtime feature investigation](runtime-feature-restrictions.md).
The comparison fixes a native game, restricts one capability, and then restores
it. Its objectives are preservation conditions, explicit counterexamples, and
requirements inherited by further abstractions. None of the external results
below is a proved adapter for the Vegas native protocol. The first native
comparison is now checked directly: restoring passive observation prevents
matching a restricted equilibrium's declared payout law in the fixed bounded
selective-association game, with all raw responses retained.

## Verifiable disclosure: a close existing characterization

Scott Saas, *Disclosure-Proof Correlated Equilibria*, Games and Economic Behavior
159 (2026), 546--563,
[published article](https://doi.org/10.1016/j.geb.2026.08.001), studies a finite
complete-information base game with exogenous private signals. The theorem
numbers below refer to the accessible June 13, 2025 manuscript.
Players may publicly disclose their exact signal before simultaneously playing
the base game. Lemma 1 characterizes a no-disclosure sequential equilibrium for
a **fixed** signal structure: its decision rules must induce the desired outcome,
be Bayesian equilibria after every possible disclosure, and give each type no
profitable unilateral disclosure. Theorem 1 permits redesigning the signal
structure and characterizes attainable no-disclosure outcomes by obedience and
interim participation constraints. The participation threshold is the worst
correlated-equilibrium payoff with the discloser's action independent of the
others; for two players it is the worst Nash payoff. Proposition 4 and Section 5
give positive cases for two-player binary-action and zero-sum games, respectively.
Section 5 also gives a three-player example where private selective disclosure
destroys a direct-recommendation implementation that survives public disclosure;
another information structure restores that outcome.
[Primary paper](https://eller.arizona.edu/sites/default/files/2025-10/Disclosure_Proof_Correlated_Equilibria-8.pdf)

**Application to our investigation.** This suggests a useful property of a
restricted game: its intended equilibrium admits rational disclosure
continuations that deter every allowed disclosure. It supplies a more concrete
research target than requiring all extra information to be irrelevant. The
native adapter must identify the feasible evidence, recipients, association
events, response opportunities, and conditional continuation payoffs. Our
selective disclosures and endogenous candidate choices are outside the cited
model. Neither its positive game classes nor its freedom to redesign signals
can be transferred to our fixed service without proof.

## Passive observation must really be observational

Makris and Renou, *Information design in multistage games*, Theoretical Economics
18 (2023), fix a dynamic base game and expand it with additional private signals.
Their expansion kernels leave the base transition kernel unchanged conditional
on base history and actions; extra signals depend only on already realized
events. Theorems 1, 3, and 4 characterize unions of outcome sets over expansions
for BNE, weak PBE, and conditional-probability PBE. The last concept is explicitly
weaker than Kreps--Wilson SE; their conclusion leaves SE extensions open.
[Published paper, Sections 3--6](https://www.econstor.eu/bitstream/10419/296445/1/1876215240.pdf)

**Application.** A no-leak/leak comparison should preserve the same conditional
inclusion and application transitions after fixing transmissions. The scheduler
must not receive a record of private observations. Players' later actions may
still depend on what they observed. This separates an information feature from
a scheduler feature. The cited characterization does not show that every
equilibrium survives any particular expansion, and gives no shortcut to the
specific equilibrium and consistency obligations discharged by our native proof.

## Trace patterns need information alternatives and timing assumptions

Moses, *Relating Knowledge and Coordinated Action: The Knowledge of Preconditions
Principle* (2016), Theorem 3.1, proves that if a condition is necessary for an
action whose occurrence the actor knows, knowing that condition is also
necessary. It derives nested-knowledge requirements for ordered actions and
common-knowledge requirements for simultaneous actions. The paper's examples
also explain how known delivery bounds and clocks permit learning from silence.
[Primary paper](https://arxiv.org/pdf/1606.07525)

**Application.** A pattern such as `certificate -> association -> response`
must include a statement about which compatible histories remain possible at
the response. Its temporal arrows cannot automatically be replaced by message
chains: a service deadline can provide information without a new delivery.
The knowledge theorem concerns necessary conditions for correct action, not
equilibrium optimality. Our continuation-decision lemmas supply the separate
incentive step. Probabilistic optimal action may require only a posterior
threshold, rather than certain knowledge.

Clarkson and Schneider, *Hyperproperties* (2010), distinguish properties of one
trace from properties of sets of traces; confidentiality generally belongs to
the latter category. [Primary paper](https://www.cs.cornell.edu/fbs/publications/Hyperproperties.JCS.pdf)

**Application.** Use existing native histories and observations first. A
secrecy witness compares executions with different secrets and indistinguishable
recipient observations. A quantitative guessing bound additionally needs their
probabilities; equal supports alone are insufficient. An equilibrium obstruction
also needs feasible deviations and payoff comparisons. A new trace logic is
unnecessary for the first experiment.

## Strategy zeros and restrictions on the game

Kreps--Wilson consistency requires a limit of fully mixed strategy profiles
and their Bayes beliefs. The limiting profile may assign zero probability to
available actions. Reny, *A simple proof of the sufficiency of Dilmé's
power-sequence test for Kreps-Wilson consistency*, International Journal of
Game Theory 55, article 29 (2026), restates this definition and fixes Nature's
probabilities throughout every approximating sequence. Its Theorem 2.3 gives
the power-sequence characterization; Remark 2.5 supplies a bound on the
required integer exponents from the finite game tree.
[Primary article, Sections 1--2](https://doi.org/10.1007/s00182-026-00997-z)

**Application.** The native empty-observation experiment changes a fixed chance
kernel. Restricting legal player responses instead changes available deviations
and legal histories. Neither operation is equivalent to assigning a legal
player action probability zero. The checked distinction and the additional
obligations for restoring actions are described in
[the restriction analysis](runtime-feature-restrictions.md#model-restrictions-and-zero-probability-play).
The native posterior proof instead uses the existing common uniform-tremble
sequence, a concrete injection between response tuples, and finite limit
comparison. It does not rely on a power-sequence adapter. Applying the cited
finite exponent bound to other protocol examples still needs a verified
adapter to that theorem's game-tree presentation.

## Concrete proof obligations and opportunities

### Checked no-leak equilibrium and restored-observation separation

The [native SE construction](../VegasTests/SelectiveAssociationRestrictedEquilibrium.lean)
proves the required zero payout for Alice in the game with empty passive
observation. It covers the complete bounded raw menu, including rejected
packets, malformed candidates, replays, withholding and deadlines. The
[prefix injection](../VegasTests/SelectiveAssociationRestrictedPrefixInjection.lean)
flips a privately fixed true candidate into a false one while preserving the
guesser's whole input. The
[probability comparison](../VegasTests/SelectiveAssociationRestrictedPrefixPosterior.lean)
and [common consistency limit](../VegasTests/SelectiveAssociationRestrictedBeliefs.lean)
justify the required beliefs at off-path sites as well as on the prescribed path.

The [separation capstone](../VegasTests/SelectiveAssociationRestrictedSeparation.lean)
compares the actual native payout evaluator under the two observation rules.
Every sequentially rational assessment with the original passive observation
gives Alice at least one half, so none can match the restricted SE's payout law.
Utilities are the program's fixed declared payouts. The exclusion permits
arbitrary target strategies and beliefs, including payoff-dependent choices.
This is one isolated feature counterexample, not a positive preservation
theorem or an impossibility for every game admitting communication.

### Positive patterns to investigate

- **Information arrives after its recipient's last possible influence.** Later
  relay transmissions count as influence. This should be a clean first positive
  comparison, provided private observation does not affect the service and the
  retained outcome ignores the observation record. A native SE theorem remains
  to be proved.
- **Disclosure is feasible but not profitable.** Prove rational continuation
  responses and a no-gain inequality for the discloser at each relevant site.
  This can permit payoff-relevant information, unlike an information-erasure
  criterion. Consistency across all such continuations remains an obligation.
- **Added observations contain only locally reproducible randomness.** A
  promising sufficient certificate is that each player's extra observation can
  be simulated from its old observations and independent randomness, including
  along deviations. The consistency construction must be proved; marginal
  independence of a signal from a secret alone is insufficient.

These are proposed native proof targets, not consequences already obtained from
the cited literature. The completed negative comparison identifies one game
outside any class that safely erases the feature. A positive characterization
of such classes remains open; it should precede a general interface for
describing preservation certificates.
