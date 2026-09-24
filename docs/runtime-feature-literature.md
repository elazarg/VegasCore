# Literature for restoring isolated runtime capabilities

This note supports the [runtime feature investigation](runtime-feature-restrictions.md).
The comparison fixes a native game, restricts one capability, and then restores
it. Its objectives are preservation conditions, explicit counterexamples, and
requirements inherited by further abstractions. None of the external results
below is a proved adapter for the Vegas native protocol.

## Verifiable disclosure: a close existing characterization

Scott Saas, *Disclosure-Proof Correlated Equilibria*, working paper, June 2025,
studies a finite complete-information base game with exogenous private signals.
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
missing no-leak native equilibrium.

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

## Concrete proof obligations and opportunities

### The no-leak native fixture

Generic finite-game SE existence does not establish Alice's required payout of
zero. The restricted fixture still has arbitrary legal responses, rejected
public packets, malformed candidates, withholding, and deadlines. An assessment
that ignores all unexpected information is not justified. The proof must cover
off-path sites and one common consistency sequence, using the existing service
and opening lemmas wherever their premises are independent of passive leakage.

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
the cited literature. The first completed feature comparison should precede a
general interface for describing them.
