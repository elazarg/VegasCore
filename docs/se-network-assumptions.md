# Network assumptions for sequential-equilibrium preservation

The correlated-service delivery lemmas and counterexamples here are paper
arguments. The concurrent theorem is checked under the reserved-epoch service as
`Vegas.Paper.concurrent_source_raw_sequential_equilibrium`; the
[proof note](se-concurrent-mechanization.md) describes its proof. The other network models
below have no checked equilibrium construction.

The question is which assumptions let concurrent commit/reveal implement each
selected source sequential equilibrium with its original joint outcome and net
payoff law. The [general assumptions note](se-preservation-assumptions.md)
records the target and the existing conditional one-block comparison. This
note examines uncertain, correlated delivery and common literature assumptions.

## The main distinction

Actual independence of transaction delays is stronger than the delivery
comparison needs. A useful alternative is:

> Under the same underlying network conditions, submitting the same packet
> earlier cannot postpone its arrival or reduce its admission opportunities.

This allows exogenous shared congestion compatible with that monotonicity,
correlated delays, and learning about network conditions. It is a
counterfactual comparison across two submission policies,
not merely FIFO ordering of packets that were both sent in one execution.
Whether a chain backend satisfies it must be justified. It is a delivery
property, not yet a preservation theorem.

Players can also be uncertain about the dependencies themselves. The standard
Bayesian formulation uses a common prior over hidden network parameters and
updates it from observations. This is an application of
[Harsanyi's model of incomplete information](https://pubsonline.informs.org/doi/abs/10.1287/mnsc.14.3.159),
not a requirement that players know the realized congestion or delay schedule.
Such uncertainty can remove a particular predictor under a specified prior.
It can also make waiting valuable: another receipt may reveal which network
regime is active. Ignorance alone supplies no incentive inequality.

## Common assumptions and what they contribute

The theorem descriptions below come from primary sources. Their implications
for VegasCore are our assessment; none of these citations closes the compiler's
preservation obligation.

| Assumption | Literature/model | Contribution and limitation here |
| --- | --- | --- |
| Known bounded message delay, adversarial within the bound | [Pass, Seeman, shelat](https://eprint.iacr.org/2016/454) analyze blockchain consistency and liveness in this model. | Supports a bounded network-service abstraction. Does not provide iid delay, transaction admission by a cutoff, or conditional earlier-send dominance. |
| Unknown delay bound or eventual stabilization | [Dwork, Lynch, Stockmeyer](https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf) distinguish two partial-synchrony models. | Useful for eventual progress. An unknown safe bound or unknown stabilization time cannot directly justify a known zero-failure deadline. |
| Honest-majority resources and unpredictable leadership | [Ouroboros Praos](https://eprint.iacr.org/2017/573) combines honest-majority stake, cryptography, and an unknown bound on adversarially chosen delays. | Relevant security assumptions, rather than independent transaction delays. High-probability consensus guarantees require an explicit bridge to our exact on-path law. |
| Fair eventual delivery and activation | [Geffner and Halpern](https://arxiv.org/html/2309.14618v2), Theorem 2, obtain asynchronous mediated SE implementation for n > 4k. | Genuine positive precedent with authenticated private communication and a content-blind adaptive scheduler. Different source/task, participant, duration, and nontermination assumptions; no finite-deadline expel/restart theorem. |
| Oblivious scheduling | [Aspnes](https://www.cs.yale.edu/homes/aspnes/papers/podc2012consensus-journal.pdf) fixes process scheduling independently of process coin flips. | Restricts scheduler adaptation. Does not imply iid latency or prevent information in players' chosen send times. The exact meaning of oblivious must be stated. |
| Transaction order fairness | [Aequitas](https://eprint.iacr.org/2020/269) adds fairness to consistency and liveness. | Constrains ordering manipulation. Does not hide participation or guarantee that waiting cannot improve a first packet's qualification. |
| Ideal ledger, synchronization, and funded penalties | [Kiayias, Zhou, Zikas](https://eprint.iacr.org/2015/574) construct robust computation with compensation using these interfaces. | Good precedent for making availability and collectible liability explicit. Compensated security is not SE, and compensation is not the current expel/restart payoff law. |
| Common prior over an unknown service regime | [Harsanyi](https://pubsonline.informs.org/doi/abs/10.1287/mnsc.14.3.159) models hidden parameters by Nature and partial signals. | Admits correlated, unknown dependencies within ordinary Bayesian modeling. The actual posterior, including off-path observations, must satisfy the needed comparisons. |
| Computational information hiding and bounded deviations | [Halpern, Pass, Seeman](https://arxiv.org/html/1506.03030), Theorem 4.6, preserve computational SE under a suitable representation. | A useful deviation-simulation and belief-construction architecture. Computational or approximate preservation would be a different guarantee from exact unrestricted SE. |

Bounded propagation, block production, transaction inclusion, stable finality,
and equilibrium preservation are separate obligations. In particular, a
consensus-honest proposer need not include every valid game transaction unless
the specified ledger/admission policy requires it. The
[Bitcoin backbone](https://eprint.iacr.org/2014/765) makes transaction-ledger
liveness and persistence explicit, rather than identifying them with message
delivery alone.

The exact asynchronous SE result above has further scope qualifications:
its main finite-message regime uses rational action-profile probabilities,
with extensions discussed separately, and its underlying games are Bayesian
or normal-form. Its scheduler can adapt to traffic identities and order while
remaining unable to inspect contents. Content blindness and obliviousness are
different restrictions.

## A proved delivery comparison with correlated delays

Fix a packet, its deadline C, and one latent network experiment omega. Let
A(s,omega) be the potential arrival time if the packet is first submitted at s.
The experiment must correctly describe the counterfactual response to every
allowed first-send policy. Assume

    s <= t  implies  A(s,omega) <= A(t,omega).

Define Q_s = {A(s,omega) <= C} for one fixed eligible packet episode and cut,
where arrival by C is the stipulated packet qualification. Native acceptance,
call validity, and namespace cancellation are separate obligations. For any
bounded adaptive later send time tau >= s, pointwise nesting gives

    1{Q_tau} <= 1{Q_s}.

Taking conditional expectations proves that waiting cannot improve this fixed
packet's qualification. The player may learn arbitrarily much about omega;
the argument works for every prior and every signal about this experiment.
It also survives conditioning on foreign failures and weighting by any
nonnegative continuation value, provided the SAME experiment and SAME
continuation weights apply under both policies.

Two concrete classes satisfy the comparison:

* **Shared processing opportunities.** Packets are admitted at the next eligible
  opportunity in an exogenous sequence with bounded gaps. Capacity is reserved
  for the bounded modeled raw traffic, not merely honest traffic. All owners
  can share the same unknown sequence; their delays can be strongly correlated.
* **Correlated latent lags.** Each coordinate has a latent delay D_e, possibly
  correlated with every other coordinate, and A_e(s) = s + D_e. Alternative
  send times use the same latent D_e. Learning it cannot make later arrival
  earlier in that coupled comparison.

These are nonempty mathematical service classes, not claims about an unmodified
chain. Admission buffers must not discard an earlier packet because it waited
longer. Fee changes, replacement packets, channel selection, and probes require
their own comparisons. Shared-capacity contention or opponents' reactions can
also change foreign outcomes, which the packet inequality does not control.

For a concrete protected instance of one newly ready block, give each owner
a stochastic first opportunity within r. Let ingress for coordinate e take a
fixed hidden lag D_e <= Delta, arbitrarily correlated across coordinates.
Process all pending eligible packets at shared exogenous epochs whose gaps
are at most B, reserving capacity for the entire modeled raw budget. A deadline
T > r + Delta + B guarantees prompt processing. Earlier sends reach ingress
and the next epoch no later under the same experiment. This is not a claim
about unreserved chain blockspace or a full preservation theorem.

## A weaker condition on players' conditional predictions

For one fixed packet, let F_t contain everything the player has observed while
not yet sending, and put q_t = P(Q_t | F_t). A prior-specific sufficient
condition is

    E[q_(t+1) | F_t] <= q_t.

This is a bounded supermartingale. Finite-horizon optional sampling gives
E[q_tau | F_s] <= q_s for every bounded adaptive send time tau >= s.
Conversely, requiring this comparison for every stopping policy at every
no-send node implies the displayed one-step inequality. The potential-service
experiment must describe actual interventions; a purely observational
correlation does not specify what happens if the player changes send time.

For example, let Theta be an unknown persistent network regime. Given Theta,
suppose a new packet has a stationary lag law F_Theta, conditionally independent
of the entire pre-send information given Theta. Players can learn Theta, and delays are
correlated through it. Nevertheless,

    q_t = E[F_Theta(C-t) | F_t],
    E[q_(t+1) | F_t] = E[F_Theta(C-t-1) | F_t] <= q_t.

Thus actual unconditional delay independence is unnecessary. The condition
concerns what observations let the player predict and exploit. For a fixed
prior it can hold even when some individual latent environments violate a
pathwise comparison; the conclusion then concerns that Bayesian mixture.
Uniform guarantees over all possible environments require stronger hypotheses.
This particular latent-regime example also admits a common-quantile pathwise
coupling; it is not an example separating the two sufficient conditions.

This statement remains a packet result. The qualification supermartingale
alone is insufficient for utilities when successful delivery can select a
more valuable source or retry branch.

## Two counterexamples to tempting shortcuts

**Equal marginal success does not control adaptive timing.** At time zero,
success probability is .6. At time one, a signal reveals a fair hidden regime:
success is .7 in H and .5 in L. At time two it is .6 in both. Every fixed send
time has marginal success .6, but sending at one in H and at two in L succeeds
with probability .65. Initially unknown dependencies can therefore create an
opportunity to learn and wait.

**Unchanged success probability does not control continuation value.** There
are two equally likely foreign-miss states, bad and good. An early send
qualifies only in bad, a later send only in good. Success probability is .5
either way, and the conditional success process is a martingale when the state
is revealed. Let qualified payoffs be 0 in bad and 10 in good, with permanent
own-failure payoff -1. Early expected payoff is -.5; later expected payoff is
4.5. This is a finite comparison example, not a new native-runtime refutation.

For the existing conditional block proof, the delivery comparison must hold
conditional on the SAME foreign-miss experiment J, or must control the
payoff-weighted quantity

    r_t = E[1{Q_t} (X_J-a) | F_t],

where X_J is the source/retry continuation value and a the own-failure floor.
Pathwise nesting handles all nonnegative weights X_J-a; an unconditional
success-probability inequality need not. A utility-specific r condition is a
proof criterion, not a primitive network guarantee.

## Remaining preservation obligations

The candidate service closer to an idealized ledger is a shared sequence of
bounded inclusion opportunities that processes every eligible modeled game
packet, with enough opportunity to submit after readiness. It permits variable
activation and transaction order, hidden common congestion, and correlated
delays. It does not require an exact activation calendar or independent packets.

Turning its delivery lemma into a whole-game proof still requires:

1. Joint source-information fidelity: the foreign-miss experiment, complete
   observations, and qualification must preserve the actual original source
   posterior. Neutrality only after conditioning on J is insufficient.
2. A comparison that retains foreign admission and responses. The focal owner
   must not change them through capacity competition or early cancellation.
3. A retry coupling carrying catalogs, private recall, elapsed time, and old
   receipts; canceled choices must not acquire a new strategic effect.
4. One common consistent assessment giving optimal continuation at delayed,
   unreached, and restarted information sets.

These are the full-proof gaps. We have not shown that consensus assumptions,
the new correlated-service class, or ignorance of dependencies establishes
them automatically.

Unknown-law beliefs that simply ignore actual predictive evidence are not the
Bayesian consistency required by the current SE target. Ambiguity aversion or
misspecified learning can be studied, but would require a different decision
model; no such target change is adopted here. Similarly, high-probability
ledger guarantees cannot silently replace the exact zero-failure on-path law.
Small ex ante errors also need not stay small after conditioning on a rare
information set.
