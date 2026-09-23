# Behavioral assumptions for inclusion

## Working position

Preservation may assume a specified class of miner or service behavior. The
blockchain need not enforce every assumption of that class. The assumption
must have an operational interpretation, retain the players' available
deviations, and appear in the theorem statement.

For this project, a useful working hypothesis is that inclusion treats
competing commitments according to their delivery and fee attributes, without
using them as signals about the desired game outcome. Passive observation by
players remains available. The scheduler may retain public history.

Outcome indifference motivates such a hypothesis, but does not uniquely fix a
selection rule: an indifferent miner has several possible best responses.
Selection and tie breaking therefore need explicit behavioral assumptions as
well as an account of incentives. This distinction is familiar in transaction
fee analysis: Roughgarden defines miner utility separately from the intended
allocation rule and asks whether following that rule maximizes utility.
[Transaction Fee Mechanism Design, Sections 3.2 and 5.1](https://arxiv.org/html/2106.01340).

The [early-opening counterexample](early-opening-and-spe.md) proves that the
current recovery compiler can fail SPE with a fixed schedule and uniform,
at-most-once selection. Event-local neutrality alone leaves competition
between transmissions for different events unresolved.

No positive native SPE theorem is established by this note. The local regularity
argument, its converse, the weighted and priority selectors, and the compiler's
local recovery inequality are checked in Lean. Composition through the
reactive service needs a contract addressing this counterexample, in addition
to correspondence of proper subgames.

## Proof and assumption boundaries

The implementation separates three responsibilities:

| Layer | Checked result |
|---|---|
| `GameTheoryExtensions/Math/Probability` | Regularity, its expectation characterization, exact displaced-mass coupling, and weighted and priority choice laws |
| `GameTheoryExtensions/Core` | Optimal optional submissions, supported recovery, and exact response-law factorization under regular selection |
| `Interaction` | Pending-or-published invariant, at-most-once service contract, all-replay invariance for unpublished menus, and concrete selection laws |
| `Vegas/Pending` | The recovery lottery instantiates the local incentive theorem; the active reserved service includes each identifier at most once at every legal history |

The mathematical statements developed here have the following proof anchors:

- [`expect_gain_eq`, `RegularAt.expect_le`, and `regularAt_iff_expect_le`](../GameTheoryExtensions/Math/Probability/Regularity.lean)
  prove the gain identity, sufficiency, and converse.
- [`RegularSelection.optimal_response`, `RegularSelection.optimal_response_of_support`, and `RegularSelection.nash_preserved`](../GameTheoryExtensions/Core/RegularChoice.lean)
  prove the local incentive statements with a fixed stochastic continuation.
- [`regular_option_restore`](../GameTheoryExtensions/Math/Probability/RegularCoupling.lean)
  and [`RegularSelection.responseLaw_factor`](../GameTheoryExtensions/Core/RegularChoiceSimulation.lean)
  prove exact simulation with a response-independent branch law. Silence uses
  the distribution of displaced old probability mass on the fresh branch.
- [`interaction_history_publishedOnce`](../Vegas/Pending/ReactiveServicePublication.lean)
  proves at-most-once inclusion in the actual service, including rejected calls.
- [`replay_unpublished_history`](../Interaction/ReactivePublication.lean)
  proves all-replay menu invariance at arbitrary legal initialized histories.
- [`prioritySelection_responses_factor`](../Interaction/ReactiveSelection.lean)
  factors the decoded selection law after arbitrary randomized native responses
  through a fixed branch law, with an explicit decoder and fresh-candidate value.
- [`bindingSelection_history_regular` and `bindingSelection_value_independent`](../Vegas/Pending/ReactiveSelection.lean)
  prove all-response regularity and independence from hidden commitment meanings
  for the public binding-acceptance selector. These concern immediate selection;
  future scheduling and the decoded continuation remain separate obligations.
- [`weightedSet_insert` and `weightedSet_one`](../GameTheoryExtensions/Math/Probability/WeightedSet.lean)
  prove the weighted mixture equation and equal-weight specialization.
- [`PriorityChoice.choose_insert` and `law_regular_insert`](../GameTheoryExtensions/Math/Probability/PriorityChoice.lean)
  prove stability under insertion and regularity for finite mixtures of rankings.
- [`before_eq`, `after_eq`, `regular`, and `not_fixed_mixture`](../GameTheoryExtensionsTests/RegularChoice.lean)
  prove the strict separation example below.
- [`PendingPriority.lean`](../Interaction/PendingPriority.lean) and
  [`PendingWeighted.lean`](../Interaction/PendingWeighted.lean) lift the choice
  rules to network packets, including replay and passive learning.
- [`RetainsEligible.replay_ids`](../Interaction/PendingSelection.lean) covers
  all raw replays under an explicit candidate-retention premise. The
  [removed-envelope example](../InteractionTests/PendingPriority.lean) proves
  why already-pending replay invariance alone does not discharge that premise.
- [`reactiveRecoveryLaw_regular_optimal`](../Vegas/Pending/ReactiveRegularity.lean)
  applies the local theorem to the compiler's recovery policy.

All distributions in these results have finite support. Referenced background
results, such as Luce's representation theorem and the exponential-race
construction, are proved in the cited sources; they are not imported Lean
theorems or dependencies of our preservation argument.

## A sufficient special case: unchanged relative odds

Fix the current prefix and a nonempty set `S` of competing eligible messages.
Let `q(i)` be the probability of selecting old message `i` if no new candidate
is submitted. For a fresh message `c`, require

```text
P(select c from S + c) = p
P(select i from S + c) = (1 - p) q(i)     for every i in S.
```

Thus the conditional law over old messages is unchanged whenever it has
positive probability. The multiplication form also covers `p = 1`, where
conditioning on an old winner would be undefined.

The probability `p` must also be independent of the source value encoded in `c`, with
delivery and fee attributes held fixed. This is a second condition: preserving
old relative odds alone does not make different new values equally competitive.
The local proof also fixes the downstream continuation kernel across the
responses compared.

The relative-odds condition is the local form of Luce's choice axiom, often
expressed as independence of irrelevant alternatives. Under positivity and
consistency across finite menus, choice probabilities have a representation
by positive candidate weights divided by total weight. Applying it here is a
modeling decision about inclusion, rather than a claim about consumer choice.
[Luce, *Luce's choice axiom*](https://doi.org/10.4249/scholarpedia.8077).

Name blindness is weaker. An algorithm can ignore packet contents and names
while selecting the first old arrival when three messages are pending and
the second when only two are pending. Relabeling packets preserves that rule,
but insertion changes the old winner. The reactive counterexample exploits
this kind of dependence on traffic.

## Fees and concrete selection rules

### Fixed weights

Give each eligible candidate a positive weight based on permitted attributes,
and select proportionally to weight. If old total weight is `W` and the new
weight is `w`, then

```text
p = w / (W + w).
```

Every old probability is multiplied by `W / (W + w)`. The equation is checked
by `weightedSet_insert`; `weightedPending_append_fresh` applies it to the
network. Uniform selection is the checked equal-weight case. Weights can
depend on fees; their definition must leave old
weights unchanged and make the fresh weight independent of its encoded source
value. Fee-proportional sampling is an illustrative model, not an Ethereum rule.

Independent exponential clocks with these rates give the same weighted choice
law. That supplies a stochastic mechanism for the equation, without claiming
that actual propagation delays are exponential or independent.
[Maddison, *A Poisson process model for Monte Carlo*, Lemma 6](https://www.cs.toronto.edu/~cmaddis/pubs/ppmontecarlo.pdf).

### Fixed priorities

A selector can instead choose the highest-priority eligible candidate, breaking
ties consistently. If the ordering of old candidates is unchanged, inserting
a new candidate either leaves the old winner in place or makes the new
candidate win. At a fixed deterministic ranking, this satisfies the mixture
condition with `p = 0` or `p = 1`.

This has a direct fee-based motivation: EIP-1559 recommends prioritizing higher
priority fees and using receipt time to order equal-fee transactions. Those
recommendations support studying stable priority rules; they do not establish
our full service assumptions for block construction.
[EIP-1559, Transaction Ordering](https://eips.ethereum.org/EIPS/eip-1559#transaction-ordering).

Different miners may have different receipt orders. Mixing their rankings
need not preserve relative old probabilities, even if every ranking is stable.
The weaker condition below accommodates that case.

### Selection fees and utility costs are different obligations

Fee-sensitive priorities are compatible with the inclusion analysis. Allowing
the player to choose fees, and charging those fees in utility, introduces an
additional optimization problem. Knowing a source-optimal game action does
not reveal how much the player should pay to improve its inclusion chance.

An initial theorem may fix the fee policy or explicitly ignore fee costs.
It must still account for the delivery effects of any fee changes admitted as
native deviations. A result with fixed fees cannot silently quantify over
arbitrary fee bidding. Likewise, no local-computation charge is needed to
describe an actual transaction payment.

## A weaker sufficient condition: regularity

The local incentive argument does not require unchanged *relative* odds.
It is sufficient that adding a candidate never increases any old candidate's
*absolute* selection probability, provided the new candidate's encoded value
does not affect the selection law. In choice theory, the first condition is
called regularity.
[Fudenberg, Iijima, and Strzalecki, *Stochastic Choice and Revealed Perturbed Utility*, 2014 working paper, Definition 2](https://scholar.harvard.edu/files/tomasz/files/perturbed_choice.pdf).

Here is the derivation for a finite candidate set. Let:

- `q(i)` be the old selection probabilities without a submission;
- `r(i)` be the probabilities of those same old candidates after submission;
- `p` be the new candidate's probability, so `p = sum_i (q(i) - r(i))`;
- `V(i)` be the utility of the fixed continuation after old candidate `i`;
- `V*` be the utility of an optimal source action, with `V* >= V(i)` for all `i`.

Assume `r(i) <= q(i)` for every old candidate. Submitting a new candidate
encoding the source optimum improves on silence by

```text
p V* + sum_i r(i) V(i) - sum_i q(i) V(i)
  = sum_i (q(i) - r(i)) (V* - V(i))
  >= 0.
```

Encoding an alternative source action `a` in the new candidate keeps `p` and
the `r(i)` unchanged. Its disadvantage is therefore `p (V* - V(a)) >= 0`.
Taking averages gives the same conclusions for randomized responses and
optimal source lotteries independent of the selection randomness.
`RegularSelection.optimal_response` proves this with an arbitrary stochastic
continuation. `RegularSelection.optimal_response_of_support` permits the recovery policy to
reuse a supported optimal choice instead of sampling again.

There is also an exact local converse. If selecting after insertion weakly
improves expected utility for **every** utility having its maximum at the
fresh candidate, every other candidate's probability must weakly decrease.
To test one old candidate, give it utility minus one and every other candidate
utility zero. `regularAt_iff_expect_le` proves both directions. This
characterizes this utility-independent comparison with silence, not the class
of all services that preserve SPE for a particular source game.

This argument assumes selection of exactly one eligible candidate and a common
downstream kernel. An outside outcome such as expiry needs its own treatment
and dominance premise; it is not automatically a legal retained source choice.

### Why this weakening is operationally useful

Consider two possible miner rankings, each used with probability one half:

| Ranking | Without fresh C | With fresh C |
|---|---|---|
| A before C before B | A | A |
| C before B before A | B | C |

Before insertion, A and B each have probability one half. After insertion, A
and C each have probability one half, while B has probability zero. Relative
old odds change, so the mixture condition fails. Regularity still holds.

For every fixed ranking, the new message either wins or the previous winner
survives. If it contains a source-optimal choice, every displaced outcome is
weakly improved. Random selection of a miner or an ordering preserves that
inequality. The ranking law and this example are checked in Lean. They are
not a theorem about Ethereum.

Fixed priorities provide a particularly clear explanation: inserting a new
message does not reorder the older ones. It can overtake some of them. The
example above shows why this operational condition need not preserve their
relative *probabilities* after averaging over unknown arrival orders.

## Scope and tests of the assumption

The following are explicit modeling choices or external motivations, rather
than conclusions of the checked probability and incentive results:

| Subject | Assumption or unmodeled justification |
|---|---|
| Miner incentives | Outcome indifference motivates neutral selection; no miner utility or best-response theorem is implemented. Non-collusion alone is not the selection contract. |
| Priorities and weights | The same ranking distribution or weight function is used for the responses compared. It may describe delivery or fee attributes; the model does not derive those attributes from propagation or fees. |
| Encoded values | Holding transport attributes fixed must also hold the selection law fixed across fresh source values. Opaque commitment meaning alone does not establish this for every packet field. |
| Fees | There is no endogenous fee bid or fee charge in these results. Any future fee deviations require their own delivery and utility analysis. |
| Replays | Distinct-identifier selectors exclude published identifiers. Rebroadcasts remain observable and legal. No propagation effect is derived from a physical network model. |
| At-most-once inclusion | A published envelope is spent even if its call fails. A fresh envelope can retry the same payload. Ethereum nonces motivate this abstraction; nonce ordering, replacements, fees, and reorgs are not modeled. |
| Service composition | Every relevant inclusion and continuation must satisfy the proof premises. A regular selector installed only at the last step is insufficient to establish those premises. |

The concrete selectors deduplicate identifiers, rather than removing duplicate
broadcasts from the network. `*_replay` proves equality of selection laws for
an already pending envelope. `*_learn` proves that passive observation does
not alter those laws. Neither says that the player forgets what was read, or
that the player's later reactions are irrelevant. The active reserved service
has not been changed to use these selectors.

The useful behavioral premise is stronger than the statement that miners do
not collude. Even a miner maximizing only fees may face dependencies between
transactions or block-capacity constraints. Optimizing a whole block can
change which older transactions fit. A theorem about an isolated choice among
eligible candidates cannot be asserted for that optimization without a bridge.
Roughgarden's model explicitly optimizes fee revenue subject to feasibility;
its miner-incentive theorem does not imply Luce's choice axiom or regularity
for our commitment event.
[Transaction Fee Mechanism Design, Definition 5.1 and Theorem 5.2](https://arxiv.org/html/2106.01340).

The implementation and proof must address:

1. **Eligibility.** Identify the competing messages for one event. Account for
   invalid packets, nonce dependencies, receipt order, and expiry. Hidden source
   values must not change the relevant selection attributes.
2. **Replay and replacement.** Repeating an existing broadcast remains a legal
   operation. Deduplication may make it inert; improved propagation may make
   it useful. Any useful effect needs to be simulated or bounded. Neither
   regularity for fresh candidates nor the mixture equation alone covers all
   replay behaviors. The checked weighted-copy example isolates this gap.
   `RetainsEligible` is a checked sufficient invariant for replay to preserve
   each selector's eligible menu. The carrier's pending-or-published invariant
   establishes it at every legal history when eligibility excludes published
   identifiers. The active reactive service enforces at-most-once inclusion
   independently of application acceptance. The removed-envelope example shows
   why the exclusion matters for replay of a previously included identifier.
3. **Player capabilities.** The source-optimal value must be encodable with the
   transport attributes needed by the proof. A fresh packet cannot simply
   inherit an old packet's authentic timestamp or erase already distributed
   signatures. No private preparation cost is introduced.
4. **Intervening activity.** The law must describe the relevant continuation,
   not just a final reserved draw. Earlier inclusions, different activations,
   and deadline changes can settle the event first.
5. **Information and later play.** Foreign-message leaks and reactions remain
   in the model. Their effects must satisfy the continuation correspondence;
   neutral inclusion does not make public transmissions unobservable.
6. **Off-path scope.** The contract is needed at every proper target root,
   including legal histories with earlier deviations. The compiled player's
   initialized one-packet guarantee cannot discharge this requirement.

## Design recommendation

The at-most-once rule is an operational service guarantee, independent of
neutral-selection assumptions. The rule uses the public ledger, without
inspecting hidden commitment values. Ethereum's sequential nonce is external
motivation for this choice, not a verified backend correspondence.
[ERC-4337 nonce discussion](https://eips.ethereum.org/EIPS/eip-4337#semi-abstracted-nonce-support).

Keep the condition in the service's theorem premises. No source-language flag,
restricted raw player menu, or strategic miner player is needed merely to
state the assumption. Adding a miner as a strategic player would be a separate
extension if the goal becomes deriving its behavior from an explicit utility.

Use stable priorities and regularity as the broader candidate model; retain
the checked fixed-mixture lemma as a sufficient special case. Investigate
which version composes with the reactive service before committing the paper
to the stronger probability-ratio assumption. Both are legitimate explicit
behavioral hypotheses when their economic motivation, operational scope, and
excluded interference are stated.

The [inclusion investigation](inclusion-and-spe.md) records checked results.
The [reactive counterexample](reactive-inclusion-obstruction.md) identifies
behavior excluded by both conditions: a new packet with no chance of winning
increases one old packet's chance at another old packet's expense.
