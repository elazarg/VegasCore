# Honest off-path disclosure can prevent SE preservation

This is Codex's analysis of a boundary for a general preservation theorem.
Matching a selected source equilibrium's honest on-path execution is
insufficient. Information correspondence must also constrain legitimate source
continuations that the selected equilibrium does not take. The following finite
game gives an exact example. Its source assessment is a sequential equilibrium;
the corresponding outcome cannot be implemented by any target sequential
equilibrium or weak PBE. Nash can implement that outcome.

The example and its consistency witness below are a mathematical proof, not an
instantiation of the repository's protocol SE predicate. The checked generic
results relevant to its obstruction are identified at the end. No checklist
box or runtime semantics changes follow from this note.

## The two games

Nature samples a bit `v`, with probabilities `Pr(v = 1) = 9/20` and
`Pr(v = 0) = 11/20`. The sender learns `v` and chooses `Out` or `In`.
`Out` terminates the game. `In` activates the receiver, who chooses a guess
`g` in `{0, 1}`. The payoffs are:

| Terminal outcome | Sender | Receiver |
| --- | --- | --- |
| `Out` | `1/2` | `0` |
| `In`, then `g` | `2 * [g = 1]` | `[g = v]` |

The sender's preference for guess `1` does not depend on its bit. This is a
permitted preference specification, and prevents a sender type from secretly
having a different incentive in the source assessment.

In the **source**, the receiver observes `In` but does not learn `v`. Its two
decision histories belong to one information set. In the **target**, executing
the same legitimate `In` move discloses `v` to the receiver before it chooses.
The receiver therefore has two singleton information sets. Neither game has
extra moves, scheduling risk, fees, penalties, or strategically controlled
nature. Both are finite games with perfect recall and the same payoffs.

The retained terminal outcome is `(v, Out)` or `(v, In, g)`. Its initial-bit
coordinate can be erased without changing the nonpreservation conclusion.

## A source sequential equilibrium

Consider the assessment in which both sender types choose `Out`, the receiver
guesses `0` after `In`, and its belief there is `Pr(v = 1 | In) = 9/20`.

Write `x_v` for the sender's probability of `In`, and `y` for the receiver's
probability of guess `1`. A sender type's continuation value is

```
V_sender(x_v, y) = (1 - x_v)/2 + 2*x_v*y.
```

At `y = 0`, this is `(1 - x_v)/2`, strictly maximized by `x_v = 0`.
The receiver's continuation value under belief `p` is

```
V_receiver(p, y) = p*y + (1 - p)*(1 - y).
```

For `p = 9/20`, this is `11/20 - y/10`, strictly maximized by `y = 0`.
These comparisons cover every continuation deviation: each player moves at
most once. The assessment is sequentially rational at every information set.

Consistency has an explicit common fully mixed witness. For natural `n`, put
`epsilon_n = 1/(n + 2)`. At each sender information set, choose `In` with
probability `epsilon_n`; after `In`, choose guess `1` with probability
`epsilon_n`. Every legal action has positive probability, and these strategies
converge to the stated pure strategy profile. Bayes' rule at the receiver gives

```
Pr(v = 1 | In)
  = ((9/20)*epsilon_n)
    / ((9/20)*epsilon_n + (11/20)*epsilon_n)
  = 9/20.
```

The belief is constant along the sequence. At each sender information set,
the unique compatible history supplies its belief. Thus one sequence of fully
mixed profiles and its Bayes assessments converges to the specified assessment.
This proves Kreps-Wilson consistency and establishes a source SE. It also
establishes a source PBE under definitions imposing these same compatibility,
Bayes, rationality, and consistency requirements.

## The target cannot preserve this outcome as SE or PBE

After target `In`, the receiver knows `v`. Its unique sequentially rational
response is `g = v`. This holds at an unreached information set as well as a
reached one: a singleton has only one compatible history, so every compatible
belief assigns that history probability one. Bayes requirements at positive
reach are not needed for this step.

The type-`1` sender therefore gets `2` from `In` and `1/2` from `Out`; the
type-`0` sender gets `0` from `In` and `1/2` from `Out`. Consequently every
sequentially rational target assessment uses

```
type 1: In;   type 0: Out;   receiver: guess the disclosed bit.
```

This assessment is itself a target SE. For example, let type `1` choose
`In` with probability `1 - epsilon_n`, type `0` choose `In` with probability
`epsilon_n`, and the receiver at each information set guess the correct bit
with probability `1 - epsilon_n`. The strategies are fully mixed and converge
to the stated profile; all decision beliefs are their uniquely compatible
singleton beliefs. This proves target consistency. The target therefore has an
SE, but every target SE has `Pr(In) = 9/20`, whereas the designated source SE
has `Pr(In) = 0`.

For the terminal outcomes above, the total variation distance from the source
law is exactly `9/20`: the target moves probability `9/20` from `(1, Out)`
to `(1, In, 1)`. The same distance remains after retaining only whether `In`
occurred. Thus the failure survives removal of the secret and guess from the
observed outcome. There is no target weak PBE preserving the source law either,
provided weak PBE requires sequential rationality at every information set and
beliefs supported on compatible histories. Any stronger PBE refinement sharing
these requirements has the same obstruction.

The obstruction also has an explicit approximate-rationality bound. Here
`epsilon` means an absolute continuation-regret bound at each information set,
in the payoff units above: the best continuation's value minus the prescribed
continuation's value is at most `epsilon`. This is a local sequential criterion,
not an ex-ante approximate-Nash criterion weighted by the site's reach.

Suppose `0 <= epsilon < 1/2`. Let `y_1` be the receiver's probability of
guessing `1` after learning `v = 1`, and let `x_1` be that sender type's
probability of `In`. The receiver's regret bound gives

```
1 - y_1 <= epsilon,   so y_1 >= 1 - epsilon.
```

The sender's pure-`In` continuation has value `2*y_1`, whereas its prescribed
continuation has value `(1 - x_1)/2 + 2*x_1*y_1`. Therefore

```
(1 - x_1)*(2*y_1 - 1/2) <= epsilon.
```

Since `1 - x_1 >= 0` and `2*y_1 - 1/2 >= 3/2 - 2*epsilon > 0`, these imply

```
x_1 >= 1 - epsilon/(3/2 - 2*epsilon),

Pr(In) >= (9/20)*(1 - epsilon/(3/2 - 2*epsilon)) > 0.
```

The last inequality is strict because `epsilon < 1/2`. The same expression
lower-bounds total variation distance from the source all-`Out` law, even when
the readout retains only the entry indicator. No Bayes or consistency condition
beyond compatible singleton beliefs is needed for this bound.

The threshold `epsilon = 1/2` is sharp for this payoff normalization. Preserve
all-`Out`, let the receiver guess `1` with probability `1/2` after learning
`v = 1`, and let it guess `0` after learning `v = 0`. The true-type receiver's
regret is `1/2`; the true-type sender can improve from `1/2` to `1` and hence
also has regret `1/2`. All other decision regrets are zero. This assessment is
consistent: both sender types can tremble into `In` with probability
`epsilon_n`, the true-type receiver can keep its already fully mixed response,
and the false-type receiver can tremble to guess `1` with probability
`epsilon_n`. Their Bayes beliefs remain the compatible singleton beliefs.
Thus a consistent assessment with regret at most `1/2` can preserve the source
law. The numerical threshold concerns this game and these utility scales.

## Nash permits preservation

There is a target Nash equilibrium with both sender types choosing `Out` and
the receiver guessing `0` after either disclosed bit. Against that receiver
strategy, each sender type gets `0` from `In` and `1/2` from `Out`.
Against the all-`Out` sender strategy, the receiver's expected payoff is zero
for every response strategy. No player has a profitable unilateral deviation.

The receiver's response after learning `v = 1` is an off-path, noncredible
threat. It defeats SE and PBE rationality but does not defeat Nash optimality.
Accordingly, this example proves an information-related separation between
Nash and sequential preservation; it does not show Nash nonpreservation.

## What the example requires from a general theorem

The source SE's honest path always takes `Out`. Under the corresponding target
strategy, its execution, private information on that path, terminal outcomes,
and payoffs agree exactly with the source. The difference appears only after
the legitimate source choice `In`. A correctness condition referring solely
to the selected equilibrium's honest paths therefore admits this target and
cannot imply SE preservation.

The relevant larger set of paths is every faithful execution of legal source
continuations, including off-path choices. A suitable information adapter must
control what is learned along these continuations, or supply another argument
that the new information leaves the required continuation choices optimal.
An ordinary payoff or outcome simulation restricted to the selected
equilibrium does not supply this argument.

This is not a counterexample to a compiler already proved to protect the bit
on every faithful continuation. It is also not a universal public-mempool
impossibility. A source `In` packet can be opaque until the intended disclosure
point, or the source can explicitly expose the bit as part of `In`. Those are
different information models from the pair above.

A failure floor and a large timing-deviation penalty do not address this
example: `In` is an allowed source move, and its target execution is faithful.
Forfeiting collateral just because a sender takes `In` would change that
legitimate move's payoff. A general timing-enforcement theorem must first have
the information/payoff correspondence needed for all such source continuations.

## Existing checked boundaries

The library already contains a checked result that knowing a fact fixes its
posterior reward at any decision information set, including off-path ones:
`ContinuationDecision.expectedReward_of_known` in
[ObservationRequirement.lean](../GameTheoryExtensions/Analysis/Protocol/ObservationRequirement.lean).
Its response-factorization theorems prohibit merging decisions with disjoint
posterior maximizers. They formalize the kind of receiver obstruction used
here, but have not been instantiated with this two-player game.

For finite terminal decision experiments, the repository proves the exact
fixed-payoff boundary:
`preserves_fixed_payoff_sequentialEquilibria_iff_commonMaximizer` in
[DecisionPayoff.lean](../GameTheoryExtensions/Analysis/Protocol/DecisionPayoff.lean).
With the reporting payoff `[g = v]`, the supported states `0` and `1` have
disjoint unique maximizing guesses. A pooled observation has no common
maximizer. The exact criterion also allows added information when all states
in an observation fiber share a best action for the particular payoff.

Neither checked statement by itself establishes the entire two-player
source/target example as a library SE theorem. The paper proof above supplies
the full strategies, compatible beliefs, common tremble sequences, and local
continuation comparisons; a protocol instantiation remains separate work.
