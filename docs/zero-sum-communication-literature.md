# Correlation, credibility, and competitive game classes

## What the equilibrium concepts remember

The library's `IsCorrelatedEq` is ordinary normal-form correlated equilibrium:
a device recommends a complete strategy, and each player may replace their
recommendation by another strategy. Sequential equilibrium additionally checks
optimal continuation behavior at every decision information set and requires
one common sequence of fully mixed strategies and Bayesian beliefs.
Kreps and Wilson's original criterion explicitly includes decisions off the
equilibrium path. [Kreps and Wilson (1982)](https://www.gsb.stanford.edu/faculty-research/publications/sequential-equilibrium)

Consequently, a theorem preserving normal-form CE constraints has no automatic
access to all SE constraints. This is a proved separation here, including
equality of the complete normal-form outcome map, rather than merely a warning
about different definitions.

### Checked counterexample: the same normal form, different SE outcomes

[CorrelatedSequentialGap.lean](../GameTheoryExtensionsTests/CorrelatedSequentialGap.lean)
defines two actual protocols with the following terminal utilities:

| Entrant's choice | Incumbent's choice | Public result | Entrant | Incumbent |
| --- | --- | --- | ---: | ---: |
| Out | Either | Out | 1 | 2 |
| Enter | Fight | Fight | -1 | -1 |
| Enter | Accommodate | Accommodate | 2 | 1 |

In the source, both players act at the initial simultaneous decision. In the
target, the entrant acts first; the incumbent acts only after observing Enter.
Each player has one binary decision. Both pure normal forms are obtained by
running their respective protocols, and their profile-to-outcome maps agree.

Out/Fight is an SE of the simultaneous source: entering against Fight loses,
and the incumbent cannot change the result when the entrant chooses Out.
The checked proof supplies a consistent assessment, including its common
tremble witness. The same profile is a CE of either normal form. But in the
sequential target, accommodating is strictly better after Enter; with this
continuation, the entrant can obtain two by entering. Every target SE gives the
entrant expected utility at least two, excluding the source's Out outcome.
This argument allows arbitrary target strategies and beliefs.

The capstone
`CorrelatedSequentialGap.correlated_preservation_without_sequential_outcome_preservation`
is in namespace `GameTheoryExtensionsTests`. Supporting theorems are
`normalForm_equal`, `correlated_equilibrium_iff`, `threat_correlated`, and
`no_target_equilibrium_out`. The CE equivalence quantifies over **all
preferences**, whereas the SE failure uses the single utility in the table.
This is a finite diagnostic game, not a claim that the Vegas compiler performs
this particular transformation. Its utility is not zero-sum.

Extensive-form correlated equilibrium is another concept: its mediator reveals
a recommended move only when its information set is reached. Recommendation
timing and the permitted deviations are part of that model. Replacing ordinary
CE by EFCE therefore changes the premise; it does not convert a normal-form
transport theorem into an unmediated SE theorem.
[von Stengel and Forges (2008)](https://doi.org/10.1287/moor.1080.0340)

## Two-player zero-sum: distinguish value, law, and repair

The checked root theorem
`GameTheory.IsCoarseCorrelatedEq.expectedUtility_eq_of_zeroSum` compares any
coarse correlated equilibrium with an existing Nash equilibrium of the same
two-player zero-sum game form. Strategy carriers may themselves be behavioral
policies. Its conclusion is equality of each player's **expected utility**.
The [runtime bridge](zero-sum-runtime-bridge.md) identifies the actual pending
service to which the compiler instantiation applies and the remaining gap to
the finite reactive service.

Expected value does not determine the payout law, even when utility is exactly
the amount paid. Consider actions `x,y ∈ {-1,0,1}` and payout vector `(xy,-xy)`.
Both the pure profile `(0,0)` and independent fair choices of `-1` and `1` are
Nash equilibria. Proof: against an opponent with mean zero, every action has
expected payoff zero. Their payout laws are respectively

```text
δ_(0,0)             and             ½ δ_(1,-1) + ½ δ_(-1,1).
```

Thus zero-sum value equality alone cannot establish the paper's stronger
preservation of public-result or payout distributions.
[ZeroSumOutcomeLaws.lean](../GameTheoryExtensionsTests/ZeroSumOutcomeLaws.lean)
checks this example with the existing matrix-game semantics: both profiles are
mixed Nash, utility is exactly the zero-sum payout vector, expected utilities
agree, and the payout laws differ. The distinguishing statistic is the first
player's squared payout, whose expectations are zero and one.

An independent route is to preserve Nash first, then repair only off-path target
behavior while preserving the initialized outcome law. The
[sequential repair note](zero-sum-sequential-repair.md) gives a mathematical
argument for finite two-player zero-sum games with perfect recall. It is not
yet a Lean theorem or a completed native compilation result. Its conclusion
would be existence of a matching SE; it would not make every compiled profile
sequentially rational. The distinction matters even if the source compiler
already preserves CE.

## A positive disclosure result with a precisely limited environment

Saas considers a finite, complete-information simultaneous base game preceded
by private coordination signals and optional public verifiable disclosure.
Disclosure-proof outcomes admit a no-disclosure SE of the extended game.
Section 5 gives `DPCE(G) = CE(G)` for two-player zero-sum games. The definition
allows choosing the signal structure; Lemma 1 separately characterizes a fixed
structure. Replacing SE by BNE removes the credibility restriction behind the
participation constraints. [Saas, June 2025 manuscript, Lemma 1 and Section 5](https://eller.arizona.edu/sites/default/files/2025-10/Disclosure_Proof_Correlated_Equilibria-8.pdf)

**A fixed-structure specialization to investigate.** For exogenous finite signals
in a two-player zero-sum complete-information game, prescribe an existing
signal-contingent BNE when both players remain silent; after any public
disclosure, both switch to a fixed minimax equilibrium. Every type can already
secure the minimax value by ignoring its signal, so disclosure cannot improve
its payoff. The continuation is rational under any posterior. Independent,
type-independent disclosure trembles preserve the intended limiting beliefs
on silence; full-support action trembles complete consistency. This is a
written construction, not a checked native adapter.

The assumptions doing the work are public detection of disclosure, a common
continuation phase after disclosure, exogenous signals, unchanged base-game
actions, and absence of disclosure costs. The native protocol has endogenous
commitments, selective recipients, and actions between evidence transmission
and inclusion. To use this construction there, one must prove that the actual
information and continuation structure supports it. Neither a minimax slogan
nor the ability to send a message supplies that proof.

## Which multiplayer restrictions are substantive?

### A single prize does not make all players opponents

For three players with utility equal to receiving a unit prize, changing the
winner probabilities from `(0,1/4,3/4)` to `(1/4,1/2,1/4)` benefits both the first
and second players. Each terminal outcome still has exactly one winner and the
sum of prizes remains one. This explicit calculation shows why exclusivity at
terminal outcomes does not imply opposed preferences over lotteries.

There is a stronger written extension of the checked credibility example.
Add a third player with no decisions, and replace each terminal result with a
lottery awarding one unit to exactly one player:

| Original result | Entrant wins | Incumbent wins | Third player wins |
| --- | ---: | ---: | ---: |
| Out | 1/6 | 1/4 | 7/12 |
| Fight | 0 | 0 | 1 |
| Accommodate | 1/4 | 1/6 | 7/12 |

If the original utilities are `(u_A,u_B)`, the first two winning probabilities
are `(u_A+1)/12` and `(u_B+1)/12`; the third receives the remainder. All displayed
probabilities are nonnegative and sum to one. Expected prize utilities are
positive affine transforms of the original utilities, so every incentive
inequality has the same sign; the new chance move occurs after all decisions
and changes no earlier information. The inactive player adds no deviations.
Consequently the source Out/Fight SE remains, whereas target sequential
rationality forces Accommodate after Enter and then Enter at the root. Their
winner distributions differ. This is a written derivation from the checked
fixture, not an additional Lean theorem. It rules out a general SE-preservation
claim based solely on three-player constant-sum or winner-take-all payoffs.

### Strict competition must include randomized choices

Adler, Daskalakis, and Papadimitriou prove that a two-player matrix game whose
expected preferences are opposed over every pair of mixed-strategy profiles
is positively affine equivalent to a zero-sum game. Opposite rankings only at
pure outcomes are a weaker condition and do not justify the same conclusion.
[Theorem 1, primary manuscript](https://people.csail.mit.edu/costis/SCG_1.pdf)

For our purpose this supports a two-player affine-zero-sum condition on the
declared utility. It does not supply a multiplayer condition, nor show that
arbitrary runtime continuations preserve the required utility structure.

### Zero-sum polymatrix is a real additional restriction

Cai, Candogan, Daskalakis, and Papadimitriou study games whose player payoffs
decompose into pairwise terms and whose total payoff is always zero.
Theorem 2 says that the **product of a CCE's marginals** is Nash. Individual
Nash payoffs need not be unique, strategies need not be interchangeable, and
individual minimax strategies need not be Nash strategies.
[Cai et al. (2016), Section 3](https://www.cs.yale.edu/homes/cai/publication/cai-zero-sum-2016/cai-zero-sum-2016.pdf)

Their proof also gives payoff equality between the CCE and that product:
writing `w_i` for the correlated payoff and `x` for its marginal profile,
pairwise separability and CCE imply `w_i ≥ max_a U_i(a,x_-i) ≥ U_i(x)`.
Both payoff sums are zero, so every inequality `w_i ≥ U_i(x)` is equality.
This preserves expected payoffs, not the joint recommendation or terminal law.
It is a static theorem and contains no off-path belief condition.

For a dynamic extension, the substantive condition must hold on the induced
strategic or realization-plan payoffs, not merely on isolated terminal
transfers. A later action may depend on several players' earlier messages;
substituting such strategies into pairwise-looking terminal transfers can
destroy pairwise separability. The
[repair note's multiplayer section](zero-sum-sequential-repair.md#a-multiplayer-extension-with-a-precise-sufficient-condition)
investigates an aggregate unilateral-deviation condition and a realization-plan
polymatrix instance. These remain written research arguments, without a native
recognizer or a general Vegas theorem.

## Design consequence

Keep three contracts explicit:

1. Preserve ordinary Nash/CE incentives in the initialized policy game.
2. Under a utility restriction, preserve equilibrium expected values.
3. Construct consistent, rational native continuations preserving the desired
   outcome law, possibly by repairing off-path behavior.

The first does not imply the third in general, as the checked example proves.
Two-player zero-sum structure supports the second and gives a substantive route
to investigate the third. Multiplayer prize conservation alone does neither
job; a stronger strategic structure must be established for the actual game.
