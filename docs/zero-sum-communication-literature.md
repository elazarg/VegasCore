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
writing $w_i$ for the correlated payoff and `x` for its marginal profile,
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

## Preserving a component of the game

### What potential and harmonic components do identify

For a fixed finite normal form, Candogan, Menache, Ozdaglar, and Parrilo
decompose payoff tables into potential, harmonic, and nonstrategic parts.
Potential differences come from one scalar function on strategy profiles;
harmonic differences describe the remaining circulation of unilateral
incentives. Nonstrategic payoffs are independent of the receiving player's
own strategy. These statements concern incentives in that fixed normal form,
not the existence of communication or coalitions. Their equality between CE
and mixed Nash for two-player harmonic games is generic, rather than an
unconditional identification of the concepts.
[Candogan et al. (2011), Sections 4 and 5](https://arxiv.org/abs/1005.2405)

Zero-sum and harmonic are not interchangeable hypotheses. For example, let
Alice choose a bit `a`, let Bob have any finite nonempty action set, and set payoffs
to `(a,-a)`. The game is zero-sum, but Alice strictly prefers `a = 1`.
Consequently uniform play is not Nash, whereas uniform play is Nash in every
harmonic game under the paper's uniform decomposition. Potential structure
describes unilateral payoff differences; it does not specify which coalitions
or messages players can use. Hwang and Rey-Bellet explicitly separate normalized zero-sum,
normalized common-interest, and zero-sum-equivalent potential components;
their decomposition is useful precisely because these classifications are
not a single competition-versus-cooperation dichotomy.
[Hwang and Rey-Bellet (2020), Theorem 2.1](https://arxiv.org/abs/1602.06648)

A compiler presents an additional problem: source and target have different
strategy spaces. Even duplicating a strategically redundant action can change
the decomposition obtained by counting every action equally. Abdou,
Pnevmatikos, Scarsini, and Venel give weighted decompositions whose components
commute with elimination of duplicate strategies after the weights are
transported appropriately. This supports component transport for genuine
strategy duplication; it does not establish transport when a new message
enables an opponent to react.
[Abdou et al. (2020), Theorem 3.19](https://arxiv.org/abs/1901.06048)

Thus a Hodge-component theorem would require a specified correspondence
between strategy spaces, compatible weights, and a proof that decomposition
commutes with that correspondence. For a runtime with additional information
and reactions, those are substantive obligations. Calling its harmonic part
the source's competitive content would not discharge them.

### A nonstrategic payoff can acquire strategic force through a message

The checked [component example](../GameTheoryExtensionsTests/ComponentCommunication.lean)
is independent of cryptographic commitments. In
the source Alice and Bob choose bits simultaneously, with payoffs `(b,0)`.
Every profile is Nash: Alice cannot change Bob's bit, and Bob is indifferent.
Alice's entire payoff is nonstrategic in this normal form.

In the target, Alice first sends a bit `m`, after which Bob chooses `b`.
Fix Bob's strategy to `b = m`. Alice's payoff now changes from zero to one
when she changes her message. The payoff formula is unchanged, but Bob's
fixed strategy is a response function, so fixing it no longer fixes Bob's
action. The profile `m = 0, b = m` is not even Nash. Bob's indifference makes
his response optimal after either message; no computational,
ownership, authentication, or secrecy assumption is involved.

This example does not claim a failure of existential outcome implementation:
Bob could instead choose a constant response. It establishes the narrower
point needed for component reasoning: being nonstrategic in the source is
not enough to remain nonstrategic after adding communication. A similar
warning applies to replacing a zero-sum-equivalent game by its zero-sum
representative: the removed terms must remain irrelevant to *native*
deviations, including continuations. Source strategic equivalence alone does
not prove that.

### A component criterion on the shared payoff space

The direct alternative is to work with declared outcome utilities, whose
coordinates have the same meaning on both sides of compilation. The following
is checked by `IncentiveComparison.mem_coneWithin_iff` in
[IncentiveCone.lean](../GameTheoryExtensions/Core/IncentiveCone.lean).

Fix source and target assessments and their observed outcome maps into a
common finite set `Omega`. Include private types in `Omega` if utilities
depend on them. Let

```text
V = R^(Players × Omega).
```

An element of `V` is a complete payoff profile. For a comparison concerning
player `i`, lift the prescribed-minus-deviation outcome difference `d` to
`e_i ⊗ d` in `V`: its coordinates are zero for all other players. Write
$s_j$ for these joint source vectors and $t_k$ for the joint target vectors.
Then rationality is exactly the family of inequalities
`<s_j,u> >= 0` or `<t_k,u> >= 0`, respectively.

Choose a linear payoff class `L` in `V`, with orthogonal projection `P_L`.
Examples include outcome-by-outcome two-player zero-sum utilities, payoffs
depending only on designated outcome features, and linear combinations of
specified transfers. The exact criterion is

```text
for every u in L:
  (all <s_j,u> >= 0) implies (all <t_k,u> >= 0)

iff

every P_L(t_k) belongs to the closed convex cone generated by the P_L(s_j).
```

Proof: for `u` in `L`, taking the inner product with a vector or its projection
gives the same result. Apply the finite-dimensional bipolar/separation
criterion inside `L`, exactly as in
[IncentiveCone.lean](../GameTheoryExtensions/Core/IncentiveCone.lean).
Failure produces a separating payoff profile **inside the declared class**,
rather than an arbitrary utility outside it.

Using one joint payoff space is essential. Two-player zero-sum is the coupled
restriction `u_A(omega) + u_B(omega) = 0`; each player's coordinate projection
separately contains every utility. Treating players independently would lose
the restriction. In the joint space the cone certificate can combine source
incentive inequalities of different players, because their payoffs satisfy
the declared relationship.

[CoupledIncentives.lean](../GameTheoryExtensionsTests/CoupledIncentives.lean)
checks a strict separation: Bob's preference for one outcome implies Alice's
preference for the other under the joint zero-sum restriction. The projected
target comparison belongs to the source cone, while its unrestricted
counterpart lies outside it, with an explicit separating utility.

This criterion compares the actual games under a specified payoff class.
It is not an inference that an equilibrium of one summand of a payoff table
is an equilibrium of the full table. It also does not provide belief
consistency: a sequential-equilibrium theorem still needs a consistent target
assessment and the desired initialized outcome law. Quantifying the criterion
over a compiler's assessment construction supplies the incentive part of
such a theorem; one fixed assessment comparison is not a compiler theorem.

The actual protocol instantiations are
`sequential_rationality_preservation_iff_coneWithin` in
[SequentialIncentives.lean](../GameTheoryExtensions/Protocol/SequentialIncentives.lean)
and `sequential_equilibrium_preservation_iff_coneWithin` in
[Sequential.lean](../GameTheoryExtensions/Analysis/Protocol/Sequential.lean).
They use the existing continuation assessments and whole-policy deviations.
For a consistent source assessment, the latter characterizes preservation
over the payoff class by target consistency plus the projected cone condition.
It does not construct a native assessment or establish its decoded outcome law.

### Extracting a retained component and bounding the rest

There is also a constructive sufficient certificate. For each target
comparison, choose a finite nonnegative combination of source comparisons,
and define its residual:

```text
c_kj >= 0
r_k = t_k - sum_j c_kj s_j
W = intersection_k { u : <r_k,u> = 0 }.
```

For every utility in `W`, source rationality implies target rationality.
This follows by taking inner products in the defining equality and summing
the nonnegative source inequalities. `W` is the largest subspace on which
**these chosen comparison combinations agree exactly**; it need not be the
largest payoff class supporting preservation. Different certificates may
produce different subspaces, and preservation classes need not be subspaces.
With explicit finite comparison lists, finding `W` for given coefficients is
ordinary linear algebra. No enumeration algorithm for arbitrary protocols or
all assessments follows from that observation.

More usefully, this certificate says something about the original game even
when its utility is outside `W`. Write `u = P_W u + u_perp`. If the source
assessment is rational for the **full utility** `u`, then

```text
<t_k,u> >= <r_k,u_perp> >= -norm(r_k) * norm(u_perp).
```

The first inequality expands the residual identity and uses source
rationality; the second is Cauchy--Schwarz. Thus the component outside `W`
bounds the size of profitable target continuation deviations. For finite
comparison lists, their maximum is an explicit common bound. There is no
assumption that the source assessment is rational separately for `P_W u`.
This is a potentially useful preservation result even when exact SE transport
fails: the retained component contributes no unexplained incentive change,
and the remaining component gives a quantitative error bound. A consistent
target assessment is still required to interpret it as approximate
sequential rationality with consistent beliefs.

The quantitative inequality is checked by
`IncentiveComparison.regret_le_norm_comparison_residual` in
[IncentiveCone.lean](../GameTheoryExtensions/Core/IncentiveCone.lean).
`IncentiveComparison.mem_comparison_error_orthogonal_iff` additionally
characterizes the largest subspace preserving every incentive margin for a
specified alignment of source and target comparisons. Equality of margins is
stronger than preservation of their signs.

### An interpretable component associated with correlation

Suppose a particular runtime difference changes only the coupling of two
finite outcome features `x` and `y`, preserving both marginal laws. Every
payoff of the form `f(x) + g(y)` then has exactly the same expectation on both
sides. Conversely, if a payoff has the same expectation under every pair of
joint laws with matching marginals, it has this additive form.

For the converse, compare the equally weighted laws on `(x,y),(x0,y0)` and
on `(x,y0),(x0,y)`. Their marginals agree, so

```text
u(x,y) + u(x0,y0) = u(x,y0) + u(x0,y).
```

Choosing fixed basepoints gives
`u(x,y) = u(x,y0) + u(x0,y) - u(x0,y0)`, the required decomposition.
The forward direction is linearity of expectation. Empty feature sets are
vacuous; otherwise the basepoints exist.

One can also extract the component explicitly. Choose reference distributions
`alpha` and `beta`, and define

```text
I_u(x,y) = u(x,y) - E_beta[u(x,Y)] - E_alpha[u(X,y)]
                   + E_(alpha × beta)[u(X,Y)].
```

The subtracted part is additive. Consequently any two joint laws `p,q` with
matching marginals satisfy the exact identity

```text
E_p[u] - E_q[u] = E_p[I_u] - E_q[I_u].
```

This follows by cancelling the expectations of the additive terms. When
`alpha,beta` are the marginals of `p` and `q = alpha × beta`, the mean of
`I_u` under `q` is zero, so the gain from correlation is precisely `E_p[I_u]`.
Finite support suffices for these identities; the feature carriers themselves
need not be finite. This is a payoff identity for the original utility,
rather than an equilibrium claim about a substituted component game.

This identifies a genuine interaction component: sensitivity to correlations
lies in the cross differences of the payoff table. It could certify that an
abstraction preserving selected marginals also preserves selected incentives,
provided the marginal premise is established for the relevant prescribed and
deviating continuations. Early disclosure can change the recipient's action
marginal as well as its correlation with a secret, so that premise must be
proved for the particular runtime edge. Additive payoffs alone are not a
general theorem that communication can be erased.

These correlation statements are checked in
[CorrelationPayoff.lean](../GameTheoryExtensions/Analysis/CorrelationPayoff.lean):
`preserves_marginals_iff_additive`, `expectation_difference_eq_interaction`,
and `correlation_gain_eq_interaction`. Their hypotheses concern the actual
joint laws. They do not assume a particular message format or commitment owner.

### Recommended scope

The next runtime obligation is to instantiate the checked joint payoff-subspace
criterion and residual bound against an isolated feature whose incentive
differences are understood. They share the existing protocol and assessment
semantics. Hodge decomposition can later supply a candidate
subspace when a compatible strategy correspondence has been proved; it does
not need to become another level of the compilation tower.

These arguments themselves impose no rule about who may generate a
commitment, copy its randomness, share an opening, or construct a message.
Those rules affect the target comparison vectors. A certificate established
for an owner-only ideal target must be checked again when cooperative
construction, evidence sharing, or additional fabrication is admitted.
Correlation in a distribution over strategies and a larger set of executable
strategies are separate changes; allowing the former does not automatically
account for the latter.
