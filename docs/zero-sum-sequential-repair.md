# Repairing zero-sum Nash outcomes to sequential equilibria

## Status and exact claim

This note gives a mathematical proof of the complete repair theorem; that
theorem is not yet formalized in Lean. Finite decision tables, local trembles,
the conditional probability floor, and the finite L1 saddle construction have
checked implementations, listed below. Their remaining composition with
continuation incentives and limits is still open. No published
source for this exact outcome-preserving repair statement has been identified;
the references below supply its standard ingredients.

**Theorem (initialized outcome repair).** Let a finite extensive-form game have
two players, perfect recall, and terminal utilities `u₂ = -u₁`. Fix the chance
law and a behavioral Nash equilibrium `b*`. There is a sequential equilibrium
assessment `(b, μ)` such that:

1. `b` agrees with `b*` at every information set reached with positive
   probability under `b*`;
2. `b` and `b*` induce the same probability distribution over terminal histories.

The conclusion therefore preserves the law of every function of the initialized
terminal history, including public results and payouts. It need not preserve
off-path behavior, the law against an arbitrary opponent, or continuation laws
from arbitrary starts. The same theorem applies to two-player constant-sum
games after subtracting the constant from one utility.

Chance edges of probability zero are deleted before constructing the game.
Equivalently, every information set considered has at least one history with
positive chance reach. This makes Bayes beliefs well defined under every fully
mixed behavioral profile. No assumption of perfect information or public
observations is made.

## Standard representation

For each player `i`, let `Sᵢ` be the finite set of their own action sequences,
including the empty sequence. Action labels identify their information sets.
Perfect recall gives a unique preceding own sequence `q(I)` at every information
set `I`. A realization plan is a vector `x ∈ [0,1]^Sᵢ` satisfying

```text
x(∅) = 1,
Σ_{a ∈ A(I)} x(q(I)a) = x(q(I)).
```

These constraints define a nonempty compact convex polytope `Xᵢ`. Every behavior
strategy induces such a plan. Conversely, a plan determines behavior by
`b(a|I) = x(q(I)a)/x(q(I))` when the denominator is positive; choices at zero
denominators can be completed arbitrarily. Expected utility has the bilinear
form `U₁(x,y) = xᵀAy`, with chance probabilities incorporated in `A`. These are
the sequence-form facts proved by
[von Stengel (1996)](https://www.sciencedirect.com/science/article/pii/S0899825696900500).

Write `x*`, `y*` for the plans of `b*`, and `v = U₁(x*,y*)`. Nash equilibrium and
zero-sum utility give the two security inequalities

```text
U₁(x,y*) ≤ v ≤ U₁(x*,y)           for all x ∈ X₁, y ∈ X₂.       (1)
```

Let `H ≥ 1` bound the number of player decision nodes on any path, let `M ≥ 1`
bound every action-set cardinality, and let `B ≥ 0` bound the absolute terminal
utility. These loose finite bounds suffice for every estimate below.

## Protect exactly the reached decisions

Let `Rᵢ` contain player `i`'s information sets with positive reach under `b*`.
Define the protected sequence coordinates and their absolute-value penalty by

```text
Pᵢ = {q(I), q(I)a : I ∈ Rᵢ, a ∈ A(I)},
Dᵢ(x) = Σ_{q ∈ Pᵢ} |x(q) - x*(q)|.
```

Let `Kᵢ = |Pᵢ|` and `K = K₁ + K₂`. Each penalty is continuous and convex, and
`0 ≤ Dᵢ ≤ Kᵢ`. Protecting all outgoing coordinates includes actions assigned
probability zero at reached information sets; otherwise new terminal paths
could appear in the limit.

**Locality lemma.** If `I ∉ Rᵢ`, changing player `i`'s continuation at `I` and
their subsequent information sets leaves every coordinate in `Pᵢ` unchanged.

Proof. Perfect recall implies that if one history at a subsequent information
set `J` passes through `I`, every history in `J` has `I` and the same intervening
own actions in its recall. Hence `Pr_b*(J) ≤ Pr_b*(I) = 0`. A local continuation
change at `I` can affect only sequences containing an action at `I`; none of the
protected preceding or outgoing sequences can contain such an action. This is
an exact statement for every realization plan, including fully mixed plans;
it is not an asymptotic estimate. ∎

## Perturbed saddle problems

For `0 < ε < 1/M`, impose the linear inequalities

```text
Xᵢ(ε) = {x ∈ Xᵢ : x(q(I)a) ≥ ε x(q(I)) for every I,a}.
```

Every own sequence has positive realization in this polytope, by induction on
sequence length, and the corresponding behavioral probability of each action
is at least `ε`. Conversely, every such behavioral strategy lies in the
polytope. It is compact, convex, and nonempty.

One explicit approximation to any behavior strategy is

```text
b^ε(a|I) = (1 - |A(I)| ε) b(a|I) + ε.                         (2)
```

At one information set this changes total variation distance by at most
`M ε`. Coupling along a path gives the following uniform bounds:

```text
|x^ε(q) - x(q)| ≤ H M ε,
|Uᵢ(bᵢ^ε, c₋ᵢ) - Uᵢ(bᵢ, c₋ᵢ)| ≤ 2 B H M ε.               (3)
```

The second bound holds for every fixed opposing strategy. The same coupling
bound holds for continuation utility from any belief over an information set.

For `δ > 0`, consider the zero-sum saddle objective

```text
F_{ε,δ}(x,y) = U₁(x,y) - δ D₁(x) + δ D₂(y)
```

on `X₁(ε) × X₂(ε)`, with player 1 maximizing and player 2 minimizing. It is
continuous, concave in `x`, and convex in `y`. Compactness and
[Sion's minimax theorem, Theorem 3.4](https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-p.pdf)
give a saddle point `(x_{ε,δ}, y_{ε,δ})`. The penalty is an auxiliary analytical
device; it is not a change to the source or runtime utility.

Choose positive sequences `δₙ → 0`, `εₙ → 0` with `εₙ/δₙ → 0`. For example,

```text
δₙ = 1/(n+1),          εₙ = δₙ²/(2M).
```

Let `(xₙ,yₙ)` be corresponding saddle points and `bⁿ` their fully mixed
behavioral profiles. Let `μⁿ` be their Bayes beliefs. Finitely many behavior and
belief simplexes are compact, so pass to one subsequence along which
`(bⁿ,μⁿ) → (b,μ)`. This common sequence proves Kreps–Wilson consistency of
the limit assessment. All subsequent arguments use this same subsequence.

## The protected coordinates return to the prescribed equilibrium

Apply the two saddle inequalities using the smoothed original plans
`x*^{εₙ}` and `y*^{εₙ}`. Adding them cancels the actual saddle payoff:

```text
δₙ [D₁(xₙ) + D₂(yₙ)]
  ≤ U₁(xₙ,y*^{εₙ}) - U₁(x*^{εₙ},yₙ)
    + δₙ [D₁(x*^{εₙ}) + D₂(y*^{εₙ})].                      (4)
```

By (1), `U₁(xₙ,y*) - U₁(x*,yₙ) ≤ 0`. By (3), replacing the two original
plans by their smoothings changes this expression by at most `4 B H M εₙ`.
The coordinate bound in (3) also gives
`D₁(x*^{εₙ}) + D₂(y*^{εₙ}) ≤ K H M εₙ`. Therefore

```text
D₁(xₙ) + D₂(yₙ)
  ≤ 4 B H M (εₙ/δₙ) + K H M εₙ → 0.                      (5)
```

At each originally reached information set, `x*(q(I)) > 0`. Both that
coordinate and all outgoing coordinates converge to their original values.
The quotient defining behavior therefore gives `b(a|I) = b*(a|I)`.

Induct on tree depth to obtain equality of the initialized history laws.
Positive-probability prefixes use the same behavioral distributions and chance
law. A zero-probability prefix cannot acquire probability: its first zero edge
is either a fixed chance edge or an action of probability zero at an originally
reached information set, whose probability is preserved. Thus terminal laws
are equal, including probabilities of terminals outside the original support.

## Sequential rationality at every information set

Fix a player `i`, an information set `I`, and an arbitrary behavioral
continuation `τᵢ` from `I`. Localize the deviation to `I` and subsequent own
information sets. Perfect recall ensures this has exactly the intended
continuation effect and changes no behavior before reaching `I`.

Smooth the deviating continuation by (2), retain `bⁿ` elsewhere, and call the
resulting full strategy `cᵢⁿ`. Its realization plan lies in `Xᵢ(εₙ)`. Let
`pₙ(I) > 0` be the reach of `I` under `bⁿ`. Since the deviation is localized,
the exact payoff difference factorizes as

```text
Uᵢ(cᵢⁿ,b₋ᵢⁿ) - Uᵢ(bⁿ)
  = pₙ(I) [Vᵢ(τᵢ^{εₙ}; μⁿ_I,b₋ᵢⁿ)
            - Vᵢ(bᵢⁿ; μⁿ_I,b₋ᵢⁿ)].                     (6)
```

Here `Vᵢ` is conditional continuation utility. No comparison of opponents'
reach probabilities is needed: both sides use the same prefix law and the same
Bayes belief `μⁿ_I`. The saddle best-response inequality gives

```text
Uᵢ(cᵢⁿ,b₋ᵢⁿ) - Uᵢ(bⁿ)
  ≤ δₙ [Dᵢ(cᵢⁿ) - Dᵢ(bᵢⁿ)].                            (7)
```

There are two cases.

**Originally unreached `I`.** The locality lemma makes the right-hand side of
(7) exactly zero. Divide (6) by `pₙ(I)` and use (3) for the deviating
continuation:

```text
Vᵢ(τᵢ; μⁿ_I,b₋ᵢⁿ) - Vᵢ(bᵢⁿ; μⁿ_I,b₋ᵢⁿ) ≤ 2 B H M εₙ. (8)
```

This bound has no `1/pₙ(I)` term. In particular, it remains valid if the
information set requires several simultaneous trembles or has extremely small
reach. This exact cancellation is the essential point of the construction.

**Originally reached `I`.** Equality of the limiting initialized law gives
`pₙ(I) → p*(I) > 0`. The penalty difference in (7) is at most `Kᵢ`, so the
same calculation gives

```text
Vᵢ(τᵢ; μⁿ_I,b₋ᵢⁿ) - Vᵢ(bᵢⁿ; μⁿ_I,b₋ᵢⁿ)
  ≤ δₙ Kᵢ/pₙ(I) + 2 B H M εₙ → 0.                       (9)
```

All continuation utilities are finite polynomials in behavior probabilities
and linear in the belief at `I`. Pass to the common limit in (8) or (9).
Because `τᵢ` was arbitrary, `bᵢ` is optimal against every entire continuation
deviation at `I`, given `μ_I` and `b₋ᵢ`. This proves sequential rationality
directly; it does not rely on a one-step deviation principle. Together with
consistency it proves the theorem. ∎

## Checks on the scope and fragile steps

| Potential problem | Why the proof addresses it |
| --- | --- |
| Equal values need not imply equal outcomes | Equation (5) fixes every reached decision, including zero-probability actions. |
| Off-path realization may have positive own reach | Protection depends on joint information-set reach under `b*`; it does not protect every positive own coordinate. |
| Conditional incentives divide by tiny reach | For originally unreached information sets the penalty cancels exactly before division. |
| Independent belief choices may be inconsistent | Every belief is obtained from one subsequence of the same fully mixed profiles. |
| A continuation might change a protected later coordinate | Perfect recall makes every own information set after an unreached one unreached as well. |
| Behavioral tremble constraints might be nonconvex | Their realization-plan form `x(qa) ≥ εx(q)` is linear. |
| Ordinary perturbations might select a different Nash outcome | The rate `εₙ/δₙ → 0` makes the prescribed reached-coordinate penalty dominate the smoothing error. |

It would be incorrect to penalize every realization coordinate. For example,
Alice chooses `Out` (payoff 0) or `In`; after `In`, Bob chooses between giving
Alice payoff -2 or -1. The profile `Out`, followed by -1 off path, is Nash.
Sequential rationality requires Bob to choose -2. Its initialized outcome can
be preserved, but Bob's strategy against an entering Alice must change.

Zero-sum with three players is insufficient. Alice chooses `Out`, yielding
`(1,1,-2)`, or `In`; after `In`, Bob chooses `Fight`, yielding `(0,0,0)`, or
`Accept`, yielding `(2,2,-4)`. Carol has no effective decision. `Out/Fight` is
Nash. Sequential rationality forces `Accept`, then `In`, so no sequential
equilibrium preserves the `Out` outcome. Every terminal payoff vector sums to
zero. Carol can be given a payoff-irrelevant choice without changing this
argument. A multiplayer extension needs a stronger strategic condition than
the sum of utilities being zero.

## A multiplayer extension with a precise sufficient condition

This section has the same mathematical, non-formal status as the two-player
proof. Keep a finite perfect-recall extensive game, now with `N` players. Its
realization-plan domains `Xᵢ` are independent compact convex polytopes. Each
expected utility `Uᵢ(x)` is continuous and affine in player `i`'s own plan;
with more than two players it can have higher-order interactions across the
other plans.

For a specified original profile `x*`, impose the following **aggregate
unilateral inequality**:

```text
A_{x*}(x) := Σᵢ [Uᵢ(xᵢ*, x₋ᵢ) - Uᵢ(x)] ≥ 0
                                      for every x ∈ ∏ᵢ Xᵢ.   (10)
```

This is a condition on the supplied profile and the actual game. It does not
postulate an equilibrium, belief system, or repair in a second game. It implies
that `x*` is Nash: substitute a profile differing from `x*` only at player `i`;
every other summand is zero and the remaining summand is exactly their Nash
inequality. An arbitrary Nash equilibrium need not satisfy (10).

**Multiplayer repair theorem.** If the original behavioral profile has
realization profile `x*` satisfying (10), there is an SE agreeing at all its
reached information sets and preserving its complete initialized terminal law.

To prove this, use exactly the same protected coordinates, smoothing, and
rates as above. On the perturbed product domain `∏ᵢ Xᵢ(εₙ)`, give each player
the auxiliary payoff

```text
Gᵢⁿ(x) = Uᵢ(x) - δₙ Dᵢ(xᵢ).
```

These payoffs are continuous and concave in the player's own coordinate.
The compact convex concave-game Nash existence theorem gives a Nash profile
`xⁿ`. Unlike the two-player argument, this is a concave-game fixed-point
argument; it is not a two-player saddle problem. The needed existence result
is the product-domain special case of
[Rosen (1965)](https://doi.org/10.2307/1911749).

The Nash inequality against `xᵢ*^{εₙ}` gives, for each player,

```text
δₙ Dᵢ(xᵢⁿ)
  ≤ Uᵢ(xⁿ) - Uᵢ(xᵢ*^{εₙ},x₋ᵢⁿ) + δₙ Dᵢ(xᵢ*^{εₙ}).
```

Sum over players, use (3) to remove each smoothing, and apply (10):

```text
δₙ Σᵢ Dᵢ(xᵢⁿ)
  ≤ -A_{x*}(xⁿ) + 2 N B H M εₙ + δₙ K H M εₙ
  ≤ 2 N B H M εₙ + δₙ K H M εₙ.                            (11)
```

Thus every protected coordinate returns to its prescribed value. The proof of
sequential rationality uses only each player's own best-response inequality,
their own penalty locality, and a common fully mixed sequence. Equations
(6)--(9) therefore apply unchanged. This proves the multiplayer theorem. ∎

### A structural class: pairwise zero-sum realization payoffs

A useful game-wide sufficient condition is an actual expected-payoff
decomposition

```text
Uᵢ(x) = Σ_{j ≠ i} xᵢᵀ Aᵢⱼ xⱼ,
Aⱼᵢ = -Aᵢⱼᵀ.                                             (12)
```

This is a zero-sum polymatrix structure on the realization-plan domains.
The domains need not be simplexes. The familiar normal-form class and its
minimax connections are studied by
[Cai, Candogan, Daskalakis, and Papadimitriou (2016)](https://www.cs.yale.edu/homes/cai/publication/cai-zero-sum-2016/cai-zero-sum-2016.pdf).
The argument here proves the particular inequality needed for repair directly.

Let `x*` be any Nash equilibrium. Antisymmetry gives both

```text
Σᵢ Uᵢ(x) = 0,
Σᵢ Uᵢ(xᵢ*,x₋ᵢ) = -Σᵢ Uᵢ(xᵢ,x₋ᵢ*).                     (13)
```

The second equality follows by exchanging the ordered pair of indices in
the sum and transposing its scalar terms. The individual Nash inequalities,
summed at `x*`, give

```text
Σᵢ Uᵢ(xᵢ,x₋ᵢ*) ≤ Σᵢ Uᵢ(x*) = 0.
```

Combining this with (13) proves (10) for every feasible `x`. Consequently,
every Nash outcome of a finite perfect-recall game satisfying (12) admits the
same sequential repair. This includes the two-player zero-sum case, for which
the only two matrices are `A` and `-Aᵀ`.

Condition (12) is about expected utility as a function of complete realization
plans. Terminal payoffs merely summing to zero does not imply it. Even a
pairwise-looking terminal payment rule can acquire higher-order interactions
when a third player's choices control whether the payment event is reached.
The decomposition must therefore be proved for the game's actual expected
payoff map before this corollary is used. No classification of all repairable
multiplayer games, or necessity of (10), is claimed.

## What this would give a compiler

Suppose a compiler already sends each source Nash profile to a Nash profile of
the **same finite native game** used for sequential-equilibrium analysis,
preserving a decoded initialized result law. Suppose both players' native
utilities are zero-sum. Applying this theorem to the translated profile gives
a native sequential equilibrium with that same decoded law. In particular it
implements every source sequential-equilibrium outcome, since source SE is
source Nash.

This is existence of an implementing sequential assessment after off-path
repair. It does not say the original playerwise translated strategies form an
SE, preserve source beliefs, or work unchanged in every continuation.
The construction depends on the whole equilibrium profile: its protected
information sets are those reached jointly by all players. It therefore does
not itself produce a playerwise compiler that can translate each strategy
independently of its opponents. Selecting and repairing a known equilibrium
profile is the operation justified by this theorem.
Additional explicit finite-game and protocol bridges are required before
applying it to VegasCore. In particular, a Nash theorem for one target
application cannot silently be used as a theorem for a different reactive
application.

## Preferred formalization: finite plans and sign tests

The existence steps above can be reduced to finite-game equilibrium existence.
This avoids requiring a new general theory of convex realization polytopes in
Lean. The construction is an auxiliary proof game; it adds no runtime behavior
or compilation stage.

### Trembling pure plans span exactly the permitted behaviors

Let `Πᵢ` be the finite set of deterministic behavioral plans. Interpret a plan
`πᵢ` with a fresh local tremble at every visited information set: execute its
prescribed action with probability `1-(|A(I)|-1)ε` and every other action with
probability `ε`. Let `rᵢ^ε(πᵢ)` be this strategy's realization vector.

A distribution over these plans is equivalent to behavior with every action
probability at least `ε`. Conditional on the player's own recalled prefix,
their latent prescribed action has some posterior distribution `ν_I`, and
the next local tremble is fresh. The action law is therefore
`ε + (1-|A(I)|ε)ν_I(a)`. Perfect recall makes that posterior a function of
their information set; the usual mixed-to-behavioral realization argument
then preserves every outcome against every opposing strategy.

Conversely, for a behavioral strategy `bᵢ` with this probability floor,
independently draw the prescribed action at each information set from

```text
ν_I(a) = [bᵢ(a|I)-ε] / [1-|A(I)|ε].                       (14)
```

These are probability distributions because `ε < 1/M`. The resulting product
distribution on pure plans, followed by the fresh trembles, realizes `bᵢ`.
Independence and perfect recall ensure that an information set's prescription
has not already been used and remains distributed as (14) when reached.
Thus the convex hull of `rᵢ^ε(Πᵢ)` is exactly the permitted realization set.
For formalization it suffices to prove these finite mixture and realization
facts; the full polytope equality is not required as a separate interface.

### Two-player existence from one finite zero-sum game

Player 1's auxiliary pure choice is a plan `π₁` and a sign vector
`s₁ ∈ {-1,1}^{P₂}`; player 2 chooses `π₂` and
`s₂ ∈ {-1,1}^{P₁}`. Let `U^ε(π₁,π₂)` be actual expected utility when both
plans are executed with fresh trembles. Define the auxiliary player-1 payoff

```text
U^ε(π₁,π₂)
  - δ Σ_{q∈P₁} s₂(q) [r₁^ε(π₁)(q)-x*(q)]
  + δ Σ_{q∈P₂} s₁(q) [r₂^ε(π₂)(q)-y*(q)].                 (15)
```

Player 2 receives its negative. This is an ordinary finite zero-sum matrix
game, so the existing finite mixed minimax theorem supplies an equilibrium.
Project its two plan marginals to realization vectors `x,y`, and its sign
marginals to expected vectors `s̄₁,s̄₂`. Correlation between a player's own plan
and sign creates no extra term: each summand in (15) pairs variables belonging
to different players, whose mixed choices are independent. Expected payoff is

```text
U₁(x,y) - δ s̄₂·(x-x*) + δ s̄₁·(y-y*).
```

Holding their plan marginal fixed, each player can replace the sign marginal
arbitrarily. Optimality of these sign choices gives

```text
s̄₂·(x-x*) = D₁(x),       s̄₁·(y-y*) = D₂(y).             (16)
```

For every other permitted plan `x'`, the absolute-value inequality gives
`s̄₂·(x'-x*) ≤ D₁(x')`. The plan best-response inequality, keeping player 1's
own sign marginal fixed, consequently implies

```text
U₁(x',y) - δD₁(x')
  ≤ U₁(x',y) - δs̄₂·(x'-x*)
  ≤ U₁(x,y) - δs̄₂·(x-x*)
  = U₁(x,y) - δD₁(x).
```

The analogous inequality for player 2 gives
`U₁(x,y)+δD₂(y) ≤ U₁(x,y')+δD₂(y')`. Hence `x,y` form the exact saddle of
`F_{ε,δ}` needed above. This proves full optimality against permitted plans,
not merely a first-order stationarity condition.

### Multiplayer existence from finite Nash existence

For the multiplayer proof, use one ordinary plan player and one auxiliary sign
tester per original player. Plan player `i` chooses `πᵢ`; their tester chooses
`sᵢ ∈ {-1,1}^{Pᵢ}`. Give the plan player payoff

```text
Uᵢ^ε(π) - δ sᵢ·[rᵢ^ε(πᵢ)-xᵢ*],
```

and their tester payoff `δ sᵢ·[rᵢ^ε(πᵢ)-xᵢ*]`. Ordinary finite mixed Nash
existence provides a profile. Each independent tester supports the absolute
penalty at its plan player's marginal, exactly as in (16). The same
absolute-value inequality turns each plan player's best response into a best
response for `Uᵢ(x)-δDᵢ(xᵢ)` on all permitted realizations. The original plan
marginals therefore supply precisely the regularized Nash profile used in
(11). The testers disappear after this existence proof and play no role in
the limiting assessment of the original game.

## Literature and formalization boundary

[Miltersen and Sørensen (2006)](https://pure.au.dk/portal/en/publications/computing-sequential-equilibria-for-two-player-games-2/)
prove polynomial-time computation of an SE in finite two-player zero-sum
perfect-recall games; their reported result also obtains normal-form
perfection. That existence/computation result does not by itself assert repair
of an arbitrary prescribed Nash outcome. The argument above uses selective
regularization to establish that additional conclusion.

The existing `GameTheory` code defines finite protocol assessments,
sequential rationality, consistency, and zero-sum saddle points. The extension
library supplies compactness-based consistent completions, but a consistent
completion need not be rational. There is no checked complete repair theorem
or general finite-game SE existence theorem in the current development.

The following ingredients are checked in the Lean kernel:

| File | Checked result |
| --- | --- |
| [`FiniteInformation.lean`](../GameTheoryExtensions/Protocol/FiniteInformation.lean) | `DecisionPlan` is a table on legal decision sites, finite when legal histories and those menus are finite. Pure and behavioral restriction/extension preserve the complete run law from every legal history. Ambient information may be infinite. |
| [`Tremble.lean`](../GameTheoryExtensions/Math/Probability/Tremble.lean) | `prob_tremble`, `le_prob_tremble`, and `tremble_removeTremble` establish the local floor and exact residual decomposition. `pi_bind` exchanges independent sampling with coordinate kernels. `le_prob_condOn_mixture_pi` retains a common floor under arbitrary correlated mixtures and conditioning on other coordinates. |
| [`TremblingPlans.lean`](../GameTheoryExtensions/Protocol/TremblingPlans.lean) | `BehavioralDecisionPlan.residualPlans_tremble` recovers the exact independent decision-table law. `trembledMixedPolicy_consistent` proves every legal decision record has positive compatible mass. `le_prob_trembledMixedPolicy_toBehavioralWith` proves that the existing mixed-to-behavioral realization retains epsilon at every legal decision choice. |
| [`ZeroSumRegularization.lean`](../GameTheoryExtensions/Analysis/ZeroSumRegularization.lean) | `exists_saddle` and `penalty_bound` establish the finite L1 sign-game construction and its penalty estimate, allowing correlations between each player's plan and sign tests. |

The protocol floor theorem assumes perfect recall, finite decision sites,
finite site menus, `ε > 0`, and `ε·card(menu) ≤ 1` at every site. It permits an
arbitrary correlated distribution over prescribed plans and an arbitrary legal
fallback policy. It has no remaining positive-record-mass premise. Its proof
establishes both that the record restrictions are satisfiable and that the
current decision coordinate does not already occur in the player's record;
the weaker `ConstrainsAlike` property alone is not used in place of recall.

The existing `runMixed_toBehavioralWith` theorem then gives the exact initialized
history law of the constructed mixed policy for every horizon. One remaining
execution bridge must identify the independently pre-drawn noisy decision
table with fresh local trembling along the existing behavioral runner. Perfect
recall makes this mathematically valid, but that specific table-product bridge
has not yet been connected to the existing finite-site predrawing theorem.

Formalizing this proof requires the following substantive bridges, rather than
a theorem with its conclusion hidden in an assumption:

1. Finish the fresh-behavior/predrawn-table execution bridge, then identify
   remembered-sequence realization coordinates as finite-plan expectations.
2. Prove the uniform smoothing estimates and connect the checked finite L1
   estimate to the protected protocol coordinates in (5). The multiplayer
   auxiliary sign-test existence argument is also not yet formalized.
3. Prove exact off-path locality of those protected coordinates and the
   conditional bounds (8) and (9), including the localized-continuation
   identity (6).
4. Obtain a common behavior-and-belief limit, using the existing consistency
   infrastructure where its hypotheses match.

The proof concerns finite games. It does not remove the bounded-interaction
assumption or address computational equilibria and cryptographic trembles.
