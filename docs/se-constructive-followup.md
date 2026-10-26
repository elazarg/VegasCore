# Constructive preservation experiments

This work extends the checked constructions in the
[constructive ledger](se-preservation-constructive-experiments.md). The four
experiments have dedicated branches. Only verified improvements are merged;
an unhelpful experiment is retained on its branch with its checked evidence,
adapter costs, and reason for rejection. Work shares one checkout without
worktrees; file ownership is disjoint and the integration owner handles Git
and normal builds.

| Experiment | Branch | Acceptance boundary | State |
| --- | --- | --- | --- |
| Finite-game power completeness | `research/power-completeness` | Extract a certificate for the same assessment from an actual consistency sequence, including real coefficients and integer exponents | Finite global-coordinate case checked end to end; finite actual-coordinate generalization in progress |
| Actual Vegas finite representation | `research/vegas-observable-representation` | Check actual transitions, private views, legal policies and joint payoff/readout observables; measure closure and total adapter cost | Two-decision payment program selected; compiled graph representation in progress; native lift remains separate |
| Conditional observable certificates | `research/conditional-observable-certificates` | Derive actual conditional expectations from tensor certificates with unequal positive observation masses, every adaptive policy and a common parameter family | Tensor word identity checked; actual transcript/Bayes adapter in progress |
| Production preservation consumers | `research/production-preservation-consumers` | Improve an actual Vegas conditional-gain proof while retaining all deviations, the common assessment sequence and selected joint law | Candidate comparisons under investigation; integrates accepted producers |

## Rational homogeneous directions

[RationalStrictDirection](../GameTheoryExtensions/Math/RationalStrictDirection.lean)
proves that a real feasible direction for finite rational homogeneous equations
and strict inequalities admits a rational direction for the exact same system,
then an integer one after clearing a positive common denominator. A rational
projection repairs dense rational approximants without disturbing the equality
constraints. Coordinate positivity can be included among the strict rows.

This is a supporting linear-algebra result. It does not extract logarithmic
constraints from games or establish power completeness by itself. The existing
power soundness theorem and all runtime preservation assumptions remain intact.

## Power completeness with finite global coordinates

[PowerCompleteness](../GameTheoryExtensions/Analysis/Protocol/PowerCompleteness.lean)
extracts positive real coefficients, natural exponents and reference histories
for the **same** supplied assessment from its actual sequential consistency.
The current theorem assumes finite players, finite ambient information states,
finite local choices and finite actual histories. It derives all logarithmic
constraints from the actual common Bayes sequence; none is an extra hypothesis.
Positive prescribed action masses get exponent zero and their prescribed
coefficient. Zero prescribed action masses get positive integer orders. Every
positive/zero belief history satisfies the soundness certificate's exact
coefficient ratio and equal/higher order conditions.

The proof supplies full support and prescribed convergence at unused strategy
coordinates without changing any actual evaluator weight or Bayesian belief,
then combines actual trace-count identities and Bayes log-ratio limits with
the real affine-ray and integer-direction theorems. The
[nonzero-payoff extraction client](../GameTheoryExtensionsTests/PowerExtraction.lean)
supplies only the existing game's checked consistency and obtains the whole
certificate; it supplies no rates or affine/logarithmic constraints.

This finite-global case is a checked mathematical construction, not a production
Vegas instantiation. An ambient information carrier can contain infinitely many
unreachable views even when actual histories are finite. A finite actual-trace
coordinate adapter is being investigated to remove that avoidable restriction.
