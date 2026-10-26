# Constructive SE interfaces

This ledger records the checked scope of the
[constructive directions](se-preservation-constructive-directions.md).
These additions leave GameTheory, runtime semantics, the preservation target,
and its checklist unchanged. Supporting results do not close target boxes.

## Power-certificate soundness

[NormalizedPower](../GameTheoryExtensions/Math/Probability/NormalizedPower.lean)
constructs actual positive normalized PMFs. Local constant-term equations
identify their prescribed limits, including choices at unreachable sites.
[PowerReach](../GameTheoryExtensions/Analysis/Protocol/PowerReach.lean)
factors the existing behavioral history evaluator into the fixed Nature
probabilities, shared action coefficients, total natural exponent, and product
of encountered local denominators. Those denominators need not agree between
histories: each tends to one.

[PowerPosterior](../GameTheoryExtensions/Math/Probability/PowerPosterior.lean)
normalizes the finite information fibers after removing their common minimum
power. [PowerCertificate](../GameTheoryExtensions/Analysis/Protocol/PowerCertificate.lean)
constructs one common fully mixed Bayes sequence and proves consistency of
the exact supplied assessment from its support orders and coefficient ratios.
There is no premise assuming convergence of the Bayesian beliefs.

The assumptions are finite players, finite local choice sets, finite decision
information fibers, the existing decision-information antichain, positive
coefficients, natural orders, local constant-term equations, and the checked
fiber constraints. Global finiteness of the history carrier is unnecessary.
Completeness, extraction of certificates from arbitrary consistency sequences,
and preservation of a particular runtime mixture/coupling family are separate.

## Affine rays

[AffineRay](../GameTheoryExtensions/Math/AffineRay.lean) proves the finite real
linear statement: finite-limit equations and rows tending to positive infinity
give an exact intercept and a kernel direction strictly positive on every
divergent row. Its proof uses a continuous linear right inverse on the closed
finite-dimensional image. It adds no solver or dependency. This is the real
direction lemma; rational approximation, integer scaling, logarithmic game
interpretation, and power-certificate completeness are not conclusions.

## Closed observable spaces

[InvariantObservables](../GameTheoryExtensions/Math/InvariantObservables.lean)
constructs the least operator-invariant span of selected observables, proves
its finite-dimensional basis bound, and checks supplied spanning certificates
for every finite label word. Independence and minimality are unnecessary for
certificate soundness.

[PrivateObservableTransport](../GameTheoryExtensions/Analysis/PrivateObservableTransport.lean)
uses observation-filtered action operators and the existing transcript-local
behavioral runner. Closure under every observation/action branch preserves
bounded terminal scores for every adaptive policy. Including the readout
indicators preserves the **joint** law of final selected readout and full
input/output transcript. The operators retain observation probabilities.
Different finite systems can be represented on their disjoint union.

[The exact rational search](../scripts/experiments/observable_space.py) returns
spanning columns, closure/seed coordinates, and a distinguishing word when
the initial signed row fails to annihilate the space. Search is untrusted;
the Lean certificate theorem is the soundness boundary. The
[finite example](../GameTheoryExtensionsTests/ObservableClosure.lean) checks
the actual observation-filtered operators and proves the adaptive joint-law
conclusion for the computed two-dimensional space in a four-state system.
Five Python checks include direct reconstruction of matrix identities,
dependent and zero seeds, rational transitions, and a distinguishing trace
for an unclosed terminal observable.

This pilot has a finite, fixed all-action interface. It does not compile a
Vegas runtime or transport a dependent legal-action menu. It does not prove
the general tensor/cross-product conditional certificate, parameter-uniform
runtime certificates, or SE preservation from observable closure alone.

## Signed stopped residuals

[StoppedCharge](../GameTheoryExtensions/Analysis/Protocol/StoppedCharge.lean)
supplies exact drift and integrability for absolutely bounded signed charges;
its nonnegative APIs retain their scopes.
[StoppedResidual](../GameTheoryExtensions/Analysis/Protocol/StoppedResidual.lean)
proves that the difference of two actual stopped continuation values equals
the source expectation of the accumulated signed target Bellman residual.
The start is any legal history; the payoff and horizon are bounded, and no
finite-history or finite-Nature assumption is needed. The existing potential
comparison for arbitrary well-founded protocols retains its scope.

Concrete unequal-order incentive and conditional signed-cancellation consumers
are under development. These generic theorems alone are not evidence that
either stronger consumer has been checked.
