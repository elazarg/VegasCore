# Constructive SE interfaces

This ledger records the checked scope of the
[constructive directions](se-preservation-constructive-directions.md).
These additions leave GameTheory, runtime semantics, the preservation target,
and its checklist unchanged. Supporting results do not close target boxes.
The [follow-up experiments](se-constructive-followup.md) track completeness,
actual finite representations, conditional certificates, and production ports
on dedicated branches, including documented rejection decisions.

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
The public exact-assessment certificate theorem chooses its own canonical
positive vanishing sequence; callers supply only the certificate constraints.
The explicit leading-assessment theorem also accepts any such common sequence.

[PowerNormalizerPaths](../GameTheoryExtensionsTests/PowerNormalizerPaths.lean)
checks two actual histories in the same information fiber with reaches
`t/(1+2t)` and `t/((1+2t)(1+t+t²))`. Their ratio is not the coefficient ratio
at any positive parameter, but the general evaluator theorem proves its
correct limit. Thus this regression exercises the noncancelling denominators.

The assumptions are finite players, finite local choice sets, finite decision
information fibers, the existing decision-information antichain, positive
coefficients, natural orders, local constant-term equations, and the checked
fiber constraints. Global finiteness of the history carrier is unnecessary.
Completeness, extraction of certificates from arbitrary consistency sequences,
and preservation of a particular runtime mixture/coupling family are separate.

[UnequalPowerEquilibrium](../GameTheoryExtensionsTests/UnequalPowerEquilibrium.lean)
instantiates the certificate for an actual finite game with sender weights
`(1,t,2t,4t²)`. Its exact off-path pair beliefs are `(1/3,2/3)`, `(1,0)`,
and `(0,1)`. The sender strictly prefers its main action, and the observer's
three prescribed guesses are strictly optimal against every other pure legal
choice. The sequential-rationality theorem handles every whole-policy
deviation, and consistency supplies the **same exact complete assessment**.
The actual initialized terminal runner has joint readout/realized utility law
`pure(done 0 none, 1, 0)`. This is a nonzero-payoff SE witness, not a claim
that power soundness alone implies rationality or runtime preservation.

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
It also checks one symbolic certificate for a disjoint pair of different
hidden kernels: two columns in eight states, valid for **every** pair of real
mixing parameters in `[0,1]`. The adaptive joint-law equality is therefore
uniform along arbitrary parameter sequences. The column-certificate adapter
derives full-space closure and initial moment agreement from checks on the
supplied columns, reusing the shared moment-span theorem.
Six Python checks include direct reconstruction of matrix identities,
dependent and zero seeds, rational transitions, and a distinguishing trace
for an unclosed terminal observable.

This pilot has a finite, fixed all-action interface. It does not compile a
Vegas runtime or transport a dependent legal-action menu. It does not prove
the general tensor/cross-product conditional certificate, parameter-uniform
runtime certificates, or SE preservation from observable closure alone.

The bounded Vegas candidate was
[SequentialPhaseService](../Vegas/Examples/SequentialPhaseService.lean).
Its phase-history finiteness instance is proof-level; an executable rational
labelled representation is not provided. Connecting one would require checked
legal-menu normalization, actual private observation filters, symbolic policy
coefficients, and joint terminal readout/payoff indicators. Moreover this
candidate has only one callback, so it would not exercise recursive adaptive
closure beyond a static choice. No unused Vegas representation adapter was
installed: the finite policy-system pilots provide the checked closure evidence.
No computed Vegas closure dimension or compression result is claimed.

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

[The concrete cancellation game](../GameTheoryExtensionsTests/StoppedResidual.lean)
has Nature reveal a context before the focal player chooses. An opponent's
two later randomized decisions add and subtract a unit reward. Both actual
fully mixed Bayes assessment families converge to one complete limiting
assessment. At each genuine conditional decision, for every focal whole-policy
deviation and every common sequence index, the signed accumulated residual is
zero while the expected absolute charge is `1/(2*(n+2)) > 0`. The actual Bayes
continuation contexts therefore have equal deviation gains. The focal reward
depends on the observed context and chosen action, and the two nonzero local
residuals are retained until their cancellation is proved.

The canonical profile-update theorem covers every focal behavioral policy;
later moves belong to the opponent. The proof reuses the existing theorem
deriving tree-shaped histories from unique predecessors to obtain singleton fibers
and full assessment convergence. It does not assume a conditional prior or
only compare initialization. This is a strict conditional gain refinement;
it does not claim sequential rationality or equality of selected joint laws.

## Validation and remaining scope

The production roots have exact standard-axiom guards in Paper. Test-library
roots are audited separately, respecting the library import boundaries.
Normal compilation covers the generic owners, concrete consumers, and existing
preservation capstones. Source policy, centralized options, module boundaries,
documentation references, whitespace, and all 111 Python tests are checked.
The full default build passes all 5,962 jobs, including the existing concurrent,
recovery and sequential-phase preservation capstones. Thirty-seven selected
production and fixture roots use only the standard axioms; fifteen production
roots have permanent exact guards in Paper. The pre-existing recursion
diagnostic in optional metadata for symbol frequencies replays without a
kernel/build failure.

Physical source cost is a net 1,117 lines across ten library owners, 2,095 lines
in four concrete test modules, 90 lines of Paper guards, and 222 lines of exact
search tooling and Python tests. These counts include the adapters and fixtures,
not just the small abstract certificate statements.

The additions provide reusable constructions and stronger checked examples;
they are not a net proof-compression result. General power completeness and
integer extraction, a Vegas labelled-representation compiler, conditional
tensor/cross-product certificates with unequal observation masses, and
gain-only SE preservation remain open. The existing coupling along a common
sequence and selected-law arguments remain necessary in runtime preservation.
