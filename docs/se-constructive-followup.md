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
| Finite-game power completeness | `research/power-completeness` | Extract a certificate for the same assessment from an actual consistency sequence, including real coefficients and integer exponents | Accepted: exact-assessment extraction; ambient information finiteness removed |
| Actual Vegas finite representation | `research/vegas-observable-representation` | Check actual transitions, private views, legal policies and joint payoff/readout observables; measure closure and total adapter cost | Compiled compression rejected for production adoption; reachable native handle obstruction checked |
| Conditional observable certificates | `research/conditional-observable-certificates` | Derive actual conditional expectations from tensor certificates with unequal positive observation masses, every adaptive policy and a common parameter family | Accepted: actual adaptive posterior transport and unequal-mass incentive family checked |
| Production preservation consumers | `research/production-preservation-consumers` | Improve an actual Vegas conditional-gain proof while retaining all deviations, the common assessment sequence and selected joint law | Accepted: completion stopping, finite-history whole-policy zero gain and strict callback-budget regression |

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

## Power completeness with finite actual histories

[PowerCompleteness](../GameTheoryExtensions/Analysis/Protocol/PowerCompleteness.lean)
extracts positive real coefficients, natural exponents and reference histories
for the **same** supplied assessment from its actual sequential consistency.
Its assumptions are finite players, finite local choices at every information
coordinate (including unused ones), finite actual histories and the supplied
decision-information antichain used by the existing consistency predicate. This is noncomputable existence extraction, rather than
an executable game-to-constraint compiler. Ambient information carriers may be
infinite. Every logarithmic constraint is derived from the actual common Bayes sequence; none is an extra
hypothesis. Positive prescribed action masses get exponent zero and their
prescribed coefficient. Zero prescribed action masses get positive integer
orders. Every positive/zero belief history satisfies the soundness certificate's
exact coefficient ratio and equal/higher order conditions.

[FiniteTraceCoordinates](../GameTheoryExtensions/Analysis/Protocol/FiniteTraceCoordinates.lean)
constructs the finite cover from the coordinates actually drawn along legal
histories, including inactive draws and repeated occurrences. Matrix extraction
uses this cover; coefficients and orders extend to every strategy coordinate.
Fixed-cover order, coefficient-log and actual-reach identities require no
finite-history assumption. [LogReach](../GameTheoryExtensions/Analysis/Protocol/LogReach.lean)
uses the universal cover when the global coordinate carrier is finite,
retaining that broader scope without a second trace-induction proof stack.
[UnboundedTracePowers](../GameTheoryExtensionsTests/UnboundedTracePowers.lean)
proves an actual history carrier infinite and exercises all six global
formulas at arbitrary finite depths; it asserts no SE for its repeated
information state. Full support and prescribed convergence at unused
coordinates do not change any actual evaluator weight or Bayesian belief. Actual Bayes log-ratio limits,
the real affine-ray theorem and rational homogeneous direction extraction
supply the certificate. No new analytic axiom is needed.

The [nonzero-payoff client](../GameTheoryExtensionsTests/PowerExtraction.lean)
supplies only its checked game consistency, without rates or affine constraints.
Interpreting its automatically extracted certificate with the existing power
soundness machinery yields exactly the original full assessment, including its
prescribed strategy and all beliefs.
[InfiniteInformationPowers](../GameTheoryExtensionsTests/InfiniteInformationPowers.lean)
has provably infinite natural-number information states and finite actual
histories, and extracts the exact assessment's certificate. This is a generic
finite-game construction; a production Vegas instantiation still needs the
particular model's finite-history and finite-menu adapters.

## Actual Vegas observable representation

The compiled two-decision payment experiment checks ten actual Config states,
all legal binding/disclosure outcomes, genuine private observations, both policy
representation directions, arbitrary schedulers, and publication/payment/utility
read out together. Its stopped observation/action orbit space has exact dimension
seven, independently checked in Lean. All four live callback states remain
distinct. The three saved dimensions concern terminal failure histories only.

Production adoption is rejected: 568 lines of representation and certificate
adapters buy no live decision compression and do not discharge native recall or
handle transport. The checked source, exact search and detailed rejection are
retained on the [dedicated experiment branch](https://github.com/elazarg/VegasCore/blob/research/vegas-observable-representation/docs/experiments/program-payments-observable-representation.md).
The seven-dimensional compiled result is not a native-runtime dimension claim.
The retained snapshot is 5ac0fa04: 1,047 Lean lines including the independently
useful 479-line native prefix owner. Only the 568 compiled adapter lines are
excluded from production integration.

[ProgramPaymentsNativeRepresentation](../Vegas/Examples/ProgramPaymentsNativeRepresentation.lean)
proves a useful operational boundary independently: two genuine initialized raw
roster histories reach second callbacks with the same source Config but different
accepted handles and private observations. The same admitted raw opening succeeds
in one and is rejected in the other. Thus no literal Config-only observation or
raw-action factorization works even on these reachable callbacks. Richer finite
encodings or coherent handle/action renamings remain possible. This example also
supplies the actual completed prefix used by the production stopping regression.
No unused native matrix framework is installed.

## Conditional observables with unequal observation masses

[PrivateTranscriptWeights](../GameTheoryExtensions/Analysis/PrivateTranscriptWeights.lean)
factors the actual adaptive runner's selected transcript moment into the real
policy's response weights and its unnormalized observation-filtered kernel word.
The factor uses each actual remembered past. Positive transcript support proves
both factors positive, and the actual fiber-posterior expectation is the
normalized word moment. No likelihood-factorization hypothesis or alternative
runner is assumed. Hidden states are finite; input and output types need not be.

[ConditionalObservableTensor](../GameTheoryExtensions/Analysis/ConditionalObservableTensor.lean)
uses independent source/target kernels to compute the cross-product of their
conditional numerators and masses. A closed finite spanning certificate kills
this signed cross-product. Consequently the actual conditional expectations
agree for every common complete input/output transcript supported in both
systems, including under separately chosen adaptive policies. Observation
probabilities may differ. Closure and initial moments are checked under all
labels, rather than sampled policy coefficients.

The [concrete incentive client](../GameTheoryExtensionsTests/ConditionalObservableTensor.lean)
checks a three-column certificate throughout a common parameter family. The
actual transcript masses are 1/[2(n+2)] and 1/[4(n+2)]: positive, unequal and
vanishing. Both actual posteriors give values 3/4 for retaining the hidden reward
and 1/4 for flipping it at every index. The same symbolic closure proof handles
all priors, labels and adaptive policies. See the
[conditional-certificate explanation](conditional-observable-certificates.md).

This is a selected conditional-expectation result. It does not identify full
hidden laws, establish native policy legality, produce a common SE assessment,
or replace the initialized joint-law obligations of preservation.

## Payoff-aligned production stopping

[SourceTerminalReadout](../Vegas/Game/SourceTerminalReadout.lean) proves that the
actual source Config and typed source readout freeze after source completion,
under every legal continuation profile. The complete terminal readout law equals
the law stopped at that actual completion time.
[SourceTerminalComparison](../Vegas/Game/SourceTerminalComparison.lean) uses
existing honest-response occupation machinery to charge responses only until
source completion, for arbitrary starting histories and dominated profiles.
It preserves the same joint typed readout and original exclusion-payoff vector,
and gives bounded-readout payoff estimates. The original initialized one-packet
bound is derived from this stronger producer with its exact statement retained,
including the empty-player case. Its assessment sequence, service premises and
selected law are unchanged.

[SourceTerminalIndifference](../Vegas/Game/SourceTerminalIndifference.lean)
derives completion on every history in the actual information fiber from the
public completion view. All continuation profiles then have identical original
readout payoff at each hidden history. The signed continuation residual is zero for every continuation profile.
With finite actual histories, the whole-policy conditional gain is zero for
every belief and every deviation.
This equality is used before any absolute-value estimate. No audit-charge,
receipt or complete-history equivalence is asserted.

[SourceTerminalCallbacks](../VegasTests/SourceTerminalCallbacks.lean) constructs
a genuine source-initialized bounded-raw commit/reveal history and a subsequent
callback. At that callback the completion-stopped response budget is zero while
the full-horizon budget is at least one for **every** continuation profile. The
scheduler mixture used to exhibit this prefix has no claimed physical-service
certificate; the general bound uses the existing original service assumptions.

See the [production scope and rejection rationale](payoff-aligned-source-completion.md).

A generic opposite-sign cancellation improvement is not accepted: arbitrary
payoffs and foreign failures supply no sign relation between distinct live
residuals. Freezing the source readout also does not freeze audited monetary
charges. The useful exact cancellation is the proved completed-source equality;
additional live cancellation needs a separately justified payoff relation.

## Verification and remaining scope

The full default build passes all 5,982 jobs, including the original preservation
capstones and every test aggregator. The 111 Python tests pass, as do the strict
source-policy, module-boundary and documentation-reference checks. Sixteen new
permanent Paper guards pass. A final fifteen-root audit of the generic covers,
exact assessment interpretation, both infinity regressions, conditional payoff
family and native callback witnesses uses only the standard axioms. All six
global trace-algebra theorem headers are retained exactly; their proofs share
the stronger fixed-cover machinery. The maintained manuscript's 32 annotated
mathematical results remain pinned, with no import exceptions.

The build replays the existing optional SymbolFrequency metadata diagnostic;
it exits successfully and all kernel proof checks pass. No new Lean options or
dependencies are used. GameTheory remains unchanged at
8bb3fc270f716b07686f429ee0714e7ee4ea614e. Language, runtime, payoff and funding
semantics, service hypotheses, and the fixed SE target/checklist are unchanged.

These additions supply stronger reusable constructions and actual consumers;
they expand the library and fixtures overall. No net proof-compression claim
is made. Executable power-certificate compilation, a useful richer native
finite quotient, and general gain-only SE preservation remain separate work.
The compiled prototype and unsupported generic live-cancellation refinement
have explicit rejection rationales; neither is presented as an accepted
preservation theorem.
