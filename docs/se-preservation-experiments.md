# Evaluating preservation proof interfaces

The [research survey](se-preservation-research-survey.md) proposes interfaces
whose value depends on actual game and runtime adapters. An experiment is
accepted only after strict Lean checking, standard-axiom review, and comparison
with the existing implementation. A stronger estimate and a shorter proof are
separate benefits. GameTheory remains unchanged; extensions belong locally.

This ledger does not change the [SE target](se-async-checklist.md), its boxes,
runtime semantics, or the quantifiers of existing preservation results.

| Proposal | Experiment and acceptance criterion | Disposition |
| --- | --- | --- |
| Signed observable transport | Reuse real expectations; compare selected observables without asserting equality of laws | Integration boundary checked; guarded interface retained |
| Continuation-gain equivalence | Produce a gain comparison with explicit integration and deviation scope | Conditional context and closed-span results accepted |
| Sufficient information | Test what local sufficiency supplies and identify the additional joint-law and strategy quantifiers | Policy-quantifier boundaries and static public-signal extension accepted |
| Coarsening at random | Derive posterior transport from an actual observation channel | Likelihood producer accepted; runtime fibers remain a client obligation |
| Stopped potentials | Prove the arbitrary-carrier stopped estimate and recover the uniform-depth theorem without stronger premises | In progress |
| Quantitative abstraction | Supply a runtime producer of state-dependent charges and assess conditional uniformity | In progress |
| Affine debt and error transport | Compare a potential implementation with the existing recurrence, charging all adapter costs | In progress |
| Scheduler noninterference | Reuse the stopped relational theorem while retaining observable metadata | In progress |
| Adapted information | Check a decision-timing boundary and assess the cost of a player-specific abstraction | Boundary accepted; general filtration interface deferred |
| Power-sequence certificates | Connect shared behavioral rates to actual Bayes consistency; separate soundness from completeness | Concrete normalized-power completion accepted; general characterization not added |
| Finite obstruction certificates | Check a finite obstruction with game meaning and a consistent alternative assessment | Shared-choice obstruction and same-profile SE accepted |
| Forward-path coherence | Check the acyclic parallel-path boundary for cycle-only criteria | Boundary accepted; no cycle-only runtime criterion |
| External package reuse | Inspect package ownership and dependencies before importing or extracting machinery | Finite signed prototype checked; dependency not adopted |

Accepted declarations, concrete consumers, measured costs, and reasons to retain
an existing proof are recorded here as each experiment is checked. Boundary
examples refute only their stated criterion, not SE preservation.

## Gain comparisons and sufficient observables

[KernelPosteriorGain](../GameTheoryExtensions/Math/Probability/KernelPosteriorGain.lean)
constructs a posterior from a prior and an actual observation kernel using the
existing `fiberPosterior`. A positive observation mass gives the likelihood
density, transfers absolute integrability, and expresses a gain change as its
likelihood covariance divided by that mass. A second estimate includes the
likelihood-weighted difference between source and target continuation gains.
It does not assume that the continuation kernels already agree.

Constant likelihood on the prior support is equivalent to preserving the full
posterior. Nonpositive likelihood covariance can instead preserve a
nonpositive gain while changing the posterior. These are different sufficient
conditions. The denominator remains explicit; small unconditioned errors are
not treated as uniform conditional errors.

[ObservableGainTransport](../GameTheoryExtensions/Analysis/Protocol/ObservableGainTransport.lean)
uses that producer in the existing `Context.ofBelief` and local-optimality
predicate. Every allowed alternative is compared as one choice across the
hidden-state expectation. If choices are whole policies, their information
restrictions and branch interpretation must be supplied by the client. The
theorem does not choose a different alternative at each hidden history.
It constructs neither consistent assessments nor an initialized joint law.

[ObservableMoments](../GameTheoryExtensions/Math/Probability/ObservableMoments.lean)
transports finite represented payoff spans, with both exact and coefficient
weighted error estimates. Source and target hidden carriers may differ.
Propagation through actual continuation kernels requires a common closure
matrix for both bases. The arbitrary-carrier one-step theorem states the
integration guards; the every-horizon theorem uses globally bounded bases.

[ObservableGainBoundaries](../GameTheoryExtensionsTests/ObservableGainBoundaries.lean)
checks changed posteriors with matching nonconstant gains, actual conditional
optimality, a policy-dependent channel that defeats an honest-only condition,
sharp covariance and changed-continuation bounds, rare-observation amplification,
failure of terminal-moment closure, and distinct kernels preserving a genuinely
closed gain basis at every horizon. These are additions, not proof compression.

[PublicRandomization](../GameTheoryExtensions/Analysis/PublicRandomization.lean)
gives a separate static result: ignoring an independent public signal preserves
and reflects Nash at the embedded mixed profile, for arbitrary preferences.
Every contingent randomized unilateral alternative has exactly the source
outcome law of its averaged mixed action. The
[two-player example](../GameTheoryExtensionsTests/PublicRandomization.lean)
preserves a nontrivial source Nash profile and its full declared outcome law,
while duplicated public information conditioned on a constant compression
admits no product factorization. That factorization is not necessary for this
forward static implementation. A general dynamic USI/MSI or SE compression
interface is not installed: it would still need the policy, common-sequence
and selected joint-law adapters stated in the survey.

## Consistency and finite certificates

[BeliefMonomial](../GameTheoryExtensions/Analysis/Protocol/BeliefMonomial.lean)
proves that a balanced finite product identity between actual history reach
probabilities is necessary for consistency. Matching information sites cancel
the Bayes normalizers, and one common fully mixed sequence passes the identity
to the limiting beliefs. This constrains all consistency sequences, without
assuming they are power sequences.

[CyclicBeliefs](../GameTheoryExtensionsTests/CyclicBeliefs.lean) supplies the
game meaning: fixed Nature chooses a pair, a sender uses one shared four-choice
information set, and the observer sees the pair but not the sender's choice.
The observer also has four legal choices. A real reach-product identity rules
out strict cyclic posterior rankings, including concentrated cyclic supports.
Actual own-play occurrence counts produce the corresponding three impossible
exponent inequalities. Mathlib's checked arithmetic closes their contradiction;
no second rational LP solver is introduced for this certificate.

[CyclicBeliefsCompletion](../GameTheoryExtensionsTests/CyclicBeliefsCompletion.lean)
constructs a consistent SE with exactly the entire prescribed main strategy
profile and equal pair-belief probabilities. One common Bayes sequence uses
positive uniform trembles. With a positive base tending to zero, the main and
rare weights have fixed coefficients one and normalized powers zero and one;
the coordinate identities cover both players' non-idle information states,
including unreachable coordinates, and idle menus are singleton. Nature stays
fixed. Thus the proposed cyclic beliefs fail even though the same prescribed
play admits a consistent equilibrium. All utilities in this fixture are zero.

A general compiler from finite games to exponent systems, leading-coefficient
solver, integer-exponent characterization and completeness theorem are not
added. The checked positive construction and universal obstruction exercise
the semantic obligations directly; an arithmetic-only formatter would not
replace them or simplify the current component-based completion proof.

## Observable and information boundaries

[SignedKernelPullback](../GameTheoryExtensionsTests/SignedKernelPullback.lean)
proves that expectation on unrestricted real functions is not monotone for
any fully supported PMF on the naturals, and instantiates the result with a
geometric distribution. The larger function is pointwise above one but has
divergent weighted sum. The totalized real expectation is zero there. This
does not affect guarded expectation comparisons; it shows why replacing them
with an unguarded ordered transport would be unsound.

[InformationTiming](../GameTheoryExtensionsTests/InformationTiming.lean)
defines two actual one-player game forms. Hidden policies are arbitrary PMFs
on a guess; revealed policies are arbitrary kernels from the observed bit to
a guess. Every hidden policy has value one half, while a revealed policy
achieves one and no revealed policy exceeds one. Both forms have exactly the
same exogenous bit marginal for every policy. Preserving this process law
therefore supplies no decision-value guarantee without information transport.
A general filtration framework would additionally need legal policy transport,
unilateral compatibility and a consistency construction; this example is not
such a framework or an obstruction to the fixed SE target.

[ForwardPathCoherence](../GameTheoryExtensionsTests/ForwardPathCoherence.lean)
uses Mathlib's quiver paths. Its height equation proves every closed path is
empty. Closed-path maps are identity, yet two parallel forward edges act by
identity and translation, so no compatible family exists. A cycle-only
coherence test is rejected; the existing runtime proofs retain actual
forward-step comparisons.

## External transport interface

An isolated source prototype checks the pinned Multitubes `EdgeGraph`,
`WalkLabel`, `Basic` and `Morphism` modules under the central VegasCore options,
together with a signed finite-carrier kernel pullback using the existing
GameTheory expectation. Its monotonicity and lax-section walk bound check.
The four external modules total 2,173 source lines; the signed adapter adds
34 lines. This is a source experiment, not a build of either complete external
package or a change to their dependency pins.

The prototype demonstrates that the algebra can express the comparison. It
does not remove the actual stopped-runner, invariant-region, integration or
conditional-information adapters. Its finite observable carrier also does
not replace the arbitrary-carrier potential theorem. For unrestricted real
functions the checked integration boundary above applies; restricted fibers
would require their own closure proofs. The direct guarded probability proof
is retained, and no duplicate graph or probability semantics is installed.

The [pinned Multitubes configuration](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/lakefile.toml)
selects Lean/Mathlib 4.35.0, while the
[pinned UniformEquilibrium configuration](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/lakefile.lean)
selects its own GameTheory package and external maths dependency. The survey's
package-resolution obligations remain applicable. Importing either package
wholesale offers no demonstrated reduction for these consumers.
