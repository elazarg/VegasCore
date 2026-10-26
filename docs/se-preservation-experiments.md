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
| Continuation-gain equivalence | Produce the existing gain-comparison premise with explicit integration and deviation scope | In progress |
| Sufficient information | Test what local sufficiency supplies and identify the additional joint-law and strategy quantifiers | In progress |
| Coarsening at random | Derive an existing Bayes comparison from likelihoods on actual fibers | In progress |
| Stopped potentials | Prove the arbitrary-carrier stopped estimate and recover the uniform-depth theorem without stronger premises | In progress |
| Quantitative abstraction | Supply a runtime producer of state-dependent charges and assess conditional uniformity | In progress |
| Affine debt and error transport | Compare a potential implementation with the existing recurrence, charging all adapter costs | In progress |
| Scheduler noninterference | Reuse the stopped relational theorem while retaining observable metadata | In progress |
| Adapted information | Check a decision-timing boundary and assess the cost of a player-specific abstraction | Boundary accepted; general filtration interface deferred |
| Power-sequence certificates | Connect shared behavioral rates to actual Bayes consistency; separate soundness from completeness | In progress |
| Finite obstruction certificates | Check a finite obstruction with game meaning and a consistent alternative assessment | In progress |
| Forward-path coherence | Check the acyclic parallel-path boundary for cycle-only criteria | Boundary accepted; no cycle-only runtime criterion |
| External package reuse | Inspect package ownership and dependencies before importing or extracting machinery | Finite signed prototype checked; dependency not adopted |

Accepted declarations, concrete consumers, measured costs, and reasons to retain
an existing proof are recorded here as each experiment is checked. Boundary
examples refute only their stated criterion, not SE preservation.

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
