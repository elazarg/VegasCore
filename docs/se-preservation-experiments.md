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
| Stopped potentials | Prove the arbitrary-carrier stopped estimate and recover the uniform-depth theorem without stronger premises | Comparison and automatic charge producer accepted |
| Quantitative abstraction | Supply a runtime producer of state-dependent charges and assess conditional uniformity | Conditional response-count and weighted-retention estimates accepted |
| Affine debt and error transport | Compare a potential implementation with the existing recurrence, charging all adapter costs | Actual stopped-runner recurrence accepted; quitting-game debt interface retained separately |
| Scheduler noninterference | Reuse the stopped relational theorem while retaining observable metadata | Existing concrete paired-step consumers retained |
| Adapted information | Check a decision-timing boundary and assess the cost of a player-specific abstraction | Boundary accepted; general filtration interface deferred |
| Power-sequence certificates | Connect shared behavioral rates to actual Bayes consistency; separate soundness from completeness | Concrete normalized-power completion accepted; general characterization not added |
| Finite obstruction certificates | Check a finite obstruction with game meaning and a consistent alternative assessment | Shared-choice obstruction and same-profile SE accepted |
| Forward-path coherence | Check the acyclic parallel-path boundary for cycle-only criteria | Boundary accepted; no cycle-only runtime criterion |
| External package reuse | Inspect package ownership and dependencies before importing or extracting machinery | Finite signed prototype checked; dependency not adopted |

Accepted declarations, concrete consumers, measured costs, and reasons to retain
an existing proof are recorded here as each experiment is checked. Boundary
examples refute only their stated criterion, not SE preservation.

## Stopped errors and actual runtime consumers

[StoppedContinuationComparison](../GameTheoryExtensions/Analysis/Protocol/StoppedContinuationComparison.lean)
bounds a stopped expectation difference by a nonnegative potential satisfying
the local comparison and expected-drift inequalities. Only reference steps
must preserve the region; the target may leave it. Integration is explicit,
and neither the history carrier nor the potential must be finite or globally
bounded. The uniform step-TV/decreasing-depth result follows with exactly its
original assumptions. The interval-payoff version charges the interval width
times step-TV, avoiding an unnecessary factor two for event indicators.

[StoppedCharge](../GameTheoryExtensions/Analysis/Protocol/StoppedCharge.lean)
constructs a potential rather than requiring the client to guess one. It sums
bounded nonnegative charges over actual prefix histories and subtracts the
current cumulative charge from its conditional stopped expectation. A bounded
horizon supplies integrability; the potential has exact one-step drift. It
uses the existing stopped runner, without finite-Nature or finite-history
assumptions. The
[merging-history fixture](../GameTheoryExtensionsTests/StoppedCharge.lean)
has two reachable histories at the same current state with future charges one
quarter and three quarters. An endpoint-state-only fold cannot express that
charge. This justifies the prefix-history carrier.

The actual runtime producers are
[ReactiveDecisionBudget](../Interaction/ReactiveDecisionBudget.lean) and
[ReactiveResponseCount](../Interaction/ReactiveResponseCount.lean). Each player
callback, including silence, increments the physical response count by one.
Initialization, environment and Nature steps increment it by zero. The
recorded count plus remaining response budget is at most the scheduler horizon.
An exact identity with the generic cumulative charge supplies the stopped
drift and integrability proofs, while the runtime retains its sharper
remaining-response bounds.

Write \(B\) for the payoff absolute bound, \(r\in[0,1]\) for retained honest
choice mass, and \(A(h)\) for the expected actual honest responses before the
chosen stop, conditional on the entire current history \(h\). The concrete
[stopped comparison](../Vegas/Game/StoppedHonestResponseCount.lean) proves

\[
 \operatorname{TV}(P_{\mathrm{honest}},P_{\mathrm{target}})
 \le (1-r)A(h),\qquad
 |\mathbb E_{\mathrm{honest}}u-\mathbb E_{\mathrm{target}}u|
 \le 2B(1-r)A(h).
\]

This compares complete stopped history laws at every starting history under
the stated reference-support retention condition. It is not a root-weighted
regret estimate. Padding steps themselves cost zero; changing a scheduler may
still change future response opportunities and therefore the expectation.

[StoppedHonestWeightedComparison](../Vegas/Game/StoppedHonestWeightedComparison.lean)
allows genuinely history-dependent retention. Its second producer constructs
legal target policies as mixtures with rates depending on each player's
actual information. The rate at an active history is read from that actor's
information; inactive steps have zero charge. The automatic potential pays
the actual varying losses. The runtime supplies its own bounded horizon,
rather than asking for another horizon premise. This addition does not by
itself construct a uniform vanishing SE error for an arbitrary rate family.

For uniform retention, the native initialized bound is

\[
 \min(|\mathrm{Player}|,1)\,H(1-r)
\]

for scheduler horizon \(H\), in place of
\(|\mathrm{Player}|(2H+1)(1-r)\). It improves to \(H(1-r)\) when players are
present and retains exact zero for an empty player type. The
[terminal/readout adapter](../Vegas/Game/OnePacketHonestTerminalApproximation.lean)
maps the bound to the actual joint typed readout and original
parameter-dependent exclusion payoff, using the exact honest readout law.
The initialized recovery and phase consumers use this estimate in their
existing clearance and common-assessment limit arguments.

The retained-honest payoff-error multiplier loses the ambient player count in
25 concrete source-value and gain modules. Those comparisons retain their
information-site, deviation and common-sequence quantifiers. The preservation
statements, physical service premises, consistency construction, funding
conditions and selected joint-law conclusions are unchanged. Other physical,
cubic, observation, decorrelation and enforcement errors remain separate.

The [repeated-activation fixture](../VegasTests/RepeatedActivation.lean) has
two legal silent callbacks while its single source event is unfinished.
Thus source-event count is not a general engine bound on callbacks. The
fixture does not refute an additional honest-path or service-specific bound,
and is not a counterexample to preservation under the full service contract.

## Preserving generic theorem scope

Tightening both a quantitative callback premise and its resulting estimate
does not, by itself, strengthen the generic implication. The boundary-value
adapters therefore accept arbitrary nonnegative error budgets. The higher
keyed-value callback accepts a nonnegative retention multiplier; concrete
producers use one.

Five isolated Lean probes prove the exact original complete statements from
the generalized APIs with the original player-count budgets. They preserve
all callback domains, physical and clock terms, payoff hypotheses and
conclusions. This includes the higher existential vanishing-error theorem,
whose numerical premise is inside its callback rather than its conclusion.
The concrete service theorems supply the sharper budgets; no compatibility
aliases or duplicate semantic definitions are needed.

## Retained interfaces and rejected replacements

The [paired-step stopped comparison](../GameTheoryExtensions/Analysis/Protocol/StoppedKernelComparison.lean)
already has eight concrete consumers across Interaction and Vegas, including
the sequential phase route. Their actual relations and summary maps remain
the scheduler/noninterference interface. A second abstract relation would
repeat the same kernel, stopping and observation obligations. No clock,
activation, traffic or receipt information is erased by choosing a smaller
comparison graph, and no blanket scheduler noninterference result is claimed.

The quitting-game debt equalities in UniformEquilibrium are not instantiated
as arbitrary-game best-response debts. The accepted exact recurrence is for
actual stopped cumulative charges. A general filtration interface, complete
USI/MSI transport, full power-sequence characterization, new LP solver and
wholesale external package imports do not simplify an identified consumer
enough to justify their additional semantic obligations here. Their proposed
scope remains in the survey. Rejected scaffolds have no production clients or
imports; the checked boundary examples retain the reasons for those decisions.

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
uses that producer in the existing `GameTheory.Protocol.Context.ofBelief` and local-optimality
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
The four external modules total 2,205 source lines; the signed adapter adds
29 lines. This is a source experiment, not a build of either complete external
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

## Cost and verification

Physical Lean-line changes, including comments, imports and theorem statements,
are measured against the checked evaluation baseline:

| Area | Affected files | Net lines |
| --- | ---: | ---: |
| Libraries and actual runtime consumers | 52 | +1,882 |
| Regression and boundary games | 11 | +1,474 |
| Paper imports and axiom guards | 1 | +427 |

This is a mathematical strengthening and reuse result, not a net proof-size
reduction. The three likelihood/context/moment owners contribute 501 library
lines, the independent-public-signal extension 84, and the shared reach-product
lemma 67. The finite consistency game and its preserving power construction
contribute 594 test lines. The generic charge, variable-retention runtime
adapter and merging fixture contribute 492 lines across their layers.

Local reuse still matters: the constant-response consumer is 197 lines with
two factual links to the generic charge, versus 203 with its independent drift
and integration proofs. The terminal/no-stop law is shared with the actual
proposal-recovery continuation consumer; its private duplicate is removed.
The uniform-depth comparison is a specialization of the potential estimate.
These savings are included in the complete costs rather than reported as
global compression.

Acceptance checks cover the ordinary complete build, including the recovery,
sequential-phase and concurrent capstones, 105 tooling tests, strict source policy,
module boundaries, documentation references and whitespace. There are 142
distinct affected or supporting theorem roots with explicit standard-axiom
audits, including the game boundaries. Production guards live in `Paper.lean`;
test-library roots are audited in isolated modules, preserving the prohibition
on audit imports from game-theory tests. Five exact full-statement scope probes
check the generalized callback interfaces separately.

The non-strict dependency diagnostic reports 52 of 1,955 modules with
declarations unreached from Paper, tests and examples, totaling 5,370 lines.
The unreached module count matches the evaluation baseline. This report is
separate from default-build coverage; no zero-unreached claim is made.

The full build replays the pre-existing optional symbol-frequency metadata
recursion diagnostic for `Vegas.Examples.CommitTimingInformationAudit`. Proof
checking and the axiom guards pass; the central Lean options are unchanged.
GameTheory's source and gitlink, the fixed SE target and checklist, existing
language and runtime semantics, and preservation funding/service hypotheses
remain unchanged.
