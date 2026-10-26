# Constructive routes to stronger SE-preservation interfaces

The [experiment ledger](se-preservation-experiments.md) establishes useful
interfaces and rejects several proposed replacements. It does not exhaust the
mathematical opportunities. In particular, checking a hand-built witness is
different from producing witnesses for a class of games, and declining a
production dependency does not settle the value of its underlying theory.

The [implementation ledger](se-preservation-constructive-experiments.md) records
which parts have checked Lean implementations and their precise scope.
The strongest targets are a general power-certificate interpretation,
construction of closed observable spaces, and signed continuation-error
identities. The statements and derivations below describe the mathematical
targets; the linked ledger distinguishes checked additions from open proposals.
None changes the SE target. They use the existing
probability and game semantics. None requires adopting an external package.

## Power certificates: separate the linear algebra from the game

The relevant intermediate result is more specific than “implement the full
power-sequence characterization.” Reny's Theorem 2.1 says that a finite linear
system with finite and infinite limiting right-hand sides admits an affine-ray
approximation whenever it admits any approximating sequence. His Theorem 2.3
applies this to consistency and obtains positive integer exponents.
[Reny, 2026](https://doi.org/10.1007/s00182-026-00997-z).

An equivalent useful formulation of the linear-algebra target is:

\[
 Ey_n\longrightarrow b,\qquad (Gy_n)_j\longrightarrow+\infty\quad\forall j
 \quad\Longrightarrow\quad
 \exists x,z:\ Ex=b,\ Ez=0,\ Gz>0.
\]

All matrices and vectors here are finite-dimensional over the reals. Then
\(x+t z\), as \(t\to+\infty\), has the same specified finite and infinite
limits. Negative infinite limits can be handled by negating their rows.
The finite equations concern the intercept; the homogeneous strict constraints
concern the direction. This is an attractive Multitubes theory result in its
own right, using finite alternatives and closedness of finite-dimensional
linear images. It needs neither game semantics nor a new LP solver.
The real statement is checked locally in
[AffineRay](../GameTheoryExtensions/Math/AffineRay.lean), using a continuous
right inverse on the closed image. Integer extraction remains separate.

The game interpretation can be split into independently useful results.

### A certificate whose soundness does not require completeness

Fix a finite extensive game with fixed Nature probabilities and a prescribed
behavioral strategy \(\sigma\). Use one coordinate for each zero-probability
behavioral action, shared at every occurrence of that information/action pair.
For a Nature-compatible history \(h\), let \(m_h\) be its vector of occurrence
counts for these coordinates. Let \(d_h>0\) be the product of its Nature
probabilities and its positive prescribed action probabilities, with their
actual multiplicities. Histories made impossible by Nature are excluded.

Given \(c_a>0\) and \(k_a\in\mathbb N_{>0}\), assign unnormalized action weights

\[
 q_a(t)=
 \begin{cases}
 \sigma_a,&\sigma_a>0,\\
 c_a t^{k_a},&\sigma_a=0,
 \end{cases}
 \qquad
 \sigma_a(t)=\frac{q_a(t)}{\sum_{b\in A(I_a)}q_b(t)},\quad t>0.
\]

Each local denominator tends to one, so all coordinates converge to the
prescribed strategy, including coordinates at information sets that are
unreachable under that strategy. Actual finite history reach weights satisfy

\[
 R_h(t)=C_h(c)t^{m_h\cdot k}(1+o(1)),\qquad
 C_h(c)=d_h\prod_a c_a^{m_{h,a}}>0.
\]

This expansion must be proved for the existing history evaluator. Local
normalizers need not cancel exactly across histories; their convergence to one
is sufficient. It is not enough to assign a monomial to an abstract graph.
The trace-product induction in
[BeliefTransport](../GameTheory/GameTheory/Analysis/Protocol/BeliefTransport.lean)
is an existing starting point; the missing addition records shared occurrence
counts and leading coefficients rather than introducing another reach law.

For each information set \(I\), choose a reference history \(h_I\) with
prescribed belief \(\mu_I(h_I)>0\). A sound certificate consists of:

\[
 (m_h-m_{h_I})\cdot k=
 \begin{cases}
 0,&\mu_I(h)>0,\\
 \text{a strictly positive number},&\mu_I(h)=0,
 \end{cases}
\]

and, for every history with positive prescribed belief,

\[
 \frac{C_h(c)}{C_{h_I}(c)}=\frac{\mu_I(h)}{\mu_I(h_I)}.
\]

The proof divides all reach weights in a fiber by the reference leading power.
The higher-order terms disappear; the coefficient ratios and normalization
identify the complete limiting belief. Choosing one common positive sequence
\(t_n\to0\) therefore supplies consistency of the prescribed assessment.
This soundness construction is implemented in
[PowerCertificate](../GameTheoryExtensions/Analysis/Protocol/PowerCertificate.lean),
using the actual evaluator factorization and finite-fiber posterior limits.
It preserves the prescribed limiting strategy, not automatically the extra
mixture or coupling identities of an existing runtime approximation family.
A production replacement must retain those premises as well.

The coefficient equations are also structured. With \(x_a=\log c_a\), they are
linear equations

\[
 (m_h-m_{h_I})\cdot x
 =\log\frac{\mu_I(h)}{\mu_I(h_I)}-\log\frac{d_h}{d_{h_I}}.
\]

Thus support feasibility and positive coefficient feasibility are two distinct
finite problems. The former has integer matrix entries and homogeneous strict
constraints; a real solution can be replaced by a rational one in the rational
equality subspace, then scaled to positive integers. The latter has real
logarithmic constants. Rational coefficients \(c_a\) should not be assumed to
cover all feasible inputs. A checker can accept positive real witnesses with
proofs, or exact algebraic witnesses on a suitable restricted input class.

The [balanced reach-product theorem](../GameTheoryExtensions/Analysis/Protocol/BeliefMonomial.lean)
already proves necessary identities for every consistency sequence. It does
not extract the shared history-count matrix or establish necessity of the
whole certificate format. The affine-ray theorem offers a route to that
necessity result once log reach ratios have their game interpretation.
[Dilmé's characterization](https://doi.org/10.1007/s00182-023-00874-z)
supplies the published target; soundness, certificate extraction, and the
integer-exponent step should have separate acceptance criteria.

### A stronger positive witness than zero utilities

A useful test uses the same pair-observation pattern as
[CyclicBeliefs](../GameTheoryExtensionsTests/CyclicBeliefs.lean), with a new
payoff specification. Nature selects one of the pairs \(\{a,b\},\{b,c\},\{c,a\}\)
with fixed positive probabilities.
An uninformed sender chooses a main action or a rare action; an observer moves
only when the rare action lies in the selected pair, observing just that pair.

Take rare weights \((t,2t,4t^2)\), main weight one, and normalize. The limiting
pair beliefs are

\[
 \mu_{ab}=(1/3,2/3),\qquad
 \mu_{bc}=(1,0),\qquad
 \mu_{ca}=(0,1).
\]

Give the sender payoff one for the main action and zero otherwise. Give the
observer payoff one for correctly guessing the rare action and zero otherwise.
The prescribed sender plays the main action; the observer guesses \(b,b,a\)
at the three pair sites. The sender strictly prefers its prescribed action;
each observer choice is strictly best under the stated limiting belief. Fully
mix the observer's own choices as well, converging to these prescriptions.
They do not affect reach to the observer's decision. This describes a
nonzero-payoff sequential equilibrium with unequal tremble orders and genuine
off-path incentive comparisons, rather than relying on zero-utility rationality.

This witness is checked in
[UnequalPowerEquilibrium](../GameTheoryExtensionsTests/UnequalPowerEquilibrium.lean),
a separate payoff-retaining game. It exercises the general certificate,
whole-policy sequential rationality, and the actual initialized joint law.
The existing cyclic-belief fixture is unchanged.

## Observable spaces: construct a certificate instead of assuming closure

[ObservableMoments](../GameTheoryExtensions/Math/Probability/ObservableMoments.lean)
accepts a represented payoff span and a common closure matrix for a fixed pair
of kernels. The next useful result would produce such data for a finite
family of actual continuation operators.

Weighted-automata equivalence is a particularly close precedent. Tzeng gives a
polynomial-time equivalence algorithm. Kiefer's elementary presentation gives
finite forward/backward spaces, equivalence certificates, and distinguishing
words of length at most \(n_s+n_t-1\) for two inequivalent automata. These are
statements about finite weighted languages, not SE preservation.
[Tzeng, 1992](https://doi.org/10.1137/0221017),
[Kiefer, 2020, §§2–3](https://arxiv.org/abs/2009.01217).

Here is a proposed certificate specialized to the existing observable problem.
On the direct sum of finite source and target hidden carriers, form block
diagonal operators \(M_\ell\), one for each matched action/observation label.
Let the columns of \(G\) be paired terminal gains or readout indicators. Close
their span under every operator:

\[
 W_0=\operatorname{span}(G),\qquad
 W_{j+1}=W_j+\sum_\ell M_\ell W_j.
\]

Dimension can increase at most \(n_s+n_t\) times. An external exact-arithmetic
search can return columns \(B\) and matrices \(C_\ell,D\) satisfying

\[
 M_\ell B=BC_\ell,\qquad G=BD.
\]

For initial row vector \(\lambda=(p_s,-p_t)\), also check \(\lambda B=0\).
Induction then gives \(\lambda M_wG=0\) for every finite label word \(w\).
Soundness needs only these matrix identities; proving that the supplied
columns are a minimal basis is optional. For rational input, the arithmetic
certificate can be checked exactly even when the search procedure is untrusted.

This is not a direct invocation of the existing fixed-kernel PMF theorem.
It needs induction over the labelled operator family. An observation-conditioned
operator is generally substochastic; one possible PMF adapter adjoins a
cemetery state and extends the relevant observables by zero. The adapter must
prove the pullback identity and retain an indicator for surviving observation
mass. Its cost belongs in the comparison with the current implementation.

Two qualifications matter for a game adapter:

- Labels must retain the player's actual observable history and legal action
  interface. Use unnormalized observation-conditioned kernels, so branch
  probabilities are retained. Closure for an honest kernel or for blind
  action sequences alone does not cover observation-dependent deviations.
  The adapter must prove that corresponding legal policies use matching
  coefficients on corresponding observation histories, with opponents' fixed
  policies included in the kernels. Extra target choices require a separate
  legal simulation or enforcement argument.
- Gain observables do not identify the initialized joint outcome/payoff law.
  Keep that law's existing proof, or include indicators of the actual finite
  joint readout. A basis for separate marginal readouts is insufficient.
  Finiteness and rational representability must be established for the chosen
  client; this construction is not an arbitrary-carrier replacement.

### Conditional comparisons can use cross-products

Suppose a finite labelled model represents the unnormalized gain numerator
\(N(w)\) and observation mass \(D(w)\) as weighted-automaton series. Where both
observation masses are positive, conditional equality is equivalent to

\[
 N_s(w)D_t(w)-N_t(w)D_s(w)=0.
\]

Weighted series support products by tensor constructions and differences by
direct sums. This suggests checking the displayed identity with a finite
linear certificate. It can avoid requiring equality of every hidden-state
posterior. Matching positive supports is a separate obligation: the
cross-product vanishes trivially when a numerator and its denominator are
both zero. Null observations and off-path limits cannot be ignored.
Tensor products enlarge the representation. Polynomial cost in a compiled
automaton's dimension is not polynomial cost in a succinct Vegas program;
even a finite history unfolding can be exponentially large.

This is a proposed application of automata algebra. The common assessment
sequence, information-local policy interpretation, and actual numerator and
denominator representations remain to be proved. Exact identities at one
perturbation parameter do not imply identities along a common sequence;
parameter-uniform certificates or a symbolic interpretation are needed.

There is also a useful limit on the automation promise. Exact weighted-language
equivalence and one-sided comparison over all words are different problems;
the latter is undecidable in general for probabilistic automata. This does
not obstruct bounded-horizon games, but rules out promising an unrestricted
complete procedure for gain inequalities from the equivalence algorithm alone.
[Kiefer et al., 2011, §1](https://people.mpi-sws.org/~joel/publications/langeqprobaut11.pdf).
Their later treatment also distinguishes expected-reward and reward-distribution
equivalence, matching the distinction between gain and selected-law obligations.
[Kiefer et al., 2013](https://doi.org/10.2168/LMCS-9(1:8)2013).

## Signed continuation residuals can retain cancellation

The accepted potential comparison takes absolute local errors. A smaller
extension would expose the signed identity underlying that proof. This is
related to the performance-difference approach to policy comparison.
[Kakade and Langford, 2002](https://homes.cs.washington.edu/~sham/papers/rl/aoarl.pdf).
Its starting point here is already local:
[`GameTheory.Protocol.InformationModel.runBehavioral_expect_sub_eq_sum_stepGains`](../GameTheory/GameTheory/Analysis/Protocol/SequentialRationality.lean)
telescopes integrable one-step value changes for the canonical runner.

For source and target history kernels \(P,Q\), a common bounded stopping rule
\(\tau\), and a common bounded terminal payoff \(u\), let
\(V_Q(h)=\mathbb E_Q[u(H_\tau)\mid H_0=h]\). At a running history set

\[
 r(h)=(P-Q)V_Q(h)=PV_Q(h)-V_Q(h),
\]

using the target Bellman equation; set \(r=0\) at the stopping boundary. The
proposed stopped identity is

\[
 V_P(h)-V_Q(h)=
 \mathbb E_P\left[\sum_{t<\tau}r(H_t)\mid H_0=h\right].
\]

Indeed, \(V_P-V_Q=r+P(V_P-V_Q)\) before stopping and is zero at the boundary.
Finite-horizon iteration gives the identity. Bounded payoff and horizon supply
absolute integrability, even on an infinite history carrier. With different
terminal payoffs there is an additional expected boundary discrepancy.

[StoppedCharge](../GameTheoryExtensions/Analysis/Protocol/StoppedCharge.lean)
already constructs expectations of nonnegative charges. A signed charge can
be split into its positive and negative parts; the existing drift laws then
provide the algebra. The arbitrary-start stopped-runner identity is checked in
[StoppedResidual](../GameTheoryExtensions/Analysis/Protocol/StoppedResidual.lean).
Its actual gain consumer is a separate acceptance obligation. The
[current potential proof](../GameTheoryExtensions/Analysis/Protocol/StoppedContinuationComparison.lean)
already contains the one-step signed decomposition before taking absolute values.

This could certify a nonpositive total gain despite some positive local
residuals, or prove exact cancellation where a TV-based charge stays positive.
It could also be merely a more expensive way to prove the same bound. Acceptance
requires a concrete conditional gain consumer where the signed estimate is
strictly better, uniformly over its legal deviations and common assessment
sequence. Cancellation only at initialization is insufficient. The selected
joint law remains a separate obligation.

## Ownership and acceptance

| Layer | Useful work | Evidence required before adoption |
| --- | --- | --- |
| Multitubes theory | Finite affine-ray lemma; optionally finite invariant-subspace certificates if no existing theory API suffices | A general theorem expressed without game semantics, reusing existing finite alternatives and linear algebra |
| Multitubes examples | Log-rate and signed-residual examples; a computed closed space with a distinguishing-word failure case | Examples exercise the theory and its limits; no new core probability semantics |
| GameTheoryExtensions | History-monomial certificate soundness, labelled observable interpretation, stopped signed residuals | Existing policy, belief, runner and consistency predicates appear in the conclusion |
| GameTheory | Upstream a demonstrated game-generic theorem when ownership is settled | More than one substantive client, retained scope, and an explicit dependency decision |
| Interaction and Vegas | Actual information/action labels, legal deviation transport, runtime history weights and conditional gain producers | One complete preservation consumer retains its common consistency sequence and selected joint law |

Prioritize the certificate interpreter and unequal-rate incentive example for
a general mathematical addition. In parallel as a research direction, select
a finite runtime fragment for observable-space construction; measure the
computed dimension and all adapter costs. A full-dimensional closure is useful
negative evidence about that proposed compression, not failure of the method.
The signed-residual route is the smaller proof-refinement experiment, provided
an actual consumer exhibits cancellation.

A substantive SE acceptance test should include an off-path information set,
nonconstant utilities, a deviation that depends on available information, and
the exact initialized joint readout/payoff law. A helper theorem that merely
assumes all four obligations is not a producer of them. Acceptance need not
require fewer lines: automatic certificates, weaker hypotheses, and a reusable
game-generic construction are independent gains.

The existing paired-step interface, relative-error belief transports, and
service-timing product bounds should be reused where they apply. These
proposals give no reason to replace them wholesale or import quitting-game
debt identities into unrelated games. They also do not establish general
USI/MSI preservation or a filtration framework.

## Bibliography keys

| Key | Use |
| --- | --- |
| `Reny2026PowerSequences` | Affine-ray lemma and integer-power characterization |
| `Dilme2024PowerSequences` | Consistency characterization |
| `Tzeng1992Equivalence` | Polynomial-time probabilistic-automata equivalence |
| `Kiefer2020WeightedAutomata` | Linear spaces, certificates and distinguishing words |
| `KieferEtAl2011LanguageEquivalence` | Equivalence algorithms and the inclusion boundary |
| `KieferEtAl2013WeightedAutomata` | Expected-reward versus reward-distribution equivalence |
| `KakadeLangford2002` | Performance-difference approach to policy comparison |
