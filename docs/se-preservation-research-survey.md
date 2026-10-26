# Research directions for sequential-equilibrium preservation

This survey identifies results and proof techniques that could simplify or
generalize VegasCore's sequential-equilibrium (SE) preservation arguments, or
help refute proposed preservation claims. Published results, existing library
interfaces, and proposed applications are distinguished throughout. The
applications are research proposals, not checked preservation theorems or
changes to the [fixed target and checklist](se-async-checklist.md).

The [experiment ledger](se-preservation-experiments.md) records checked local
implementations, concrete consumers, boundary examples and decisions to retain
existing interfaces. Its results have their stated scopes; the broader
applications below remain research proposals where those adapters are missing.

The most direct simplification opportunity is to transport only the
continuation gains needed for rationality. Information compression supplies a
broader generalization route, while power-sequence consistency offers finite
certificates for positive constructions and obstructions.

| Direction | Potential benefit | Main adapter still needed |
| --- | --- | --- |
| Sufficient information | Discard metadata without reconstructing full recall | Uniform information sufficiency and the selected joint-law guarantee |
| Continuation-gain equivalence | Replace full posterior comparisons with a few expectations | A family of gain functions covering every required deviation and perturbation |
| Coarsening at random | Derive Bayes transport from an operational likelihood condition | Actual observation-fiber likelihood factorization |
| Power-sequence consistency | Replace rate arguments with finite certificates | Shared action exponents, coefficients, and actual history likelihoods |
| Scheduler noninterference | Reuse local relational proofs across backends | Relations accounting for all observable clocks, traffic, and receipts |
| Quantitative game abstraction | Sharper error aggregation | Bounds at every required conditional information site |
| Adapted probability | Compare information over time across runtimes | Player-specific information and unilateral-deviation compatibility |
| Transport morphisms and sections | Compose local continuation comparisons across backends | Actual kernel comparisons on an adequate family of observables |
| Affine debt transport and potentials | Replace uniform error counts with accumulated-charge bounds | Finite homogeneous encoding where needed; uniform conditional bounds along the common fully mixed assessment sequence |

The mathematical connections below are separated from the
[proposals by owner and kind](#proposals-by-owner-and-kind). In particular,
Multitubes examples illustrate its theory; their current choices are not
requirements imposed on GameTheory or Vegas.

## Sufficient information and preservation of SE payoffs

Tang, Subramanian and Teneketzis distinguish mutually sufficient information
(MSI) from unilaterally sufficient information (USI). MSI guarantees existence
of an SE using compressed information; USI preserves the set of SE expected
payoff profiles. Deviations retain access to full recall. Their published
Theorems 3 and 4 concern finite dynamic games.
[Information Compression in Dynamic Games](https://doi.org/10.1007/s13235-025-00663-1).

Writing player information as \(H_i\), its recursively updated compression as
\(K_i\), and the system state as \(X\), USI requires a factorization of the form

\[
 P^g(X,H_i,H_{-i}\mid K_i)
 = F^{g_i}(H_i\mid K_i)\,\Phi^{g_{-i}}(X,H_{-i}\mid K_i)
\]

for every behavioral profile \(g\) at supported observations. The discarded
information contributes no further prediction of the state or other players'
information; its conditional reconstruction depends only on the player's own
strategy. This permits replacing full-information behavior with randomized
compressed behavior while preserving equilibrium payoffs.

**Proposed application.** Treat a source-facing runtime view as a candidate
compression. This offers a route for a backend whose additional private
metadata cannot be reconstructed exactly. The exact decoders in
[SequentialPhasePlayerInformation](../Vegas/Game/SequentialPhasePlayerInformation.lean)
provide a useful comparison point, while
[ObservedChoice](../GameTheoryExtensions/Math/Probability/ObservedChoice.lean)
already factors observation-local choices under explicit probability premises.
The new work would be to produce sufficiency from the runtime, then connect it
to the existing equilibrium construction.

The theorem compares strategy classes within one game and preserves expected
payoff profiles. Vegas requires a relation between games and the joint law of
initial parameters, public results, and realized payoffs for a selected source
equilibrium. Those are separate obligations. In particular, equality of
expected payoffs for the supplied utilities does not imply equality of that
joint law.

USI is also stronger than many forward-implementation arguments need. An
independent public coordination signal may fail its factorization while still
allowing all source equilibria to be implemented by ignoring the signal. A
localized sufficiency condition for the prescribed opponent family may be
enough for Vegas, but requires its own proof. Checking independence only under
honest play would not discharge the quantification over deviations or the
common consistency sequence.

## Continuation-gain equivalence

The value-equivalence principle in model-based reinforcement learning compares
models through their Bellman updates on specified functions and policies.
Agreement on all state-transition probabilities can be stronger than planning
requires. This supplies a useful analogy, not an SE-preservation theorem.
[Grimm et al., The Value Equivalence Principle](https://proceedings.neurips.cc/paper/2020/hash/3bb585ea00014b0e3ebe4c6dd165a358-Abstract.html).

**Proposed application.** Fix the continuation strategy and a pure local choice
\(a\). On a common hidden-history or readout carrier, write

\[
 d_a(h)=V(h,a)-V(h,\text{prescribed}).
\]

Once the two continuation kernels have been compared, rationality transport
needs an upper bound on

\[
 \mathbb E_{\mu_R}d_a-\mathbb E_{\mu_S}d_a.
\]

Full equality of \(\mu_R\) and \(\mu_S\) is sufficient, but equality of their
expectations on the span of the relevant gain functions also suffices. For a
finite choice menu, a small basis for that span can replace many distribution
identities with a few moment identities. A one-sided bound can suffice even
when these moments are unequal.

The library already has the appropriate consumers:

- [SourceGainTransport](../GameTheoryExtensions/Analysis/Protocol/SourceGainTransport.lean)
  expresses an information-site gain as an expectation of history gains and
  handles histories with constant continuation payoff.
- [LocalSimulationLimit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean)
  consumes pure local comparisons with vanishing error, combines them with a
  common consistent limit, and upgrades local optimality to whole-policy SE.
- [AffineKeyedPools](../GameTheoryExtensions/Analysis/Protocol/AffineKeyedPools.lean)
  uses common scalar scores to compare pooled components.
- [AffineDecorrelation](../GameTheoryExtensions/Math/Probability/AffineDecorrelation.lean)
  controls an affine payoff comparison through covariance estimates.

A direct finite-probability calculation makes the possible weakening explicit.
If an observation tilts a source posterior \(p\) by a nonnegative likelihood
\(L\), with \(\mathbb E_p L>0\), set

\[
 q(h)=\frac{p(h)L(h)}{\mathbb E_p L}.
\]

Then

\[
 \mathbb E_q d_a
 =\mathbb E_p d_a+
   \frac{\operatorname{Cov}_p(L,d_a)}{\mathbb E_p L}.
\]

Consequently, a nonpositive covariance preserves a nonpositive source gain
for this comparison. Information can change without changing the preferred
action. This calculation is a proposed adapter for the existing gain APIs;
it is not a claim that the runtime satisfies the covariance condition.

The function family must cover every local alternative required by the SE
argument and the approximating profiles used to establish consistency. If
the carrier or continuation gains differ, their comparison error must be
included before using the displayed identity. The initialized joint-law proof
remains necessary. Rare observations also require a relative error estimate:
small unconditional error need not remain small after division by their mass.

## Coarsening at random and observation likelihoods

Grünwald and Halpern characterize when conditioning in a reduced state space
agrees with conditioning in a space that includes the observation protocol.
Their coarsening-at-random (CAR) condition requires the likelihood of an
observation to be constant across compatible underlying states. Theorem 3.1
gives equivalent formulations.
[Updating Probabilities](https://doi.org/10.1613/jair.1164).

**Proposed application.** The corresponding producer obligation for a runtime
information site \(I\), history projection \(\pi\), and compatible source
history \(h\) is

\[
 \sum_{r\in I:\,\pi(r)=h}\operatorname{reach}_R(r)
 =c_I\operatorname{reach}_S(h),\qquad c_I>0.
\]

The multiplier must not depend on \(h\). This is the form already consumed by
[ProportionalBeliefTransport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean).
The useful research target is a compositional operational producer of this
factorization. The Bayes normalization itself already has an owning layer.
[StoppedBayes](../GameTheoryExtensions/Analysis/Protocol/StoppedBayes.lean)
provides another route when the information site can be recovered from a
first-passage law.

For a negative test, compare the likelihood of one runtime record at two
source histories in the same source information fiber. Different likelihoods
disprove this posterior-preservation criterion. They do not alone refute SE
preservation: an incentive separation and exclusion of all alternative
preserving equilibria are still needed. The
[universal-preservation criterion](commit-reveal-research/universal-preservation-criterion.md)
already explains the local Blackwell-style separating decision problem.

The relevant hidden state includes future service behavior when it affects
continuation gains. Independence between an initial scheduler seed and source
values is insufficient after conditioning on observed traffic. Likewise,
source-value privacy does not rule out strategically useful information about
future delivery, as illustrated by the
[private-seed signalling analysis](se-private-seed-signalling.md).

## Power-sequence certificates for consistency

Dilmé characterizes consistency in finite extensive-form games using power
sequences; integer exponents suffice. Reny's Theorem 2.3 obtains a certificate
through Farkas' lemma. In its unnormalized form, positive limiting action
weights remain fixed and vanishing weights have the form
\(c_a\varepsilon^{k_a}\), with \(c_a>0\) and positive integer \(k_a\).
Normalizing at each information set gives a fully mixed sequence with the
required limit. Nature's supported probabilities remain fixed.
[Dilmé](https://doi.org/10.1007/s00182-023-00874-z),
[Reny](https://doi.org/10.1007/s00182-026-00997-z).

**Proposed application.** Build a finite certificate interface for off-path
belief supports and leading coefficients. The
[finite-support construction below](#finite-certificates-for-power-sequence-supports)
gives the shared exponent constraints and the remaining semantic obligations.
The pinned Mathlib has geometric Farkas machinery in
`Mathlib.Analysis.Convex.Cone.Dual` and
`Mathlib.Analysis.Convex.Cone.InnerDual`; a suitable finite-matrix adapter to
that interface still needs investigation. An external alternative is
[Multitubes' finite linear-programming library](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/LinearProgramming/FourierMotzkin.lean),
with a direct theorem of the alternative and associated rational certificate
checkers. Multitubes is not a VegasCore dependency: its
[package requirements](#reuse-boundary) and a game-specific interpretation
must be supplied before these results can be used here.

This is useful for explicit off-path belief constructions and finite
counterexample search. It does not preserve arbitrary extra constraints on a
chosen approximating family, such as fixed component mixtures or particular
couplings at every approximation. Replacing a completion sequence therefore
requires checking those properties again. Inconsistency of one assessment
also does not establish nonexistence of every preserving equilibrium.

## Scheduler noninterference and stopped relational proofs

Popescu, Hölzl and Nipkow separate a program's information-flow property from
the scheduler's: under their hypotheses, a noninterfering scheduler turns
possibilistic program noninterference into probabilistic noninterference.
[Noninterfering Schedulers](https://doi.org/10.1007/978-3-642-40206-7_18).
The related Isabelle development proves compositional results for a
multithreaded language with uniform scheduling.
[Probabilistic Noninterference, AFP](https://isa-afp.org/entries/Probabilistic_Noninterference.html).

**Proposed application.** Relate two executions that differ in hidden source
coordinates, retain the observer's visible records, and couple their next
steps so the relation persists until an explicitly handled stopping boundary.
The probabilistic induction is close to
[StoppedKernelComparison](../GameTheoryExtensions/Analysis/Protocol/StoppedKernelComparison.lean).
A reusable runtime relation could separate observation and scheduler
obligations from repeated trace induction.

This requires accounting for the complete observation rule. Clock values,
activation order, pending traffic, and receipts cannot be erased if a player
can condition a decision on them. A weak equivalence that hides timing is
unsuitable when time is observable. Such an information theorem must still
be combined with deviation simulation, enforcement, and consistent completion;
noninterference alone is not an equilibrium theorem.

## Quantitative abstraction and adapted probability

Kroer and Sandholm's chance-relaxed skew well-formed abstractions separate
reward error, continuation-probability error, and conditional information-set
distribution error. They establish guarantees for Nash and self-trembling
equilibria, not a general SE-transfer theorem.
[Imperfect-Recall Abstractions with Bounds in Games](https://doi.org/10.1145/2940716.2940736).

**Proposed application.** Compare their aggregation with the runtime's stopped
law, posterior, and payoff estimates. An event-sensitive or conditional
reach-weighted bound may improve a uniform site-count multiplier. For SE,
the required conditional estimate must remain valid at every information site
and for every deviation covered by the target theorem, along one common fully
mixed assessment sequence. Root-weighted regret alone is insufficient:
conditioning at rare sites can amplify a small unconditional error.

Adapted probability treats a stochastic process together with its filtration.
Equal process laws can yield different decision values when information is
revealed at different times. Beiglböck, Pflügl and Schrott give transfer
principles for filtered processes and describe their relation to bicausal
couplings and adapted Wasserstein distance.
[A Probabilistic View on the Adapted Wasserstein Distance](https://arxiv.org/abs/2406.19810).

**Proposed application.** Use information-preserving process comparisons as a
language for runtime-general refinement and quantitative approximation.
Vegas would need player-specific filtrations, legal randomized policy
transport, unilateral-deviation compatibility, and one off-path consistency
construction. A coupling of honest executions would not supply these. This
is a longer-term generalization direction; the finite stopped-kernel API is
the more immediate implementation surface.

## Connections to Multitubes and UniformEquilibrium

[Multitubes](https://github.com/elazarg/multitubes/tree/a58f90601d4133bed849a114c1c17bf7385f3196)
provides much of the algebra beneath continuation comparisons.
[UniformEquilibrium](https://github.com/elazarg/UniformEquilibrium/tree/6a442b8fbc88a9b1232b8666084b0990d54fe6fb)
contains concrete applications connecting that algebra to incentives. The
external results below have the hypotheses specified in the linked sources.
Their proposed applications to Vegas require adapters; neither those adapters
nor new preservation results are established by this survey.

### Continuation comparisons as transport morphisms

A Multitubes transport assigns a type to each vertex of a directed
multigraph and a function to each edge. The walk map composes those functions.
An exact section is a family compatible with every edge map; a lax section
satisfies the corresponding forward inequality. The fibers can differ between
vertices, and the edge maps need not be invertible.

A probability kernel acts backward on observables:

\[
 K_e^*f(h)=\mathbb E[f(H')\mid h].
\]

The
[KernelTransport application](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/StochasticProcesses/StochasticProcesses/KernelTransport.lean)
implements this as a transport on the reversed graph. Its
[`StochasticProcesses.isSection_iff_harmonic`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/StochasticProcesses/StochasticProcesses/KernelTransport.lean)
and
[`StochasticProcesses.isLaxSection_iff_superharmonic`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/StochasticProcesses/StochasticProcesses/KernelTransport.lean)
theorems identify
harmonic families with exact sections and superharmonic families with lax
sections. Walk transport agrees with expectation under the composed forward
kernel.

The generic
[Morphism module](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/Morphism.lean)
provides
[`Maths.Transport.Hom.walkMap_naturality`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/Morphism.lean)
for exact comparisons and
[`Maths.Transport.LaxHom.walkMap_le`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/Morphism.lean)
for one-sided comparisons under monotone edge maps.
[`Maths.Transport.LaxHom.map_isLaxSection`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/Morphism.lean)
transports a lax section through a monotone lax morphism. These are reusable
local-to-global rules.

**Proposed application.** Use continuation observables as fibers and source
versus runtime comparison maps as morphisms. The observable families could
contain only the gains needed to compare deviations, provided they are closed
under all required continuation operators. This connects transport directly
to continuation-gain equivalence: it may suffice to intertwine the relevant
observables instead of entire posterior distributions. A small terminal gain
basis alone does not guarantee that this closure remains small.

This could organize repeated continuation-comparison inductions beneath
[LocalSimulationLimit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean).
It does not supply the actual kernel comparisons, the alignment of source
steps with runtime steps, information-local choices, posterior comparisons,
or the common consistency sequence. Maximizing separately at hidden histories
can enlarge the deviation class beyond what a player can observe. The
initialized joint-law obligation also remains separate.

The supplied probabilistic application uses nonnegative extended-real
observables. Signed utility gains therefore need an adapter, for example
through bounded real-valued expectations under the appropriate integrability
conditions. The generic transport theory itself does not impose that choice
of scalar type.

### Affine debt transport and accumulated error

UniformEquilibrium makes the incentive connection explicit in
[TerminalSemanticDirectedTransport](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticDirectedTransport.lean).
For the module's finite-player quitting game and an exact semantic prefix
chain, a player's best-response debt satisfies

\[
 D_t=\delta_t+s_tD_{t+1},
\]

where \(\delta_t\) is the local defect and \(s_t\) is survival probability.
[`GameTheory.QuittingTerminalSemanticPrefixChain.debt_isSection`](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticDirectedTransport.lean)
expresses this as an exact
section of a backward-time affine transport. Its finite telescope is

\[
 D_0=\sum_{t<n}\left(\prod_{j<t}s_j\right)\delta_t
       +\left(\prod_{j<n}s_j\right)D_n.
\]

Thus local defects are weighted by the probability of reaching them. The
module constructs such chains from literal behavioral profiles of that
quitting game. These are not debt recursions for arbitrary stochastic games;
a new client must establish its own incentive recurrence before applying the
generic affine telescope. Within this quitting-game setting, a positive-debt
return with survival loss must be paid by positive reached defect. The related
[DebtTransportLaw](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/UniformEquilibrium/Quitting/Debt/Dynamic/DebtTransportLaw.lean)
uses reflected max-affine transport for quitting-game finite dynamic debt
under its residual-zero hypothesis, including a closed form and a
classification of unchanged positive debt.

Another concrete consumer is
[HarmonicFiniteCoupledPotentialLP](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/MathUE/Probability/HarmonicFiniteCoupledPotentialLP.lean).
Its
[`Math.Probability.BoundedCoupledPotential`](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/MathUE/Probability/HarmonicFiniteCoupledPotentialLP.lean)
uses a finite node type, one fixed time-homogeneous Markov kernel \(P\), and
a fixed state charge \(c\). A bounded nonnegative potential pays that charge
when

\[
 c(h)+\mathbb E_P[\Phi(h')\mid h]\le \Phi(h),\qquad 0\le\Phi\le B.
\]

Telescoping bounds every finite expected accumulated charge by \(B\).
The theorem
[`Math.Probability.finiteExpectedSpaceTimeMarkovVariation_le_of_boundedCoupledPotential`](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/MathUE/Probability/HarmonicFiniteCoupledPotentialLP.lean)
applies this to conditional absolute variations dominated by \(c\); the value
observable may depend on time, but the kernel and charge do not. The module
encodes the Bellman, lower-bound, and upper-bound inequalities as a finite
linear system and derives a Farkas obstruction to existence of such a
potential. The obstruction concerns the chosen potential bounds, not
nonexistence of an equilibrium.

**Proposed application.** A potential on stopped comparison states could
replace a uniform number-of-opportunities times worst-error estimate with a
bound reflecting where continuation errors actually occur. This could improve
constants or broaden the runtime interface even when the proof is not shorter.
The runtime's history-dependent kernels also depend on the fully mixed
approximation parameter \(\varepsilon\). Applying this finite theorem
requires, for each \(\varepsilon\), a faithful finite state encoding with a
homogeneous kernel and static charge. A sufficient finite summary or a finite
time/history augmentation must be justified; arbitrary histories do not
automatically give a finite carrier. The resulting bounds must satisfy the
[conditional quantifiers above](#quantitative-abstraction-and-adapted-probability)
with one error bound \(\eta(\varepsilon)\) tending to zero, uniformly over the
sites and deviations required by the SE-limit consumer. Existence of a
finite LP at each \(\varepsilon\) supplies neither this uniform control nor
vanishing error. An extension to infinite carriers instead needs a new
probabilistic theorem with its integration and stopping hypotheses.

Multitubes also has a more general local affine comparison of the form
\(E'\le b_e+a_eE\), with \(a_e\ge0\) and compatible radii
\(b_e+a_er_s\le r_t\), in
[SwitchedHybridControl.ErrorBounds](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/SwitchedHybridControl/SwitchedHybridControl/ErrorBounds.lean).
The nonnegative-gain hypothesis is the
[`SwitchedHybridControl.ErrorComparison.gain_nonneg`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/SwitchedHybridControl/SwitchedHybridControl/ErrorBounds.lean)
field: it is needed to propagate an upper radius bound.
[`SwitchedHybridControl.ErrorComparison.walk_error_le`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/SwitchedHybridControl/SwitchedHybridControl/ErrorBounds.lean)
propagates the bound along shared executions;
finite infeasible radius constraints admit sparse certificates. Instantiating
the comparison with actual runtime continuation errors remains necessary.

### Finite certificates for power-sequence supports

The
[FourierMotzkin module](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/LinearProgramming/FourierMotzkin.lean)
provides
[`Maths.LinearProgramming.theorem_of_alternative`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/LinearProgramming/FourierMotzkin.lean)
for finite weak linear inequalities over a linearly ordered field. It also
provides
[`Maths.LinearProgramming.exists_rowEval_pos_iff_not_hasBalancedCertificate`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/LinearProgramming/FourierMotzkin.lean),
a strict homogeneous alternative. The
[CertificateCheck module](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/FiniteInequality/CertificateCheck.lean)
connects executable rational checks to real feasibility and infeasibility,
including
[`Maths.FiniteInequality.not_realPotential_of_checkRationalCertificate`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/FiniteInequality/CertificateCheck.lean).
These supply an external finite interface for the power-sequence proposal,
subject to the [reuse boundary](#reuse-boundary).

Let \(m_h\) be the vector of occurrence counts of each zero-limit action along
history \(h\), indexed by the same behavioral choices as the exponent vector
\(k\). The history's leading exponent is \(m_h\cdot k\). For each information set,
choose a history \(h_I\) assigned positive limiting belief. A proposed belief
support requires

\[
 (m_h-m_{h_I})\cdot k=0
 \quad\text{for histories assigned positive belief},
\]

\[
 (m_h-m_{h_I})\cdot k>0
 \quad\text{for histories assigned zero belief},
 \qquad k_a>0.
\]

Here histories are restricted to those compatible with Nature's fixed
support, and each action exponent is shared across all occurrences of that
behavioral choice. The finite homogeneous strict inequalities can be
normalized to margin one while retaining the equalities. Equalities can be
encoded by two weak inequalities. A rational Farkas certificate can then
rule out every real exponent vector satisfying this support pattern.

For example, constraints \(k_a>k_b\), \(k_b>k_c\), and \(k_c>k_a\) sum to
the contradiction \(0>0\). This illustrates a certificate shape, not a
constructed counterexample in the runtime.

**Proposed application.** Compile a candidate off-path support into this
system and use the existing checker to certify a small obstruction. A
successful exponent check still needs positive leading-coefficient equations,
the actual history-likelihood adapter, and the connection to consistency.
The finite alternative alone does not prove the full power-sequence theorem
or its integer-exponent conclusion. Failure of one support pattern or one
construction does not establish failure of every preserving SE.

### Holonomy and forward-path coherence

Holonomy is the transport around a closed directed walk. It suggests a useful
coherence test, but trivial directed-cycle holonomy alone does not imply path
independence on an acyclic runtime graph.

For example, let two parallel edges \(r\to t\) act on real fibers by
\(x\mapsto x\) and \(x\mapsto x+1\). There are no nonempty directed cycles,
so every closed-walk map is the identity. Nevertheless, an exact section
would require both \(x_t=x_r\) and \(x_t=x_r+1\), which is impossible.

The library's
[Exact module](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/Exact.lean)
retains the needed hypotheses:
[`Maths.Transport.walkMap_eq_of_trivialHolonomy_of_return`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/Exact.lean)
requires a return walk, while the strongly connected corollary obtains those
returns from connectivity. Its section theorem from a common holonomy fixed
point requires suitable injective return maps.

**Proposed application.** For scheduler-independent preservation, compare
alternative forward execution paths with the required observations retained.
A cycle-only test on full histories can be vacuous. This is a refutation of
that structural shortcut, not a counterexample to runtime SE preservation.

### Reuse boundary

There are separate package, dependency, and semantic boundaries:

- **Application packages.** The
  [Multitubes root package](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/lakefile.toml)
  provides the Maths libraries. The
  [StochasticProcesses package](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/StochasticProcesses/lakefile.toml)
  and
  [SwitchedHybridControl package](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/SwitchedHybridControl/lakefile.toml)
  have their own lakefiles and depend on the root package. Requiring `maths`
  does not pull in either application; matching its revision cannot make
  their modules importable. Reusing those modules needs an explicit dependency
  on the application package and a compatible package layout. For production
  clients, prefer a justified extraction into the theory plus a local semantic
  adapter over a dependency on an example's models.
- **Shared package identities.**
  [UniformEquilibrium's configuration](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/lakefile.lean)
  and [VegasCore's configuration](../lakefile.toml) both require a package
  named `GameTheory`. UniformEquilibrium's
  [submodule revision](https://github.com/elazarg/GameTheory/tree/e1aff265355a3383b9cba963259470e596a85c9c)
  is distinct from the [GameTheory dependency here](../GameTheory/lakefile.lean).
  Lake requires package names to be unique in the dependency graph; adding
  UniformEquilibrium would use a single resolved GameTheory package, not
  provide its own isolated copy. With VegasCore's direct dependency retained,
  UniformEquilibrium's APIs would need to work against that copy.
  [Lake dependency specification](https://lean-lang.org/doc/api/Lake/Config/Dependency.html).
- **Toolchain and transitive pins.** The cited Multitubes and UniformEquilibrium
  sources select different Lean and Mathlib releases; UniformEquilibrium's
  [manifest](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/lake-manifest.json)
  pins `maths` to `26622cefd5329d5b5545ad09e3678151bd61ba52`, rather than the
  standalone revision cited above. VegasCore's selected versions are recorded
  in [lean-toolchain](../lean-toolchain), [lakefile.toml](../lakefile.toml), and
  [lake-manifest.json](../lake-manifest.json). Multitubes also requires
  `fixed-point-theorems`; VegasCore already inherits that package through
  GameTheory, with a different pin. All shared pins must be reconciled and the
  relevant modules checked against the resulting single dependency graph.
- **Semantic adapters.** Compatible builds would still leave the signed
  expectation, quitting-game incentive, finite-state, and uniform-limit
  obligations described above. Importing UniformEquilibrium wholesale is not
  an automatic bridge from its examples to Vegas preservation.

External declaration citations link to full GitHub commit IDs. The local
documentation checker exempts the labels of those external Lean-source links
from local name resolution; it does not verify the external declarations.

## Proposals by owner and kind

The ownership boundary follows the mathematical content of a statement.
Multitubes owns transport and finite-constraint theory. GameTheory owns game
semantics, information, deviations, and equilibrium concepts, together with
its existing probability foundation. GameTheoryExtensions is the local home
for reusable protocol bridges that are not part of the pinned GameTheory
dependency. Interaction and Vegas own the actual runtime and compiler
interpretations. UniformEquilibrium supplies concrete consumers and candidate
reusable mathematics; its quitting-game semantics is not a required layer of
the Vegas implementation.

The proposals distinguish four kinds of work:

- **Reuse:** instantiate an existing theorem; no new mathematical result is
  claimed.
- **Refactor:** replace an implementation or reorganize ownership while
  retaining its mathematical guarantee. Any promised reduction includes
  adapters and all affected callers.
- **Addition:** supply a missing interpretation, theorem, or stronger result
  needed for the proposed route.
- **Example:** demonstrate a theorem and its boundary on a small model,
  without making that model a downstream semantic requirement.

Here *needed* means necessary to establish a proposed route, not a new
prerequisite for the currently checked preservation results. A proposal is
not authorization to change the SE target, runtime observations, or payoff
semantics.

| Owner | Reuse or refactor candidate | Additions needed for the proposed route |
| --- | --- | --- |
| Multitubes theory | Reuse morphisms, section propagation, affine composition, and finite alternatives; extract a generic comparison lemma from an example only if it supplies a missing shared API | Any genuinely missing transport law exposed by concrete clients; no missing core law is established by this survey |
| Multitubes examples | Extend the stochastic demonstration and retain the existing nonnegative hitting and deterministic control examples | Signed-observable comparison, accumulated expected charges through stopping, and small coherence/certificate examples |
| GameTheory foundations | Reuse signed expectations, information models, Bayes transport, sequential limits, and one-shot optimality | Game-semantic power-sequence certificates; optionally a precisely scoped information-compression theorem |
| GameTheoryExtensions | Reuse the current gain and SE-limit consumers; evaluate a potential-based implementation of stopped-error bounds | Bridges from generic transports to actual continuation runners and conditional gain estimates |
| Interaction and Vegas | Replace selected repeated runtime comparison proofs only after a complete consumer demonstrates a benefit | Actual kernel, observation, gain-family, stopping, and perturbation obligations for the chosen abstraction |

### Multitubes: theory and examples

**Theory.** The generic transport permits arbitrary fibers and functions.
Signed observables therefore do not require redesigning the core. Morphism
composition, monotone section transport, affine label composition, and the
finite Farkas alternative are existing reuse targets. A generic comparison
statement discovered in an application can belong in the theory when its
hypotheses mention only transports, relations, orders, or affine errors.
First check whether it is already an instance of the existing morphism or
mixed-section machinery. Moving a proof or supplying a convenient
specialization is a refactor; a weaker-hypothesis or stronger conclusion is
a separate mathematical addition.

For example, the abstract part of
[`SwitchedHybridControl.ErrorComparison`](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/SwitchedHybridControl/SwitchedHybridControl/ErrorBounds.lean)
concerns arbitrary pairs
of transports and an affine scalar error law. It is a candidate for a shared
theory interface if multiple clients need it. Its concrete switched-system
models remain examples. This is an ownership proposal, not evidence that
extracting another interface will shorten the clients.

**Examples.** Useful extensions are:

- A bounded real-valued counterpart to the nonnegative expectation example,
  demonstrating exact and one-sided kernel comparison. A small pair of laws
  agreeing on selected continuation observables but differing as distributions
  would illustrate the value-equivalence boundary.
- An accumulated-charge example using a stopped kernel and a potential
  satisfying \(c+P\Phi\le\Phi\). Include a rare-event case where an unconditional
  small error becomes large after conditioning. The example should show both
  the useful estimate and why it is insufficient for every information site.
- A rational certificate for a contradictory finite exponent system, and the
  acyclic parallel-edge holonomy counterexample. The former illustrates the
  checker; interpreting its rows as a game's trembles belongs in the game
  layer.

These complement the existing examples. Nonnegative extended-real
expectation retains its useful absence of integrability assumptions;
deterministic all-walk error bounds retain their control interpretation.
There is no identified correctness defect requiring those examples to be
replaced. An example can use Mathlib probability to instantiate the theory;
it need not introduce a second general expectation library or depend on Vegas.

### GameTheory: reuse, possible refactors, and new game theory

**Existing foundations to reuse.** The owning declaration surfaces already
provide:

- Signed real expectations with explicit integration guards in
  [ExpectationBind](../GameTheory/GameTheory/Math/Probability/ExpectationBind.lean),
  including composition on arbitrary carriers, and a bounded-payoff tower law
  in [ExpectationComposition](../GameTheory/GameTheory/Math/Probability/ExpectationComposition.lean).
- Reach-weight, history-projection, and observed-readout Bayes transport in
  [BeliefTransport](../GameTheory/GameTheory/Analysis/Protocol/BeliefTransport.lean).
- Assessment convergence and passage of continuation inequalities to limits
  in [SequentialLimits](../GameTheory/GameTheory/Analysis/Protocol/SequentialLimits.lean).
- Sequential rationality from local optimality under the stated recall and
  finiteness hypotheses in
  [SequentialOneShot](../GameTheory/GameTheory/Analysis/Protocol/SequentialOneShot.lean).
- Static strategic transfer through utility comparisons in
  [UtilitySimulation](../GameTheory/GameTheory/Core/UtilitySimulation.lean).
  This already distinguishes utility comparison from outcome-law comparison;
  it does not itself discharge the off-path requirements of SE.

The Multitubes proposal supplies no reason to replace these definitions or
re-prove these families wholesale. A transport interpretation should refer
to the existing PMFs, policies, information sites, assessments, and expected
utilities. For GameTheory, the signed-observable task is a bridge to
transport, not a missing real-expectation theory.

**Candidate refactors.** A generic protocol theorem could delegate its
propagation induction to transport after a faithful interpretation is proved.
That is worthwhile only if the result retains the existing carrier scope,
integration conditions, information restrictions, and conclusion, and the
complete implementation becomes simpler or more reusable. A bridge can start
as an optional module in GameTheoryExtensions; no dependency from GameTheory's
core to Multitubes is assumed. Upstreaming requires a separate ownership and
dependency decision. Successful replacement should update callers and remove
superseded implementations, rather than keep parallel semantic definitions.

**Additions with game-semantic content.** The power-sequence route needs a
certificate interpretation for a finite game: behavioral choices shared
across histories, history monomials, Nature's support, normalization, limiting
belief coefficients, and a theorem connecting the certificate to the existing
consistency predicate. Soundness of supplied certificates and completeness
of the certificate format are different results. The former supports checked
constructions; refuting all consistent assessments with a prescribed support
also needs the appropriate necessity result. The arithmetic checker remains
in Multitubes, while game-to-constraint translation and semantic correctness
belong in GameTheory or a game-generic extension.

An information-compression theorem is a further optional addition. It must
state its strategy quantifiers, permitted information loss, and whether it
preserves expected payoff profiles or the stronger selected joint law. The
published USI result does not already supply the latter guarantee. Neither
this theorem nor the full power-sequence characterization is claimed to be
present in the protocol interfaces listed here.

### GameTheoryExtensions: the bridge and quantitative refinement

Several relevant game-generic consumers already live here:
[SourceGainTransport](../GameTheoryExtensions/Analysis/Protocol/SourceGainTransport.lean),
[GainComparison](../GameTheoryExtensions/Analysis/Protocol/GainComparison.lean),
[ProportionalBeliefTransport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean),
and [LocalSimulationLimit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean).
The local-comparison limit theorem already accepts uniformly vanishing gain
error and a separate initialized-law error. A new transport layer should
produce those premises rather than define a second equilibrium-transfer
criterion.

A concrete **quantitative addition** is a potential-based generalization of
[StoppedContinuationComparison](../GameTheoryExtensions/Analysis/Protocol/StoppedContinuationComparison.lean).
Its existing theorem bounds the difference of two stopped continuation
expectations by \(2B\delta\,d(h)\), using payoff bound \(B\), uniform step-TV
error \(\delta\), and decreasing depth \(d\). A generalized theorem would
accept a state-dependent local error \(c(h)\) and a nonnegative potential
\(\Phi\) satisfying \(c+P\Phi\le\Phi\). It must retain the stopping and invariant
region conditions, require integrability of the terms being averaged, and
bound the terminal comparison error by the potential. The current depth
estimate should then be a specialization
with \(\Phi(h)=2B\delta\,d(h)\). This separates the new stronger estimate from
the possible refactor of the old proof. The finite homogeneous potential LP
above does not already supply this generalization on arbitrary history
carriers or its uniform control across the fully mixed assessment sequence.

The corresponding **bridge additions** identify kernel pullback with the
existing continuation runner and connect observable comparisons to gains at
information sites. They must handle the actual starting beliefs, stopping
boundaries, and any error introduced by observation or normalization. A new
potential estimate alone does not construct these identifications. Generic
probabilistic statements can be considered for GameTheory's probability
layer; protocol-specific forms belong with its protocol analysis, initially
in the local extension while the interface is evaluated.

### Interaction and Vegas: implementation choices and actual obligations

**Candidate reimplementations.** Select one repeated continuation comparison
or error aggregation in the
[phase-preservation route](sequential-phase-preservation.md). Express its
mathematical recurrence using the existing affine or transport theory and
connect the result to the current gain consumer. Compare the total proof and
dependency cost, not just the final theorem body. A successful change may
remove trace-induction duplication, sharpen a constant, or make the same
consumer usable by another runtime. No broad rewrite of source semantics,
the compiler, or the SE construction follows from the analogy alone.

**Additions required to use a proposed abstraction.** Each concrete consumer
must establish whichever of these premises its route uses:

- The runtime states, stopped summaries, and actual transition kernels
  represented by the graph, including the alignment with source steps.
- The observable or gain family and its closure under every required
  continuation; information-local alternatives must cover all legal target
  choices used by the preservation theorem.
- The actual information fibers and conditional likelihood or gain
  comparisons. Observable clocks, receipts, and traffic cannot disappear by
  choosing a smaller graph.
- The local charge, potential, or comparison error with the quantifiers
  required by the common fully mixed assessment sequence, including rare
  information sites.
- Compatibility with the initialized joint readout/payoff law and the
  existing consistency construction.

Some of these facts may already be supplied by current runtime theorems. The
work is to instantiate them at the proposed interface and identify the
remaining premises before introducing another abstraction. These concrete
producers belong in Interaction or Vegas, even if the theorem consuming them
is generic. Multitubes examples cannot certify them on behalf of the runtime.

### Evaluation order and acceptance

Use two bounded experiments with explicit owners:

1. **Continuation comparison and error.** Multitubes demonstrates the generic
   signed-observable and stopped-charge interpretations. A GameTheoryExtensions
   bridge uses the existing real expectations and continuation semantics.
   One Vegas consumer supplies the actual kernels, information, and potential
   premises and reaches the existing SE-limit theorem.
2. **Consistency certificates.** Multitubes checks an elementary finite
   certificate. A GameTheory-level adapter gives the rows their game meaning.
   A concrete game instance checks the distinction between rejecting one
   proposed support and refuting all preserving equilibria.

The mathematical layers do not require a fixed development chronology: an
actual Vegas obligation may expose the missing generic lemma first, and an
example can be revised to exercise it. Production clients should depend on
theory and their semantic bridges, not on example-specific models.

Measure complete dependency cost, hypothesis strength, off-path and deviation
coverage, and preservation of the initialized joint law. Record existing API
reuse separately from new theorems and concrete adapters. Retain a current
proof when an alternative merely renames its premises or moves comparable
complexity into an unused framework. Proof-size reductions and stronger
runtime guarantees require checked implementations and actual consumers.

## Bibliography keys

The following keys identify these sources in the maintained paper's
`vegas-paper.bib`. A bibliography entry does not assert that its proposed
application has been formalized.

| Key | Source |
| --- | --- |
| `TangSubramanianTeneketzis2026` | Information Compression in Dynamic Games |
| `GrimmBarretoSinghSilver2020` | The Value Equivalence Principle for Model-Based Reinforcement Learning |
| `GrunwaldHalpern2003` | Updating Probabilities |
| `Dilme2024PowerSequences` | A Characterization of Consistent Assessments Using Power Sequences of Strategy Profiles |
| `Reny2026PowerSequences` | A Simple Proof of the Sufficiency of Dilmé's Power-Sequence Test for Kreps-Wilson Consistency |
| `PopescuHoelzlNipkow2013` | Noninterfering Schedulers |
| `PopescuHoelzl2014AFP` | Probabilistic Noninterference |
| `KroerSandholm2016` | Imperfect-Recall Abstractions with Bounds in Games |
| `BeiglboeckPflueglSchrott2024` | A Probabilistic View on the Adapted Wasserstein Distance |
| `MultitubesRepo2026` | Multitubes: transport and constraints on directed graphs |
| `UniformEquilibriumRepo2026` | UniformEquilibrium: formal research on uniform equilibria in stochastic games |
