# Research directions for sequential-equilibrium preservation

This survey identifies results and proof techniques that could simplify or
generalize VegasCore's sequential-equilibrium (SE) preservation arguments, or
help refute proposed preservation claims. Published results, existing library
interfaces, and proposed applications are distinguished throughout. The
applications are research proposals, not checked preservation theorems or
changes to the [fixed target and checklist](se-async-checklist.md).

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
| Affine debt transport and potentials | Replace uniform error counts with accumulated-charge bounds | Conditional bounds along the common perturbation sequence |

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

**Proposed application.** Build a finite certificate interface. A history's
leading exponent is the sum of the exponents of its trembled actions.
Histories with minimal exponent in an information set retain positive limiting
belief; the leading coefficients determine their relative probabilities.
Desired support therefore produces shared linear constraints on action
exponents, with additional coefficient equations for the desired beliefs.

For example, a proposed support pattern requiring

\[
 k_a>k_b,\qquad k_b>k_c,\qquad k_c>k_a
\]

cannot be consistent. This illustrates a certificate shape, not a constructed
counterexample in the runtime. More general infeasibility can be certified by
linear separation. The pinned Mathlib has geometric Farkas machinery in
`Mathlib.Analysis.Convex.Cone.Dual` and
`Mathlib.Analysis.Convex.Cone.InnerDual`. Multitubes supplies a direct
finite-matrix theorem of the alternative and rational certificate checkers;
the [connection below](#finite-certificates-for-power-sequence-supports)
describes the remaining game-specific adapter.

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
the required conditional estimate must remain valid at every site along the
common fully mixed sequence; root-weighted regret alone is insufficient.

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
claims about these libraries below are based on source inspection at these
revisions, without an independent build or axiom audit. Their proposed
applications to Vegas are not checked adapters or new preservation results.

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
isSection_iff_harmonic and isLaxSection_iff_superharmonic theorems identify
harmonic families with exact sections and superharmonic families with lax
sections. Walk transport agrees with expectation under the composed forward
kernel.

The generic
[Morphism module](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/Morphism.lean)
provides Maths.Transport.Hom.walkMap_naturality for exact comparisons and
Maths.Transport.LaxHom.walkMap_le for one-sided comparisons under monotone
edge maps. Maths.Transport.LaxHom.map_isLaxSection transports a lax section
through a monotone lax morphism. These are reusable local-to-global rules.

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
For an exact prefix chain, a player's best-response debt satisfies

\[
 D_t=\delta_t+s_tD_{t+1},
\]

where \(\delta_t\) is the local defect and \(s_t\) is survival probability.
QuittingTerminalSemanticPrefixChain.debt_isSection expresses this as an exact
section of a backward-time affine transport. Its finite telescope is

\[
 D_0=\sum_{t<n}\left(\prod_{j<t}s_j\right)\delta_t
       +\left(\prod_{j<n}s_j\right)D_n.
\]

Thus local defects are weighted by the probability of reaching them. The
module constructs such chains from literal behavioral profiles, not only
abstract scalar sequences. A positive-debt return with survival loss must be
paid by positive reached defect. The related
[DebtTransportLaw](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/UniformEquilibrium/Quitting/Debt/Dynamic/DebtTransportLaw.lean)
uses reflected max-affine transport for finite dynamic debt under its
residual-zero hypothesis, including a closed form and a classification of
unchanged positive debt.

Another concrete consumer is
[HarmonicFiniteCoupledPotentialLP](https://github.com/elazarg/UniformEquilibrium/blob/6a442b8fbc88a9b1232b8666084b0990d54fe6fb/MathUE/Probability/HarmonicFiniteCoupledPotentialLP.lean).
A bounded nonnegative potential pays a nonnegative local charge when

\[
 c(h)+\mathbb E[H(h')\mid h]\le H(h),\qquad 0\le H\le B.
\]

Telescoping bounds every finite expected accumulated charge by \(B\).
The module encodes the Bellman, lower-bound, and upper-bound inequalities as
a finite linear system and derives a Farkas obstruction to existence of such
a potential. The obstruction concerns the chosen potential bounds, not
nonexistence of an equilibrium.

**Proposed application.** A potential on stopped comparison states could
replace a uniform number-of-opportunities times worst-error estimate with a
bound reflecting where continuation errors actually occur. This could improve
constants or broaden the runtime interface even when the proof is not shorter.
For SE, the bound must apply at the required conditional information sites
along the common perturbation sequence. An estimate averaged only from the
initial state is insufficient; rare-site conditioning can amplify it.

Multitubes also has a more general local affine comparison of the form
\(E'\le b_e+a_eE\), with compatible radii
\(b_e+a_er_s\le r_t\), in
[SwitchedHybridControl.ErrorBounds](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Applications/SwitchedHybridControl/SwitchedHybridControl/ErrorBounds.lean).
ErrorComparison.walk_error_le propagates the bound along shared executions;
finite infeasible radius constraints admit sparse certificates. Instantiating
the comparison with actual runtime continuation errors remains necessary.

### Finite certificates for power-sequence supports

The
[FourierMotzkin module](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/LinearProgramming/FourierMotzkin.lean)
already provides Maths.LinearProgramming.theorem_of_alternative for finite
weak linear inequalities over a linearly ordered field. It also provides
exists_rowEval_pos_iff_not_hasBalancedCertificate, a strict homogeneous
alternative. The
[CertificateCheck module](https://github.com/elazarg/multitubes/blob/a58f90601d4133bed849a114c1c17bf7385f3196/Maths/Multitubes/FiniteInequality/CertificateCheck.lean)
connects executable rational checks to real feasibility and infeasibility,
including not_realPotential_of_checkRationalCertificate. These supply a
direct finite interface for the power-sequence proposal.

Let \(m_h\) count occurrences of zero-limit trembled actions along history
\(h\). Its leading exponent is \(m_h\cdot k\). For each information set,
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
retains the needed hypotheses: walkMap_eq_of_trivialHolonomy_of_return
requires a return walk, while the strongly connected corollary obtains those
returns from connectivity. Its section theorem from a common holonomy fixed
point requires suitable injective return maps.

**Proposed application.** For scheduler-independent preservation, compare
alternative forward execution paths with the required observations retained.
A cycle-only test on full histories can be vacuous. This is a refutation of
that structural shortcut, not a counterexample to runtime SE preservation.

### Reuse boundary

The cited standalone Multitubes revision uses Lean 4.35.0. The cited
UniformEquilibrium revision uses Lean 4.34.0 and pins Multitubes revision
`26622cefd5329d5b5545ad09e3678151bd61ba52` from its 4.34.0 version. VegasCore's
toolchain is specified by [lean-toolchain](../lean-toolchain) and
[lakefile.toml](../lakefile.toml); the inspected configuration uses 4.34.1.
Direct reuse therefore requires dependency alignment and checking the selected
APIs at the chosen pin. The standalone application's presence does not imply
that it is available through UniformEquilibrium's older dependency.

## Bounded research experiments

Choose one local-value obligation from the
[phase-preservation route](sequential-phase-preservation.md). Identify the
continuation-gain functions it consumes and a basis for their span. Compare
the cost of transporting those expectations directly with the cost of full
posterior transport, using the existing gain and affine-score APIs.

Two concrete follow-ups use the external libraries without replacing the SE
architecture: compile one proposed power-sequence support into a finite Farkas
system, and construct one conditional continuation-error potential. The first
tests certificate production and decoding; the second tests whether an
accumulated-charge bound improves the existing uniform error estimate. In
either case, count the actual runtime adapter as part of the cost.

Measure the complete dependency cost, number and strength of hypotheses,
coverage of off-path sites and arbitrary local choices, and preservation of
the initialized joint law. A useful result can be a smaller proof, a strictly
broader backend interface, or a concrete obstruction showing that a proposed
compression loses a necessary incentive distinction.

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
