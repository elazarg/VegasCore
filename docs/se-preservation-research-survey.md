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
`Mathlib.Analysis.Convex.Cone.InnerDual`; a suitable finite-matrix adapter
still needs investigation.

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

## A bounded research experiment

Choose one local-value obligation from the
[phase-preservation route](sequential-phase-preservation.md). Identify the
continuation-gain functions it consumes and a basis for their span. Compare
the cost of transporting those expectations directly with the cost of full
posterior transport, using the existing gain and affine-score APIs.

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
