# Correlated initial priors and sequential-equilibrium preservation

The private-input independence assumption has two distinct uses in the
recovery/sequential-phase proof: **legal support for spliced histories**, and
**a constant change of prior weight across histories**. The second use proves
more than the downstream incentive argument needs. An existing common-best
component theorem offers a plausible weakening for correlated priors with
adequate support. Priors for dealing cards also challenge the first use;
covering them requires a different support argument or avoiding splicing.

This is a research analysis, not a checked weakening of a preservation theorem.
The paper accurately states the current hypothesis. The concurrent theorem
already permits correlated initial laws under its different service and
observation assumptions. Neither observation settles whether the recovery
theorem remains true after deleting independence while keeping its other
hypotheses and its selected-equilibrium/joint-law conclusion.

## What the assumption says

Fix player \(i\). Write an initial state as \((A,B)\), where \(A\) contains
that player's private inputs and initial commitments and \(B\) contains every
other cell. Let \(Z=f(B)\) be the specified public initial signal. On a signal
fiber, write \(p_z(a,b)\) for the nonnegative joint masses. The condition in
[`Vegas.SourceProgram.Setup.PrivateInputsIndependentGiven`](../Vegas/Source/PrivateInputsIndependent.lean)
is precisely

\[
 p_z(a,b)p_z(a',b')=p_z(a,b')p_z(a',b)
 \quad\text{for all }a,a',b,b'.
\]

Thus every two-by-two minor vanishes. On a positive-mass finite fiber, choose
an entry \(p_z(a_0,b_0)>0\). The identity gives

\[
 p_z(a,b)=
 \frac{p_z(a,b_0)p_z(a_0,b)}{p_z(a_0,b_0)}.
\]

Normalizing gives \(A\perp B\mid Z\), including the possibility of zero
entries. In particular, positive support on that fiber is rectangular. Null
signal fibers impose no conditional-probability requirement. This is
independence from the **whole remainder**, not pairwise independence from each
other player's input.

There is a useful simplification of the existential public-signal wording.
Let \(C\) be the complete public initial-input vector and \(B=(C,D)\).
If \(A\perp(C,D)\mid f(C)\), conditioning further on \(C\) gives
\(A\perp D\mid C\). Conversely, that last condition supplies an allowed
signal by choosing \(Z=C\). Therefore existence of a suitable public signal
is equivalent, in this finite model, to independence conditional on the
entire existing public initial input. A more informative **existing** public
signal may help an instance satisfy the condition; inventing a new public
latent variable changes the game. This equivalence is an elementary deduction
here, not a cited Lean theorem.

[`Vegas.SourceProgram.Setup.PublicInitialSignal`](../Vegas/Game/OnePacketPublicInitialSignal.lean)
requires the signal to be determined by public compiled initial inputs.
[`Vegas.public_signal_preserved`](../Vegas/Game/OnePacketPublicInitialSignal.lean)
establishes its invariance under hidden-cell splicing. The late key retains
those public inputs, but deliberately omits other private information; see
[the late-key definition](../Vegas/Game/OnePacketTrembles.lean).

## Where the proof actually needs it

| Obligation | Existing proof | What a weakening must supply |
|---|---|---|
| A swapped initial state is possible | [`Vegas.SourceProgram.Setup.splice_mem_support`](../Vegas/Source/PrivateInputsIndependent.lean), used by [`Vegas.drawn_splicePoint`](../Vegas/Game/OnePacketSplicePoint.lean) | Supported witnesses for the actual history repairs; no probability equality is needed for this step |
| Swapping multiplies every relevant history weight by one scalar | [`Vegas.ownerSwap_priorScaled`](../Vegas/Game/OnePacketConditionalPrior.lean) | A constant ratio, or an explicit nonconstant likelihood and control of its effect |
| Two late sites with the same key have the same base operational-record law | [`Vegas.ownerSwap_baseLawAgrees`](../Vegas/Game/OnePacketOwnerKeyed.lean), specialized in [the late-site adapter](../Vegas/Game/OnePacketOwnerKeyedLate.lean) | Agreement or suitable inequalities for the observables actually used by the incentive argument |
| A repaired responder is forced at its actual information state | [`Vegas.forcedAgent_of_splice`](../Vegas/Game/OnePacketSpliceForced.lean) | A legal alternative witness preserving the required observations and forced behavior |
| A common timing component is near-best at every pooled site | [The late-record construction](../Vegas/Game/OnePacketLateRecords.lean) and [common-value consumer](../GameTheoryExtensions/Analysis/Protocol/AffineKeyedPools.lean) | A common near-best component; equality of full record laws is one sufficient producer |

The base-law theorem is conditional on well-formedness, coverage of binding
inputs, finite histories, debt-free sites, and an owner swap that maps the
information states. It permits arbitrary operational-record weighting and
payoffs. The swap preserves the other history factors and the operational
record; a common positive prior ratio then cancels on normalization. It does
not claim that independence alone identifies arbitrary runtime posteriors.

This separation matters: full support can replace the support-closure use,
but full support does not make likelihood ratios constant. Conversely,
weakening the record-law conclusion does not discharge the responder-repair
support obligation.

## First target: a common best choice, not a common full belief

Let \(V_s(o)\) be the actual continuation value of component \(o\) at site
\(s\). The useful local target for each pool \(k\) is

\[
 \exists o_k\;\forall s\text{ in pool }k\;\forall o,
 \qquad V_s(o)\le V_s(o_k)+\eta.
\]

For \(\eta=0\), this says the sites have a common optimizer. Their beliefs,
values, and even rankings of other options may differ. The existing theorem
[`GameTheory.Protocol.InformationModel.memberGain_le_of_common_best`](../GameTheoryExtensions/Analysis/Protocol/SuccessRanking.lean)
already turns this premise, **together with pooled optimality, the component
mixture representation, and its finite-horizon/recall hypotheses**, into a
member gain bound of the number of information agents times \(\eta\).
It bounds deviations represented by those components. The surrounding
completion argument must still cover all actual legal deviations.

The more structured existing producer
[`GameTheory.Protocol.InformationModel.freeKeyed_memberGain_le_of_common_values`](../GameTheoryExtensions/Analysis/Protocol/AffineKeyedPools.lean)
accepts actual values within error \(e\) of

\[
 V_s(o)=a_i+q_k(o)(c_s-a_i),\qquad c_s\ge a_i,
\]

and obtains a common near-best option from an optimizer of \(q_k\).
The nonnegative slope is essential. Correlation could be harmless if it
changes continuation values or irrelevant records while preserving this
ordering. A concrete dominance property of the actual service is another
possible producer. Neither property follows merely from full support or
from honest executions.

For an SE limit, the bound must tend to zero at every required information
site along one common fully mixed assessment sequence. An arbitrary fixed
small correlation error is not enough. A strict incentive margin or a
one-sided gain inequality can sometimes absorb a nonvanishing perturbation,
but the margin must be established for the actual choices and sites.

**Recommended first experiment:** retain the existing key and component
construction, use a correlated rectangular-support prior, and derive the
common-best premise directly from actual continuation gains. Independently
replace each support-only invocation by its supported-splice hypothesis.
Success would establish a genuine, limited weakening without a new pooling
abstraction. Merely assuming the desired common-best conclusion at the
preservation boundary would expose an interface, not solve the application.

## How a correlated prior changes the comparison

Suppose a legal history bijection changes the owner's initial cells from
\(a\) to \(a'\), preserves the other likelihood factors, and both pulled-back
laws have the same positive support. Its prior ratio is now

\[
 w(b)=\frac{p(a',b)}{p(a,b)}.
\]

Writing \(\mu\) for the normalized law at the first site, the pulled-back
second law is \(\nu(b)=w(b)\mu(b)/\mathbb E_\mu w\). Consequently,

\[
 \mathbb E_\nu g-\mathbb E_\mu g
 =\frac{\operatorname{Cov}_\mu(w,g)}{\mathbb E_\mu w}.
\]

Independence makes \(w\) constant. A weaker exact condition is zero covariance
only for the relevant gain observables. For preserving nonpositive gains,
nonpositive covariance suffices. If the transported continuation itself
changes from \(g\) to \(g'\), add
\(\mathbb E_\mu[w(g'-g)]/\mathbb E_\mu w\); equal likelihood behavior does
not identify different continuation payoffs.

This algebra has existing channel-based consumers:
[`GameTheory.Math.Probability.expect_kernelPosterior_sub_expect`](../GameTheoryExtensions/Math/Probability/KernelPosteriorGain.lean),
[`GameTheory.Math.Probability.expect_kernelPosterior_nonpos`](../GameTheoryExtensions/Math/Probability/KernelPosteriorGain.lean),
and [observation-local gain transport](../GameTheoryExtensions/Analysis/Protocol/ObservableGainTransport.lean).
A prior ratio is not automatically a channel probability: it can exceed one.
For finite support it can be scaled by a positive upper bound into a binary
observation channel, without changing its normalized posterior. The required
adapter must prove the actual history identity, support, positive denominator,
and continuation correspondence. General infinite-space reuse also needs the
relevant integrability assumptions.

This suggests testing covariance against a closed family of continuation
gains, rather than every record indicator. Agreement on all indicators in a
finite space would recover equality of the entire law and lose the weakening.
The existing [observable-space machinery](se-preservation-constructive-directions.md)
explains the additional closure obligations under decisions and conditioning.
Any quantitative bound must be conditional and uniform where the SE argument
needs it; small unconditional error can be amplified at a rare site.

### A small diagnostic that separates the issues

Consider two hidden bits and no public signal:

| \(p(A,B)\) | \(B=0\) | \(B=1\) |
|---|---:|---:|
| \(A=0\) | 0.4 | 0.1 |
| \(A=1\) | 0.1 | 0.4 |

Support is rectangular, but the cross products are \(0.16\) and \(0.01\).
The probability of \(B=0\) conditional on \(A\) is respectively \(0.8\)
and \(0.2\). If option zero succeeds exactly at \(B=0\), and option one
exactly at \(B=1\), the two types have opposite unique optimizers. A single
pooled option cannot be within \(\eta<0.6\) of optimal for both. Even a
common randomized option has worst-type regret at least \(0.3\).

The change from the first conditional law to the second has
\(w=(1/4,4)\), \(\mathbb E_\mu w=1\), and covariance \(-0.6\) with
\(1_{B=0}\), exactly reproducing the conditional-value difference.
If instead one available option pointwise dominates the others, the same
correlated prior permits a common optimizer. Thus independence is stronger
than this local decision property, while positivity alone is insufficient.

For dealing two distinct cards, use masses \(1/2\) at \((0,1)\) and
\((1,0)\). Splicing produces \((0,0)\) or \((1,1)\), both impossible.
This defeats the fixed-rest support construction before likelihood comparison.
These are elementary diagnostics of proof mechanisms, **not counterexamples
to Vegas SE preservation**. A counterexample to the latter must satisfy all
remaining physical hypotheses and exclude every preserving target SE, not
just the existing pooled construction.

## Correlation without splicing: retain the joint initial draw

The concurrent proof offers a more ambitious direction. In its
[source-cylinder factorization](se-concurrent-likelihood.md), a source prefix
fixes the whole initial draw. The proof retains that joint prior mass and
sums unused strategy tails using normalized kernels. It does not factor the
initializer into player marginals. This avoids the need to exchange one
player's private cells while freezing all others.

The corresponding research target for recovery is an unnormalized identity
for the joint law of the initial draw, source history, and runtime observations,
followed by conditioning on the player's **actual** information. Such an
identity could preserve card correlations automatically. Conditioning on the
whole draw as a proof variable is legitimate for linear probability identities;
selecting a player's action using that unobserved draw is not. Policies must
still factor through their permitted information.

The concurrent construction also uses a reserved service, an input-independent
service tape, and complete pending observation. Its probability accounting
does not establish the missing recovery-history factors or information
correspondence under the recovery theorem's service. Reusing the accounting
idea requires locating exactly which local identities survive, including
off-path sites and unilateral deviations. The initialized joint outcome and
payoff law remains a separate obligation from local incentive inequalities.

## Couplings: a precise feasibility test, not an automatic replacement

For finite laws \(\alpha,\beta\) and a proposed relation \(R\) between
histories, a coupling supported on \(R\) exists exactly when

\[
 \alpha(S)\le\beta(R(S))\quad\text{for every subset }S.
\]

This is the finite form of the relation-coupling criterion in Leskelä's
Theorem 2.5, extending Strassen's formulation. Leskelä also gives conditions
for lifting such relations through kernels and finding preserved subrelations.
[Stochastic relations of random variables and processes](https://math.aalto.fi/reports/a554.pdf).

Our application would choose \(R\) to preserve the required player observation,
legal response transport, and appropriate continuation values. But a coupling
of the two conditional initial laws that requires the **entire rest of the
state to agree** exists only if their rest-state marginals agree. If required
for every pair of own types at a public signal, that is precisely the
independence restriction again. Randomizing the current fixed-rest swap does
not evade it.

A weaker relation may work. A useful finite test is to calculate a coupling
or a violating subset for the exact operational relation, then check whether
the relation survives every relevant response kernel. Whole-deck relabeling
can preserve a card prior, but it need not preserve an arbitrary source
strategy, payoff, or opponent observation. A symmetry argument must establish
those equivariance hypotheses; it cannot silently restrict the source SE
whose law is being preserved. Couplings for separate sites must also fit the
one common consistency construction.

## What the information literature contributes

**Common information and prescriptions.** Nayyar, Mahajan and Teneketzis
reformulate a decentralized team problem using a coordinator who observes
common information and chooses functions from private information to actions.
The private observations need not become public. This suggests representing
type-dependent timing by legal prescriptions while retaining the joint prior.
Their result is for team control; it does not provide strategic obedience or
SE preservation for Vegas.
[Decentralized Stochastic Control with Partial History Sharing](https://cim.mcgill.ca/~adityam/projects/info-structures/journal/partial-sharing.pdf).

The strategic extension by Nayyar, Gupta, Langbort and Başar constructs common
information based Markov perfect equilibria under additional assumptions,
including strategy-independent common-information beliefs. Timing can signal
private information, so that assumption must be checked, not inferred from
having a common-information state.
[Finite games with asymmetric information](https://arxiv.org/html/1209.3549).

**Sufficiency relative to incentives.** Bergemann and Morris characterize
Bayes-correlated-equilibrium outcomes and compare information structures by
individual sufficiency. This gives a precise incentive-oriented alternative
to demanding that entire private types be independent. Their theorem concerns
static Bayesian games and sets of outcomes under information expansions; it
does not transport a selected sequential equilibrium through a runtime.
[Bayes correlated equilibrium and the comparison of information structures in games](https://economics.mit.edu/sites/default/files/publications/paper_79_bce.pdf).
For dynamic SE, the [survey's USI/MSI discussion](se-preservation-research-survey.md#sufficient-information-and-preservation-of-se-payoffs)
states the stronger policy-dependent factorization and the remaining gap to
the selected initialized joint law.

**A private posterior signature is a possible key refinement.** On finite
positive type fibers, group own types by their conditional law of the rest
given the existing public input. Rows within a group are proportional, even
if the entire prior is not a product. This is our proposed application of
sufficiency, not a cited preservation theorem. The statistic is computable
from the player's own type and common prior, but it is private. It cannot
replace the public signal in the current theorem. Refining the timing key by
it allows additional signaling and requires new pooled-completion, actual
posterior, and consistency proofs. An initial posterior signature also need
not summarize the later posterior after strategic observations. Refining all
the way to full information merely removes the comparison problem; it does
not establish the equilibrium or its preserved law.

Likewise, expressing a finite correlated prior as a mixture of product priors
does not solve the problem. Publicly revealing the mixture component changes
information. Keeping it latent requires one legal policy construction across
components, rather than selecting a hidden-component-dependent policy.

## Ownership and useful next results

| Owner | Proposed work | Evidence that would make it useful |
|---|---|---|
| Vegas | Separate supported-splice premises from constant prior scaling; produce common-best or signed-gain bounds for a correlated rectangular-support example | An actual recovery consumer with all legal deviations, conditional errors, consistency, and the selected joint law |
| Vegas | Carry the original joint prior through source/runtime history identities, reusing concurrent accounting where justified | A supported nonrectangular prior, such as a finite card deal, under explicitly stated service/observation assumptions |
| GameTheory / local extensions | Reuse common-best, posterior covariance, and existing continuation-observable APIs; add a finite relation-coupling adapter only if a concrete consumer needs one | A reusable theorem whose premises are produced by a runtime, rather than a wrapper assuming preservation |
| Multitubes | Consider a relation-supported coupling or observable/gain-preserving transport example | A genuinely weaker relation that composes and has an application; no dependency or theory rewrite follows from this survey |

The best first target is the common-best route with rectangular support. The
joint-prior route is more likely to cover unrestricted correlations, but its
operational and information adapters are substantial. A failed common-best
example or a failed coupling should be reported at that exact scope. Neither
is a refutation of the unchanged recovery theorem without independence.

## Implementation backlog

**Status: deferred pending research on the intended ledger information boundary.**
The concurrent theorem's complete pending observation is not an accepted
substitute for ledger-based public information and explicitly permitted private
observations. Its archive reconstruction does not establish that the resulting
strategies are legal after pending traffic is hidden. The active implementation
work is the source/phase operational-information correspondence and Nash port;
the assumption-weakening experiments below remain research proposals.

**Priority:** a bounded research track after the outstanding
[source/phase operational-information and Nash port](source-phase-correspondence.md).
The support-only extraction can run independently where its files do not overlap
that port. Assumption weakening is not an exit criterion for
[semantic consolidation](consolidation.md), and these proposals do not change
the fixed asynchronous target or its checklist. Work belongs in Vegas and local
GameTheoryExtensions; the separate GameTheory repository stays unchanged.

- [ ] **Separate the support premise at actual consumers.** Identify the
  splices used by history repairs, state exactly their required support closure
  within public-signal fibers, and derive it from the existing independence
  hypothesis. Generalize support-only callers such as `Vegas.drawn_splicePoint`
  while retaining the stronger premise where prior-weight identities need it.
  Acceptance requires an actual repaired-history consumer and a correlated,
  rectangular-support instance that violates the independence identity.
  The existing preservation statements must still be checked as instances.
  This is a useful proof-interface improvement; it does not by itself weaken
  the SE theorem's assumptions.

- [ ] **Produce common near-best choices for an actual correlated runtime.**
  Keep the existing timing key and component construction. Use a finite
  rectangular-support prior whose correlation changes actual posteriors, with
  competing continuation choices and nonconstant payoffs. Prove the required
  common-best or signed-gain inequalities from the program and physical
  service conditions, using the existing common-best and covariance APIs.
  Account for the actual information sites, represented deviations and pooled
  optimality; an assumed common-best hypothesis at the preservation boundary
  is not an application. For an SE limit, any remaining error must vanish
  uniformly where required along one common consistent assessment sequence.
  A checked local consumer is an intermediate result, not a full preservation
  theorem.

- [ ] **Carry the weaker premises through the preserved equilibrium and law.**
  If the local experiment succeeds, derive all remaining repair, rationality,
  consistency and initialized-law obligations. Retain the supplied deadlines,
  full raw-history physical service, legal whole-policy deviations, audit
  funding, no-exit/no-charge guarantees and exact selected joint readout/payoff
  law. Acceptance as a weakening requires both the existing independent-prior
  theorem and a non-independent instance to follow from the resulting API.
  Any additional program or service restriction must be explicit: a theorem
  for a different restricted environment is a separate sufficient condition,
  not automatically a weakening of the present theorem. A larger class is
  established only to the extent its hypotheses have concrete producers.

- [ ] **Investigate nonrectangular priors through joint-draw transport.**
  Use a finite card deal to test whether an operational correspondence can
  preserve the original joint draw without fixed-rest splicing. Start from
  the existing initialization and initial-noise laws, then prove the missing
  continuation and actual-information identities; those initial-step results
  alone do not supply conditional beliefs at later or off-path decisions.
  This route should follow the relevant source/phase correspondence work and
  need not depend on success of the common-best experiment. A coupling adapter
  or private key refinement is justified only by a concrete consumer, with
  legal policy transport and a common consistency construction.

Run each bounded experiment on its own branch. Merge a checked reusable
improvement or a genuinely wider preservation result; otherwise document the
precise obstruction and remove unused scaffolding. In particular, the
opposite-optimizer diagnostic rules out that common-choice construction for
that example, not every preserving target equilibrium. No new general pooling,
coupling or information-compression framework is required before these tests.

Bibliography entries are in `overleaf/vegas-paper.bib`:

| Key | Role |
|---|---|
| `Leskela2010StochasticRelations` | Relation-supported couplings and kernel preservation |
| `Strassen1965Marginals` | Foundational prescribed-marginal coupling result |
| `NayyarMahajanTeneketzis2013` | Common-information prescriptions in team control |
| `NayyarEtAl2014CommonInformation` | Strategic common-information construction and its extra hypotheses |
| `BergemannMorris2016BCE` | Incentive-oriented comparison of Bayesian information structures |
| `TangSubramanianTeneketzis2026` | Dynamic information compression and SE-payoff preservation |
