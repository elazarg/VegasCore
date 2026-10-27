# Primary sources and what they do not establish

These references help formulate the research questions. None proves that a
particular deployed ledger implements the interfaces in this directory.

## Cryptographic representations of abstract games

Halpern, Pass and Seeman formulate representation of a finite extensive-form
game by computational games. Their conditions include history structure,
payoffs and simulation of efficient unilateral deviations. They prove
preservation into their computational Nash and sequential-equilibrium notions.
This separates cryptographic implementation from abstract strategic analysis;
our extra transport decisions and their observations still need adapters.
[Computational Extensive-Form Games](https://arxiv.org/abs/1506.03030).

The [preservation track](preservation-and-robustness.md) distinguishes their
computational definition from ordinary finite-game sequential equilibrium
under ideal primitives. The theorem should not be cited as if encryption alone
established our physical runtime's rationality preservation.

## Network timing and consensus

Dwork, Lynch and Stockmeyer distinguish known synchronous message bounds from
partial synchrony, including known bounds that hold only after an unknown
stabilization time. This matters when a source decision has a physical deadline:
eventual communication bounds do not themselves give a predetermined completion
deadline for a particular transaction.
[Consensus in the Presence of Partial Synchrony](https://groups.csail.mit.edu/tds/papers/Lynch/MIT-LCS-TM-270.pdf).

The inference about a transaction deadline is ours; the cited paper supplies
the network and consensus definitions. Transaction selection, fee competition,
admission capacity and decryption availability are further assumptions.

## Sequential rationality

Kreps and Wilson introduce sequential equilibrium for extensive-form games,
including optimal continuation decisions and consistent beliefs at off-path
information sets. This motivates keeping conditional incentives and a common
belief-consistency construction separate from initialized outcome matching.
[Sequential Equilibria](https://www.jstor.org/stable/1912767).

## How to add further sources

The [SE-preservation research survey](../se-preservation-research-survey.md)
connects information compression, continuation-gain equivalence, observation
likelihoods, consistency certificates, and scheduler noninterference to the
existing proof interfaces. It also examines Multitubes transport morphisms,
UniformEquilibrium's quitting-game debt and finite Markov potentials, and
rational certificate checkers. The proposals distinguish Multitubes theory
and examples, GameTheory foundations, local protocol bridges, and Vegas
implementations, with explicit package boundaries and missing hypotheses.
The [constructive directions](../se-preservation-constructive-directions.md)
connect Reny's affine-ray lemma, weighted-automata equivalence, and signed
continuation residuals to proposed certificate producers and stronger consumers.
The [constructive implementation ledger](../se-preservation-constructive-experiments.md)
distinguishes the checked general results and concrete consumers from the
remaining completeness and runtime representation work.
The [correlated-prior analysis](../se-correlated-prior-research.md) traces the
private-input independence hypothesis to supported history repairs and common
prior ratios, then compares common-best incentives, joint-prior accounting,
couplings, and common-information prescriptions as possible weakenings.
The [private-mempool analysis](../se-private-mempool-research.md) separates the
concurrent proof's archive and deterministic-observation dependencies, compares
real observation interfaces, and develops mixture-based preservation routes
and precisely scoped impossibility tests.
Its [mathematical companion](../se-private-mempool-mathematics.md) proves finite
private-observation preservation and coarsening obstructions, develops common
consistency constructions, and relates exact obstruction search to
semialgebraic equilibrium theory. The
[compiler analysis](../se-private-mempool-compilation.md) compares rollback
with absorbing failure and explains the incentive and payout requirements.
The [ledger-publication construction](../se-private-mempool-proof-routes.md)
isolates the late-opening archive obstruction and the failure of arbitrary
post-exclusion continuation selection. It gives a finite hand preservation
proof for deterministic sample padding, using causal private-observation
simulation and a counted candidate mask, followed by the existing raw audit
extension. The compiler and proof adapters remain unmechanized.
Its detailed specifications derive the
[source transformation and timing](../se-publication-padding-mathematics.md),
[conditional probability and incentive transfer](../se-publication-transfer-mathematics.md),
[actual counted-menu adapter](../se-publication-native-adapter.md), and
[audit and delayed-authorization boundaries](../se-publication-audit-boundary.md).
They separate the mathematical private-reception result from the backend's
bounded recording, authentic evidence collection and retained-signature duties.
The [scheduled-service benchmark](../se-publication-scheduled-benchmark.md)
instantiates these duties under a fixed public sender calendar and full queue
clearing. Those are stronger network premises, not compiler choices, so this
benchmark does not establish the intended asynchronous implementation.
The [asynchronous analysis](../se-asynchronous-preservation.md) separates
contract-controlled cooldowns from transaction inclusion, derives a proof-only
past-information refinement, and identifies the remaining timing, replay and
audit obligations. Its bounded-inclusion example refutes a prompt-send proof
step, not concurrent preservation itself. The
[timing module](../se-asynchronous-timing-policy.md) proves preservation of
source comparisons by optimal private timing under explicit success/floor
separation. The [audit module](../se-asynchronous-audit-feasibility.md) derives
portable evidence, reporting incentives, a report-all completion and a scoped
impossibility result for unauditable verifiable disclosure; it cites the
transaction-pool implementation and signature/relay standards separately
from the mathematical liveness assumptions.

Use papers, official protocol specifications or implementation documentation.
Record the precise property supported: cryptographic confidentiality, finality,
admission, release, observation or availability. Distinguish transaction
proposal from final admission, and disclosure authorization from receipt of
plaintext. An implementation example is evidence for a component, not a proof
of the combined game interface.

Hardware confidentiality, committee honesty and availability, and computational
cryptographic security must be named separately. Idealizing one assumption
does not idealize the rest. The present round makes no new deployment claim.
