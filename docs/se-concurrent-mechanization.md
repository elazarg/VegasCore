# Concurrent sequential-equilibrium preservation

## Deliverable

The exact target is [`Vegas.ConcurrentRawSequentialPreservation`](../Vegas/Game/ConcurrentRawSequentialPreservation.lean).
This is a checked proposition, **not a proved preservation theorem**. It fixes the
concurrent graph, concrete phase runtime, reserved service law and economics
before quantifying over intended source sequential equilibria. The conclusion
preserves the joint law of original inputs, typed terminal state, public results
and the whole realized net payoff vector, with no exclusions or audit charges.
The initial law has arbitrary correlation and finite support; binding types
are finite. Auctions with unbounded binding bid/value choices are outside this
contract.
There is no fixed-calendar target.

The external hypotheses are well-formed finite source data, complete pending
observation, bounded resources, one unconditional exogenous reserved tape prior
sampled for the entire execution, bounded gaps and timely deadlines, sufficient fresh candidates, state-based utilities and a global
exclusion floor, and authentic funded audit coverage. These are sufficient
conditions, not a claim of minimality or a chain implementation guarantee.
Tape coordinates may correlate across owners and time, but the prior is not
refreshed or selected from a public prefix at block entry. Scheduler posterior
updates condition the same sampled tape; adaptive block priors are not covered.
No posterior identity, counterpart, source cursor, gain comparison or consistency
sequence is a capstone assumption.

## Current proof boundary

**Contract and joint satisfiability checked; mathematical transport reviewed;
qualified transport, clean commitment gain and unconditional final SE open.**
Checked dependencies do not close the remaining Lean obligations.

The [concurrent hypothesis test](../VegasTests/ConcurrentRawHypotheses.lean)
discharges every operational, payoff and audit assumption together, and supplies
a source SE witness. Its actual concurrent graph has two simultaneously ready
owned Boolean bindings; its service supports both activation orders, with
nonconstant utility and a positive funded deposit. This establishes that the
contract's premises are jointly satisfiable, not preservation.

The [likelihood analysis](se-concurrent-likelihood.md) states the actual remaining
mathematical obligation. The [independent review](se-concurrent-likelihood-review.md)
records the accepted mathematical construction and its precise domain. These
are independent agent reviews and a root-agent model audit, not human review
or Lean verification.
The [code inventory](se-concurrent-code-inventory.md) identifies owning APIs and
which proposed intermediate statements exceed what the final gain proof needs.
The [reserved-service proposal](se-reserved-service-preservation.md) supplies
motivation and assumptions; the likelihood analysis supplies the detailed argument.

At a clean binding decision, the reviewed transport is the qualified
source measure: weighting actual native continuations by the clean binding gate
must give one scalar times the genuine source conditional law, uniformly over
legal proper typed insertions. The same construction must identify the actual
causal payoff continuation. This is a theorem to derive, never a premise to add.
Unqualified branches use their separate floor/reset comparison. A product law
against every full mechanical history is not required merely because an older
proof draft attempted it.

The mathematical derivation specifies the actual joint experiment,
its original initializer, source labels and archives; support and weights through
response/service/close cases; and normalization including zero mass. The physical
skeleton stops at the current binding close; later payoffs use a separate causal
kernel. Conditional laws given a supplied cursor establish neither the
coverage nor the weights of arbitrary source explanations of a native input.
The exact reviewed claim, rather than the stronger private draft, determines
the next mechanization boundary.

## Owning components

| Responsibility | Existing boundary |
| --- | --- |
| Intended and enriched source assessment | `IntendedPreservation`, `ProposalRecoveryEquilibriumConstruction` |
| Reserved service and resources | `ReservedEpochResources`, `ReservedEpochCompletion` |
| Original initialized laws and common sequence | `PhaseProposalInitializedTerminal`, `PhaseProposalInitializedLawError`, `PhaseProposalConsistentSequence` |
| Source reach factors and source information | `ProposalRecoveryPublicClassFactorization`, `ProposalRecoveryPublicClassConstancy`, `PhaseProposalNativeSourceInformation` |
| Actual local incentives | `PhaseProposalCurrentBindingGain`, `PhaseProposalPublicationGain`; clean binding remains open |
| Equilibrium limit and raw enforcement | `LocalSimulationLimit`, `PhaseOnePacketExtension` |

Detailed consumers and their actual hypothesis scopes are listed in the inventory.
Keep original initialization joint with outcomes and settlement; the convenient
raw readout wrapper alone drops a history coordinate needed by final assembly.

## Implementation discipline

Use ordinary in-tree modules and `lake build`. Do not maintain private compiler
provider registries, alternate runners or artifact-manifest verification systems.
Keep one proof representation for each justified interface. Merge focused
helper fragments into their owning mathematical component when doing so reduces
transport obligations. Remove unused constructions rather than retaining aliases.
Do not import old private proofs solely because they were checked in isolation.

Source language semantics, runtime transitions and the asynchronous checklist
obligations remain fixed. A change to external assumptions or target semantics
requires the owner's decision. Internal proof architecture may be simplified.
Use original correlated initializer atoms; retain canceled own failures, accepted
canceled foreign values, all proposals, exact addresses and actual raw aliases.
A factor one is not absence of a preparation lock. A physical failed receipt
is not automatically a particular source failure label.

`Paper.lean` remains a short paper-facing interface. Configure Lean options
centrally. Stable verified public checkpoints are committed and pushed; local
handoff notes and research archives are not committed.

## Completion gate

Mechanize the agreed transport and clean gain comparison, then use the existing
common-sequence, limit and audit APIs to prove the exact capstone. Keep its
external hypotheses fixed. If the mathematical argument appears incorrect,
stop implementation and report the precise issue.

Track the remaining obligations directly:

| Required result | Checked status |
| --- | --- |
| Actual native qualified payoff law | Native experiment, original tape posterior and initialized clean-close source word checked. Common source site, weight identity and causal payoff matching open. |
| Clean binding deviation bound | Query stability, query nonreuse, full native value-table first-close law and same-table completed values checked. Waiting payoff bound and clean gain open. |
| Full raw concurrent SE preservation | Joint-law, limit and raw-audit assembly checked conditional on local gain comparisons. That comparison premise remains open. |

The checked reductions are in the [qualified experiment](../Vegas/Game/PhaseProposalQualifiedBinding.lean),
[binding comparison](../Vegas/Game/PhaseProposalCleanBindingGain.lean) and
[conditional assembly](../Vegas/Game/ConcurrentRawEquilibrium.lean) components.
None proves the unconditional preservation contract.

Partial lemmas and conditional composition do not close these rows. State the
actual unproved premises of partial results. Review the shared interfaces before
delegating implementation; add a helper only for an identified consumer. Keep
probability, incentive and final composition work in cohesive owning components,
with one root-controlled in-tree build. Do not count new code as progress.

Only the checked capstone closes concurrent preservation. Protect it before
broader assumption minimization or porting existing NE/nonconcurrent SE to the
shared phase runtime.
