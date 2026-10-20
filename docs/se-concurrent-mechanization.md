# Concurrent sequential-equilibrium preservation

## Deliverable

The exact target is [`Vegas.ConcurrentRawSequentialPreservation`](../Vegas/Game/ConcurrentRawSequentialPreservation.lean).
This is a checked proposition, **not a proved preservation theorem**. It fixes the
concurrent graph, concrete phase runtime, reserved service law and economics
before quantifying over intended source sequential equilibria. The conclusion
preserves the joint law of original inputs, typed terminal state, public results
and the whole realized net payoff vector, with no exclusions or audit charges.
The initial law is arbitrary and correlated. There is no fixed-calendar target.

The external hypotheses are well-formed finite source data, complete pending
observation, bounded resources, a correlated reserved tape with bounded gaps,
timely deadlines, sufficient fresh candidates, state-based utilities and a global
exclusion floor, and authentic funded audit coverage. These are sufficient
conditions, not a claim of minimality or a chain implementation guarantee.
No posterior identity, counterpart, source cursor, gain comparison or consistency
sequence is a capstone assumption.

## Current proof boundary

**Contract checked; mathematical transport reviewed; Lean transport and clean
commitment gain open; concurrent preservation unproved.** Checked dependencies
do not close the remaining Lean obligations.

The [likelihood analysis](se-concurrent-likelihood.md) states the actual remaining
mathematical obligation. The [independent review](se-concurrent-likelihood-review.md)
records the accepted mathematical construction and its precise domain.
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

The owner has authorized workspace stabilization, the theorem contract,
mathematical review and code reduction. Report their outcome **before** beginning
the end-to-end mechanization. Mathematical review must either close the necessary
transport claim or name the precise remaining obstruction. A dependency build,
conditional helper or new module count is not a substitute.

Once authorized, mechanize the agreed missing transport and clean gain comparison,
then use the existing common-sequence, limit and audit APIs to prove the exact
capstone. Only that checked theorem closes concurrent preservation. Protect it
before broader assumption minimization or porting existing NE/nonconcurrent SE
to the shared phase runtime.
