# Documentation

The [README](../README.md) states the checked results. Design notes describe the
code as it is. Research notes give arguments, candidate models and
counterexamples; a statement in a research note is a paper argument unless it
cites a Lean declaration. Links into the `research-tree` tag point at retired
code, which is checked at that tag only.

## Design

- [Semantics, compiled output and enforcement](semantics-and-enforcement.md):
  the layers from source semantics to chain model, the three compiled
  contracts, how each treats deviations, and proposals for one contract.
- [Source semantics](source-semantics.md): the source language, its failures,
  player information and limits.
- [Typed event graphs](event-graph-design.md): the compiler's target and its
  execution modes.
- [Compilation boundary](compilation-design.md): the pending-message
  application, clients and what a compiler result must prove.
- [Ideal commitment and readiness capabilities](ideal-commitment-capabilities.md):
  the ideal commitment and readiness interfaces and what realizing them needs.
- [Module architecture](module-architecture.md): layers and the modules with a
  description.
- [Consolidation ledger](consolidation.md): the reduction plan, findings,
  measurements and the index of retired results.
- [Proof review and mathematical mining](proof-review.md): codebase coverage,
  checked experiments, compression candidates and stronger nearby results.

## The concurrent theorem

- [Concurrent sequential-equilibrium preservation](se-concurrent-mechanization.md):
  the contract, its hypotheses and the structure of the proof.
- [Code inventory](se-concurrent-code-inventory.md): the contract's components
  and the APIs the proof uses.
- [Qualified likelihood and causal payoff](se-concurrent-likelihood.md), its
  [review](se-concurrent-likelihood-review.md) and the
  [replay analysis](se-concurrent-replay-analysis.md): the mathematical argument
  the proof follows.
- [Reserved shared service](se-reserved-service-preservation.md): the argument
  for the reserved-epoch service and its scope.
- [Realistic assumptions](se-preservation-assumptions.md) and
  [network assumptions](se-network-assumptions.md): which network models meet
  the hypotheses.
- [Timing obstruction](se-concurrent-timing-obstruction.md): penalties alone do
  not ensure concurrent preservation.
- [Private-seed signalling](se-private-seed-signalling.md) and
  [signalling with a large exclusion loss](se-strong-exclusion-signalling.md):
  counterexamples behind the exit-payoff assumption.
- [Commit–reveal programs on an asynchronous ledger](se-preservation-commit-reveal.md)
  and its [mathematical audit](se-preservation-math.md): the route for an
  arbitrary asynchronous ledger.

## Asynchronous service and turn-based play

- [Arbitrary-builder checklist](se-async-checklist.md): obligations and evidence
  for preservation under timely builders.
- [Preservation under asynchronous service](se-schedule-generalization.md):
  target, semantics and proof route.
- [What is known in the standard runtime](standard-runtime-se-status.md).
- [Two small calculations](se-small-models.md),
  [two sources and the forfeit pass](se-two-sources.md) and
  [single-slot attempts](single-slot-attempts-se.md).
- [Checked boundaries for realistic preservation](se-runtime-refinements.md).

## Late openings and timing

- [Sequential equilibria with late sends and leaked openings](open-problem-late-turn-equilibria.md):
  the late-leak counterexample behind the Paper non-preservation theorems.
- [Runtime features versus the late-leak obstruction](runtime-features-vs-late-leak.md).
- [Late openings in the actual runtime](actual-runtime-late-opening-analysis.md).
- [Propagation lag](propagation-lag-se-boundary.md),
  [concurrent immutable disclosure](concurrent-disclosure-se-boundary.md) and
  [checking only equilibrium-path behavior](honest-disclosure-preservation-boundary.md):
  boundaries of preservation.
- [A fully public disclosure phase](full-public-disclosure-phase-preservation.md)
  and [composition at public subgames](public-reset-phase-se-preservation.md):
  positive results under complete observation.

## Preservation in general

- [What equilibrium preservation can support](equilibrium-preservation-landscape.md)
  and [how close general preservation is](general-se-preservation.md).
- [Public stochastic scheduling](public-scheduling-se-preservation.md): the
  argument behind `Vegas.Paper.public_scheduling_sequential_equilibrium`.
- [Weak PBE across a clean restriction](weak-pbe-restriction-preservation.md),
  [approximate SE under vanishing noise](noisy-runtime-approximate-se-preservation.md)
  and [failing honest publication](probabilistic-runtime-preservation.md).
- [Runtime contracts for an abstract source language](se-preservation-runtime-alternatives.md),
  [a concrete blockchain target](blockchain-se-preservation-target.md) and
  [a positive path through the runtime](actual-runtime-se-positive-path.md).
- [Abstraction, leaks and cheap talk](abstraction-and-cheap-talk.md).

## Ledger interfaces

[Ledger requirements for rational commit–reveal games](commit-reveal-research/README.md)
indexes a separate study of candidate ledger interfaces and what each supports.
