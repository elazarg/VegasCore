# Sequential equilibrium on the phase runtime

The target is the existing intended-game preservation guarantee on
`phaseApplication`, instantiated with the sequential compiled graph and singleton
phases. The phase executor, packet observations, retirement archive and permanent
exclusion semantics stay as implemented. The concurrent reserved-tape theorem
keeps its existing maximal-phase plan.

The desired conclusion is a sequential equilibrium against whole-policy
deviations, preserving the joint typed readout and realized settled payoff law
and charging nobody on its paths. A physical state comparison alone does not
establish this conclusion.

## Assumptions to retain

The source setup is well formed, with private inputs independent conditional on
an observable public initial signal. The source premise is an equilibrium of the
intended game. The exit payoff is at most every intended terminal payoff, and
utility has the existing lower and upper bounds, including the treatment of
unfinished executions as zero.

The builder must supply the counterparts of opportunity, protected inclusion and
completion on the actual phase runtime. These properties need proofs or explicit
primitive phase-runtime definitions; they cannot be inferred from the existence
of a singleton plan. The old opportunity and inclusion assumptions quantify over
all legal recovery traces, including traces after exclusion. Completion covers
all legal horizon-terminal states. The reaction and inclusion bounds must sum to
strictly less than each owned event's deadline.

The response catalogue covers output and input values, with candidate capacity
strictly greater than each player's binding-event count over the whole program.
Singleton phases do not reduce that requirement to a per-phase bound. Raw-menu
extension retains the multiplicative funding condition: the payoff spread is at
most observation rate times delivery rate times deposit. Neither rate is divided
out or silently assumed positive.

## Checked interfaces

- [SequentialRuntimePhases](../Vegas/Game/SequentialRuntimePhases.lean) constructs
  the actual singleton plan from the sequential compiled program and proves
  event membership, ownership, readiness confinement and settlement quiescence.
  This instantiates the existing phase executor rather than defining a new one.
- [PhaseSingleton](../Vegas/Pending/PhaseSingleton.lean) proves that a fresh miss
  in a singleton commitment phase leaves no surviving owner to retry. Settlement
  keeps the generation unchanged for lists with singleton commitment phases.
- [PhaseSingletonRebuild](../Vegas/Pending/PhaseSingletonRebuild.lean) proves exact
  physical-state equality after rebuilding one automatically completed singleton,
  under native invariance, unique readiness and alignment of the saved config and
  accepted handles. The result retains candidates, clock and activation metadata.
- [PhaseSingletonTransition](../Vegas/Pending/PhaseSingletonTransition.lean)
  applies the rebuild comparison to the actual due-expiry kernel, retaining the
  failed endpoint in the archive and advancing to the remaining phase suffix.
- [PhaseDrainCorrespondence](../Vegas/Pending/PhaseDrainCorrespondence.lean)
  identifies phase settlement with the global recovery drain when checkpoint
  exclusion is unchanged, readiness is unique and the endpoint is globally
  quiescent. The proof concatenates actual automatic-completion traces.
- [PhaseClearMetadata](../Vegas/Pending/PhaseClearMetadata.lean) proves on every
  legal raw history that empty exclusion implies generation zero and an empty
  archive. Consequently a nonempty actual archive certifies public exclusion.
- [PhaseRecoveryInformation](../Vegas/Game/PhaseRecoveryInformation.lean) projects
  actual local views, recall, packet identities and receipts to recovery
  information without consulting the builder's hidden history.
- [PhaseRecoveryMenuProjection](../Vegas/Game/PhaseRecoveryMenuProjection.lean)
  proves raw bounded-menu agreement and commutation of existing operational
  normalization with this projection. The normalized phase raw menu agrees with
  the recovery canonical menu; the one-packet count filters remain to compare.
- [RecoveryOnePacketPreservation](../Vegas/Game/RecoveryOnePacketPreservation.lean)
  exposes intended-to-one-packet SE preservation and its joint base-payoff/readout
  law without an audit backend or funding premises. The full recovery raw
  theorem instantiates this result and the existing raw-extension theorem.

These are supporting theorems. They do not prove the target preservation theorem
or close an arbitrary-builder checklist obligation.

## Information and continuation obligations

The phase observation contains retired public snapshots, including their past
clocks. The forced-exit observation exposes the current recovery state and own
recall. Forgetting phase metadata gives a candidate local projection; reconstructing
all phase information from the old input requires a separate proof. Final-state
equality does not supply it.

The existing recovery construction offers a more flexible seam: after any public
exclusion every remaining player's decision agent belongs to a free completion
pool. A phase proof can therefore try to reproduce the source comparisons on
clear inputs and complete the richer post-exclusion game rationally. It must use
one common fully mixed approximation and its Bayes-consistent limit, rather than
selecting unrelated best responses at separate information sets.

The remaining proof needs actual reachable frontier alignment, operational
transport through submissions, inclusion, expiry and automatic cascades, legal
one-packet choice transport, and the clear-input posterior and continuation-gain
comparisons. The recovery menu normalizes aliases, whereas the phase one-packet
menu filters the raw menu directly; matching submissions requires accounting for
this difference. The existing phase one-packet-to-raw SE extension can then supply
auditing and the settled joint law. There is no need to prove an isomorphism of
all raw actions before using that extension.
