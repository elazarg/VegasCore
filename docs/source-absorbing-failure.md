# Absorbing public defaults

The tower is intended game -> source game -> dependency graph -> ledger model.
Each level has one executor. The intended game restricts the source menus;
source, graph and ledger execution share the same absorbing public defaults.

## Source execution and observation

[Semantics](../Vegas/Source/Semantics.lean) defines the recursive evaluator
`SourceProgram.runFrom` over `Config`. The source protocol uses the same sample,
binding and revelation successors. Execution returns the complete terminal
configuration, including typed cells, guard metadata, revelations, actual own
actions and the public default history.

A binding decision is `Option (PublicationResult payload)`:

- `none` omits the binding and publicly defaults its owner immediately.
- `some (.success value)` accepts an ordinary opaque binding.
- `some .failure` accepts an opaque but unopenable binding. Its owner remains
  active until public opening fails, unless another public default occurs.

Equal hidden failed cells therefore need not imply equal public status.
At a reveal, withholding, an unopenable binding or guard rejection produces
public failure and defaults the owner. Every later instruction owned by that
player completes automatically with failure. It queries no policy callback and
adds no invented own action. Other players and public samples continue.
Automatic openings still resolve their binding and retain guard bookkeeping.

[DefaultHistory](../Vegas/Foundation/DefaultHistory.lean) is the authoritative
public record. Every completed instruction contributes an entry, newest first:
a newly defaulted player or `none`. `Vegas.SourceProgram.Config.defaulted` is
derived from this record. An empty default set does not imply an empty record.
The initialized record is empty regardless of hidden input binding values.

Views retain this entire public record and actual own actions. Players can
observe when a default happened, even when two histories have the same final
failed cells and default set. [ObservationRecall](../Vegas/Source/ObservationRecall.lean)
reconstructs earlier views by removing the last cell, its public entry and,
only when the player was active, its own action.
[SetupProtocolRecall](../Vegas/Source/SetupProtocolRecall.lean) proves perfect
and decision recall. Active-only callbacks impose no restriction on an active
player's action law and avoid arbitrary inactive responses.

[ProtocolBehavioralPolicy](../Vegas/Source/ProtocolBehavioralPolicy.lean) and
[SetupProtocolBehavioral](../Vegas/Source/SetupProtocolBehavioral.lean) identify
source policies with legal protocol policies and their continuation laws.
[Metadata](../Vegas/Source/Metadata.lean) reconstructs syntax-determined guard
registries and revelations on actual supported terminal configurations.

## Source policy transformations

[DisclosureBehavioral](../Vegas/Source/DisclosureBehavioral.lean) suppresses
openings that are unopenable or whose retained guards reject publication. This
preserves the joint typed-state/full-default-history law for arbitrary profiles
and initial laws. Private intention lists can differ, so the transformation
does not assert full configuration equality. Authentic openings remain legal
even when a guard rejects them.

[BindingNormalization](../Vegas/Source/BindingNormalization.lean) replaces
accepted unusable bindings with values and withholds their openings, while
retaining public omission and its exact public outcome law.
[ValueBinding](../Vegas/Source/ValueBinding.lean) excludes accepted unusability
without excluding omission. [Honest](../Vegas/Source/Honest.lean) instead
requires successful admission at every active binding and disclosure at every
active reveal. [IntendedPlay](../Vegas/Source/IntendedPlay.lean) proves that
intended play has successful cells and no public defaults.

## Graph compilation

[EventGraphAssembly](../Vegas/Compile/EventGraphAssembly.lean) compiles each
source instruction into a typed node and uses sequential dependencies between
source instructions. Public omission is observable: a later player can condition
on an earlier player's default. Moving the later instruction before that public
cause can change the game. More concurrency needs an information-preservation
argument.

The graph has one executor, `Config.step`, in
[Execution](../Vegas/EventGraph/Execution.lean). It normalizes requested actions
of defaulted owners, records every completion and retains the exact public
history. [Information](../Vegas/EventGraph/Information.lean) records public
default timing; own-action recall excludes automatic completions.

[EventGraphLaw](../Vegas/Compile/EventGraphLaw.lean) proves the complete source
configuration law. [EventGraphScheduling](../Vegas/Compile/EventGraphScheduling.lean)
extends it to every permitted public scheduler: the compiled order has a unique
ready event. These laws need no finite payload catalogue, independent initial
law, runtime service or equilibrium premise.
[EventGraphDeviation](../Vegas/Compile/EventGraphDeviation.lean) backtranslates
every graph deviation to one source policy chosen before initialization,
retaining the full terminal configuration law under arbitrary correlated priors.
[EventCompilation](../Vegas/Game/EventCompilation.lean) derives approximate
Nash equivalence from the same correspondence.

## Native ledger execution

[EventApplication](../Vegas/Pending/EventApplication.lean) defines one native
`State`: graph configuration, accepted handles, immutable candidate meanings and
relative-clock metadata. Default membership is read from the graph configuration.
An accepted unopenable binding stays opaque. Silence stutters until the relevant
deadline. Traffic authored after public default is rejected.

[ExclusionCompletion](../Vegas/Pending/ExclusionCompletion.lean) implements
bounded automatic completion directly on that state. Each completion is a
supported step of the graph executor. It preserves existing cells, handles,
candidates, clocks and default membership, and appends a silent completion
record. The drain terminates with no ready event owned by a defaulted player.

[ReactiveRuntime](../Vegas/Pending/ReactiveRuntime.lean) defines the compiled
Interaction application. Inclusion and environment service atomically drain
automatic completions. One physical command can complete several graph events.
[GraphRefinement](../Vegas/Pending/GraphRefinement.lean) therefore relates raw
transitions to finite supported graph paths, including stuttering. It does not
identify a command with a single source step or claim an arbitrary-policy
probability law from path existence alone.

[SourceServiceAsyncStep](../Vegas/Game/SourceServiceAsyncStep.lean) composes
local continuation laws at the actual reached prefix rank. Silent expiry,
accepted typed messages and samples use the same graph continuation; automatic
completion preserves that continuation. Full play comes from the stated
all-history service contract, rather than protocol fuel alone.

## Ordinary compiler correctness

[SourceServiceFirstTurnCompletion](../Vegas/Game/SourceServiceFirstTurnCompletion.lean)
proves the actual first-opportunity clients' source and graph laws for every
source profile. Disclosure normalization and strategy completion preserve every
total reader of the joint typed terminal state and full public default history.
They need no equilibrium, audit, finite wire catalogue, utility bound or
independent-prior premise. The async contract supplies opportunities, protected
inclusion and completion, with the strict reaction-plus-inclusion timing margin.

[CompilerCorrectness](../Vegas/Game/CompilerCorrectness.lean) realizes those
laws in bounded menus under their value-coverage and capacity interfaces.
Certified dependency modes use the public-barrier equality in
[RevealService](../Vegas/Game/RevealService.lean), without changing the source
order. [AsyncDeviationReadout](../Vegas/Game/AsyncDeviationReadout.lean)
backtranslates every unilateral physical policy against first-turn opponents to
one behavioral source deviation with the same joint typed-state/default law.
It adds no finite-player or wire-value catalogue premise.

The ordinary law retains typed state and public defaults. The intended
sequential-equilibrium compiler below additionally preserves the full source
configuration on its implementing path. These are different observation scopes
of the same executions.

## Utility, audit and sequential preservation

[Utility](../Vegas/Source/Utility.lean) reads public default membership. Under
fixed exit utility a defaulted player receives its declared exit payoff;
surviving players can value all typed cells and the complete public history.
Failed-reveal counts are diagnostics of publication cells, not the controller.
Optional source count-penalty results use that same execution with another
payoff rule. Exit transfer and total exit utility remain distinct when an
external valuation is present.

The ledger count audit charges protocol violations. Permitted source omission
and authentic guard rejection retain their declared game payoffs without an
extra audit charge. Bounds on ordinary utilities are scoped to actual source
readouts of legal histories, rather than fabricated impossible default records.

[SequentialCompilation](../Vegas/Game/SequentialCompilation.lean) preserves
each intended sequential equilibrium in the actual bounded raw-menu game.
It uses one consistent limit assessment, the original service, conditional
initial-information independence, utility, coverage and deposit hypotheses.
Its implementing path has no public defaults or audit charges and preserves
the joint full source configuration/default-history/payoff-vector law.
This covers every intended equilibrium law; it does not characterize all target
equilibria or assert uniqueness.

[ClientCompiler](../Vegas/Game/ClientCompiler.lean) packages that assessment
and its physical clients uniformly. Physical incentive comparisons cover
menu-admissible policies, not arbitrary policies outside the finite raw menu.
Value coverage includes every binding/publication payload value and initial
binding input, so those types must be finite. Ordinary clients allow arbitrary
specified pending observations. Ledger-only clients realize the same run and
rationality certificate under the explicit no-delivered-pending-data premise.
The semantic selection is nonconstructive; executable numerical synthesis is a
separate target.

[PaymentPreservation](../Vegas/Game/PaymentPreservation.lean) specializes the
same assessment to executable transfers and external valuation, preserving the
joint initial, full terminal, public and cash observation. It uses the declared
exit transfer and total exit utility without identifying them.

See the [compiler capstones](compiler-correctness-plan.md),
[concrete instance](sequential-se-instances.md) and
[open research boundaries](sequential-se-open-problems.md).
