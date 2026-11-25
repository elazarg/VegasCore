# Module ownership

The core library supports the paper-facing results, the sequential monetary
specialization, concrete runtime instances and checked concurrency adapters.
Regression tests and examples exercise these APIs. Umbrellas expose coherent
library surfaces; research prototypes stay outside them. Checked library
results and paper-facing results use the same strict proof policy.

| Layer | Responsibility and main owners |
| --- | --- |
| GameTheory | Separately managed protocol, probability and equilibrium foundation.  |
| GameTheoryExtensions | Probability, belief transport, consistency and enforcement adapters required by the retained results. |
| Interaction | Authenticated message network, actual recall, partial observation, scheduler laws and evidence. |
| Vegas.Foundation / Vegas.Expr | Typed values, environments and executable expressions. |
| Vegas.Source | Source instructions, initial law, information and guard/completion invariants. |
| Vegas.EventGraph | Typed dependencies, execution, observations and readout. |
| Vegas.Pending | Submission, inclusion, relative deadlines, operational graph refinement, automatic completion, service and count-audit contracts. |
| Vegas.Compile | Source-to-graph compiler and source/scheduler correspondence. |
| Vegas.Game | Ordinary compiler correctness, intended-source extension, Nash correspondence and raw non-concurrent SE preservation. |
| Tools | Lean-native paper validation; theorem libraries cannot import this layer. |
| Tests and examples | Retained semantic regressions and concrete consumers. |

Source execution has one configuration-based evaluator, `SourceProgram.runFrom`.
The source protocol uses the same sample, binding and revelation successors;
it does not reproduce their state updates in another interpreter.

The [absorbing-default semantics](source-absorbing-failure.md) checks that this source
executor and the graph executor preserve full configurations under compilation.
The compiler first constructs declared dataflow dependencies, then adds the
source information order to retain public completion and default timing. The
full-source scheduling proof uses the information graph's unique ready event.
[EventGraphSourceResidual](../Vegas/Compile/EventGraphSourceResidual.lean)
relates each completed cut to the remaining typed source program.
[EventGraphPrefixReadout](../Vegas/Compile/EventGraphPrefixReadout.lean)
reads the full source protocol state from the graph's store, actions, and defaults.
Fixed graph actions and mixed behavioral events preserve the decoded source law.
Under the setup's joint input law and a finite player type, the canonical graph
runner preserves this law at every bounded prefix. The terminal suffix law in
[EventGraphLaw](../Vegas/Compile/EventGraphLaw.lean) also applies to arbitrary
aligned suffix configurations and permits any player type with decidable equality.

The [dependency design](event-graph-dependencies.md) separates these choices
from edge relaxation and actor service. The sole ledger application
derives default control from the graph configuration and performs bounded
automatic completion. Its raw transitions refine finite supported graph paths;
initialized histories retain reachability, cells, deadlines and quiescence.
The [ready roster](../Vegas/Pending/ReadyRosterService.lean) runs on the
sequentialized event graph with any law on its typed inputs. Its owner roster
provides a service contract without a separate activation-coverage proof.
Each owned event has one activation and each chance event has a sample slot.
Protected inclusion takes zero clock ticks. The calendar proof follows every
legal history through automatic completion.
Completed native configurations freeze readout and fixed-exit payoff. Sequential
completion geometry uses finite paths and actual prefix ranks.
`Vegas.EventTimeouts graph` supplies only per-event timeout durations, measured
from readiness in clock ticks. The state, handlers and execution machinery
belong to the `Vegas.EventGraphRuntime` namespace.
For a sequentialized event graph, first-turn clients implement any realizable
graph profile under the asynchronous service contract and timing budget.
At each reached event boundary the distribution of the native configuration
at completion equals one canonical graph step followed by automatic completion.
This gives equality of the complete terminal graph configuration distributions,
including recorded actions.
[FirstTurnSimulation](../Vegas/Pending/FirstTurnSimulation.lean) proves both
laws for the turn policy, and
[FirstTurnClientSimulation](../Vegas/Pending/FirstTurnClientSimulation.lean)
proves them for the recovered ledger clients.
[StoppedPrefixLaw](../Vegas/Pending/StoppedPrefixLaw.lean) stops the physical run
at a specified event's completion. Restricting the resulting configuration to
that event's rank recovers the exact canonical prefix distribution whenever
the full configuration law holds. This also covers stops at which several
defaulted events completed in one native round.
[SourceClientPrefixLaw](../Vegas/Game/SourceClientPrefixLaw.lean) decodes those
actual stops into the full source protocol state after the corresponding
number of instructions, for the disclosure-normalized client profile and a
finite player type.
The source compiler instantiates this result with its disclosure-normalized
profile and projects it through the typed decoder, preserving the joint
typed-state/public-default law of the original profile.
[SourceServiceFirstTurnCompletion](../Vegas/Game/SourceServiceFirstTurnCompletion.lean)
and [SourceServiceSiteBridge](../Vegas/Game/SourceServiceSiteBridge.lean)
give the source specialization and projection.
The full-source interfaces in
[ServiceHonestLaw](../Vegas/Game/ServiceHonestLaw.lean) use the source information
graph directly. Asynchronous service retains arbitrary public scheduling and
per-event deadlines under its service contract.
The actual [periodic service](../Vegas/Pending/PeriodicServiceCompletion.lean)
supplies the raw-history contract for any graph with two players and at most
four owned events, under arbitrary dependencies, input laws and pending
observations. It uses deadlines six, reaction bounds three and inclusion bounds
two. [OddsEvensService](../Vegas/Examples/OddsEvensService.lean) specializes this
shared service to the source-ordered game and its empty pending observations.
[CompilerCorrectness](../Vegas/Game/CompilerCorrectness.lean)
realizes the law with bounded-menu clients under the supplied value-coverage
and capacity interfaces. For the normalized profile, its bounded-menu run
retains the entire terminal
graph configuration, including the action history. The [initialized menu
law](../Interaction/ReactiveRestrictedContinuation.lean) transports physical
execution results to that run. The lower graph APIs retain genuinely nonordered
results, including the different raw reveal-order laws in
[ConcurrentRevealOrderLaw](../Vegas/Examples/ConcurrentRevealOrderLaw.lean).
The dependency-parametric graph result in
[SourcePrefixForfeit](../Vegas/Game/SourcePrefixForfeit.lean) covers independent
bindings and reveals under `RevealRelaxedOrdered`. Its source-prefix clients
always submit bindings and disclose active reveals; deviations retain their
actual observations.
[PrefixClientNash](../Vegas/Game/PrefixClientNash.lean) proves
`Vegas.native_compileIntendedExtension_preserved` for the same dependency
condition, including the combined binding/reveal relaxation. Every supplied
intended extension has first-turn effective-opening source-prefix clients with
the same ε-Nash error against arbitrary raw native policies, no supported
defaults or failed reveals, and the intended joint law of the actual full
runtime readout and true forfeited payoff vector. No caller disclosure,
independent-prior, audit or deposit premise is needed.
[PrefixClientDeviation](../Vegas/Game/PrefixClientDeviation.lean) owns the
native-deviation comparison with the existing information-graph game. Its
[boundary](../Vegas/Game/PrefixDeviation/Boundary.lean) specifies the joint
source checkpoint, observed traffic, and continuation comparison. The
[binding](../Vegas/Game/PrefixDeviation/Binding.lean),
[publication](../Vegas/Game/PrefixDeviation/Publication.lean), and
[chance](../Vegas/Game/PrefixDeviation/Chance.lean) proofs establish separate
cases of that comparison.
Both results use the existing dependency-parametric `Vegas.serviceGame` and
native application.

[OwnedCompletionConfig](../Vegas/Pending/OwnedCompletionConfig.lean) derives a
focal decision from actual native recall at a solitary active event. When the
joint law of the current configuration and native traffic factors through the
focal graph observation, the induced action is observation-local and its graph
step followed by automatic completion has the exact stopped native
configuration law. The initial graph observation supplies the traffic factor
for initialized executions, including correlated inputs. For a graph whose
only event is focal-owned, this realizes the full native deviation
configuration law by one graph policy. [InitialDecisionSimulation](../Vegas/Pending/InitialDecisionSimulation.lean)
extends this deviation law to an arbitrary foreign and chance suffix when
the first event is the focal player's sole decision. It uses first-turn clients
for the other players and the existing service, timing and realizability
hypotheses.
A defaulted event already completed
by automatic service advances its graph checkpoint without another native
round. When the selected owner follows the first-turn reference, the
configuration step and automatic completion law also holds with arbitrary
policies for the other players.

[TrafficPolicy](../Vegas/EventGraph/TrafficPolicy.lean) combines conditionally
sampled action kernels into a single unilateral graph policy at the canonical
prefixes. Applying it to a full native run requires the joint law of the
primary graph prefix and stopped native traffic at every event, including
foreign actions and public samples and any ranks passed by automatic service.
[FocalCompletionTraffic](../Vegas/Pending/FocalCompletionTraffic.lean) proves
the joint factor at an active solitary focal event. The successor graph
observation recovers the previous observation and the action from the player's
recall. This supplies a conditional law for the stopped traffic.
[ChancePhaseTraffic](../Vegas/Pending/ChancePhaseTraffic.lean) proves the
corresponding factor for a solitary public sample, using the visible sample
value. [CompletionTraffic](../Vegas/Pending/CompletionTraffic.lean) transports
the factor over a defaulted graph rank already completed by the ledger.
The general iteration still needs the corresponding physical evidence for
foreign strategic events. A realizable opening may transmit a private value that the
guard rejects, leaving the graph publication failed. In the two-event witness,
the canonical client sends an initially bound Boolean despite an always-failing
guard. The next actor sees the bit in the included packet even with pending
observation disabled. Both bits yield the same graph view at that actor's
binding. Every graph profile is realizable under any law on the initial bit,
and every response based on the shared graph view has the same action law in
the two cases. [GuardRejectedTraffic](../VegasTests/GuardRejectedTraffic.lean)

The foreign traffic factor therefore requires an additional information
hypothesis. The source deviation theorem uses effective disclosures.

The full honest native law in
[PrefixClientOutcomeLaw](../Vegas/Game/PrefixClientOutcomeLaw.lean) needs no
equilibrium, finite binding catalogue, finite initial support, disclosure or
utility-bound premise. Private-binding traffic opacity, conditional table
sampling and checkpoint restoration retain the existing graph configurations
and source checkpoints. Concurrent SE preservation remains open.

For the information graph, the
[physical deviation law](../Vegas/Game/AsyncDeviationReadout.lean)
backtranslates every raw unilateral policy against first-turn clients to one
behavioral source policy with the same typed-state/public-default law. Its
structural source induction carries typed checkpoints and automatic paths;
defaulted instructions require no callback. Native Nash correspondence and its
program-payment specialization use this same observation and actual-history
settlement ranges (`AsyncServiceSpec.SettlementRange`). The concrete monetary
runtime retains the joint typed-state/default-history/cash law. Native
sequential preservation and the uniform semantic client compiler use
this same runtime and preserve the complete source configuration and payoff law.

Start with [sequential preservation](../Vegas/Game/SequentialCompilation.lean),
[observed-component preservation](../Vegas/Game/ObservedComponentEquilibrium.lean),
[monetary preservation](../Vegas/Game/PaymentPreservation.lean) and
the [one-packet raw extension](../Vegas/Game/OnePacketExtension.lean).
Their imports identify the actual proof adapters. The
[open-problems guide](sequential-se-open-problems.md) distinguishes hypotheses
from future service, audit and source refinements.

The [ordinary compiler capstones](../Vegas/Game/CompilerCorrectness.lean)
compare actual bounded clients with source and canonical graph execution.
The [operational refinement](../Vegas/Pending/GraphRefinement.lean) covers
arbitrary raw responses and schedulers, with completion conditional on service.

The [Odds–Evens raw instance](../Vegas/Examples/OddsEvensRawEquilibrium.lean)
consumes the forced-exit theorem and the
[imperfect-evidence adapter](../Vegas/Pending/ThinnedCountCollection.lean).
The [instance guide](sequential-se-instances.md) describes their exact scope.
The [semantic client compiler](../Vegas/Game/ClientCompiler.lean) selects
a consistent bounded-menu completion uniformly for each source equilibrium.
The [assessment fidelity contract](../Vegas/Game/OnePacketAssessmentFidelity.lean)
retains intended decision laws, actual replay posteriors and clean-boundary
continuations of that common completion. Its assembly owner combines strategy,
belief and continuation limits. Projected-site adapters derive cleanliness and
own-debt freedom from the intended source view. Decision coverage supplies a
genuine native site for every intended site; exact replay coverage realizes
every legal history in that source fiber at every corresponding native site.
The [raw assessment transport](../Vegas/Game/OnePacketAssessmentExtension.lean)
keeps corresponding local laws and complete normalized history laws through
the audit and private response aliases. The
[physical fidelity adapter](../Vegas/Game/ClientAssessmentFidelity.lean) composes
that certificate with the existing callback decoder.
The [audited continuation contract](../Vegas/Game/ClientContinuation.lean)
retains complete normalized histories jointly with actual settled payoff from
matching legal starts, and clean source/physical continuations with ordinary
source utility. Its certificate and the retained native SE are stored in the
compiled artifact before selection.
[Ledger assessment realization](../Interaction/ReactiveLedgerAssessment.lean)
identifies complete physical continuations and source-independent client laws.
The [compiler guide](semantic-client-compiler.md) distinguishes this semantic
construction from executable synthesis and from game-specific diagnostics.
[Physical rationality](../Interaction/ReactiveMenuRationality.lean) transports
whole-continuation comparisons to menu-admissible physical policies without
adding a game or an equilibrium definition. Client observable closure and
funding monotonicity live alongside the compiler; common-assessment utility
linearity belongs to the generic protocol analysis layer.

Use `rg` and `python lean-defs.py <files>` to inspect owners before adding
definitions. Share actual operations and isolate hypotheses that vary with a
runtime. Stronger sequential results should reuse the concrete execution and
information definitions; they do not require a universal runtime language.


The complete reactive evaluators in
[ReactiveEvaluation](../Interaction/ReactiveEvaluation.lean) and
[ReactiveResponseEvaluation](../Interaction/ReactiveResponseEvaluation.lean)
derive their evaluator budgets from the scheduler-round horizon and prove
equality with terminal play at every legal starting history. Compiler artifacts
and paper-facing results use complete execution and full sequential equilibrium;
finite-prefix fuel remains local to the corresponding proof adapters.

## Standalone checked consumers

The test and example umbrellas are deliberate build roots. A standalone module's
checked assertions consume the production APIs even when no other module imports
its declarations. These standalone examples each protect a concrete behavior:

| Example | Checked behavior |
| --- | --- |
| [BoundedPaymentAuction](../Vegas/Examples/BoundedPaymentAuction.lean) | Executable bounded-auction transfers retain a profitable conditional-withholding misreport, so truth telling is not dominant for any integer withholding charge. |
| [BoundedPrivateValueAuctionSequential](../Vegas/Examples/BoundedPrivateValueAuctionSequential.lean) | Truthful bidding has a consistent intended sequential equilibrium and exact full configuration/payoff law for every prior over bounded private values. |
| [BoundedAuctionRoster](../Vegas/Examples/BoundedAuctionRoster.lean) | One fixed public single-opportunity builder realizes the truthful sequential equilibrium and exact joint configuration/surplus law under every joint valuation prior. |
| [BoundedAuctionService](../Vegas/Examples/BoundedAuctionService.lean) | One concrete compiled auction assessment retains sequential equilibrium, source-decision fidelity, clean raw and physical play, actual cash and expected utility 8/7 under full pending observation. |
| [CommitTimingInformationSource](../Vegas/Examples/CommitTimingInformationSource.lean) | Alice's honest expected value is one half because her first commitment cannot observe Bob's retained private bit. |
| [ConcurrentRevealOrderLaw](../Vegas/Examples/ConcurrentRevealOrderLaw.lean) | The actual raw callbacks at independent reveals yield different terminal store laws under two reveal orders. |
| [OddsEvensConcurrentNative](../Vegas/Examples/OddsEvensConcurrentNative.lean) | Actual concurrent bindings and reveals preserve the compiled fair Nash equilibrium and full configuration/payoff law under a checked periodic builder and full pending observation. |
| [CorrelatedInitialBitsInformation](../Vegas/Examples/CorrelatedInitialBitsInformation.lean) | Actual private views identify the shared-bit component of an information fiber and support the conditional Bayes-belief transport. |
| [CorrelatedInitialBitsEquilibrium](../Vegas/Examples/CorrelatedInitialBitsEquilibrium.lean) | Existence of intended sequential equilibrium and preservation of every supplied equilibrium on the periodic ledger with a common private bit. |
| [LateLeak.CalibratedPenaltyPreservation](../Vegas/Examples/LateLeak/CalibratedPenaltyPreservation.lean) | The finite late-leak game admits a preserving sequential equilibrium under the calibrated cost bounds, including a forfeit-only construction. |
| [LateLeak.ObservableOutcomeSeparation](../Vegas/Examples/LateLeak/ObservableOutcomeSeparation.lean) | Profitable deferral creates a positive total-variation gap in the observable result law of the finite late-leak game. |
| [LateLeak.SettleLatePreservation](../Vegas/Examples/LateLeak/SettleLatePreservation.lean) | A sufficiently high inclusion probability prevents preservation in the finite settle-late game despite arbitrary prescribed forfeit and charge margins. |
| [LateOpeningRuntimeSourceContinuation](../Vegas/Examples/LateOpeningRuntimeSourceContinuation.lean) | The intended source continuation draws Bob's answer from his policy at the observed bit and retains the single private initial draw in its terminal law. |
| [ProgramPaymentsNativeRepresentation](../Vegas/Examples/ProgramPaymentsNativeRepresentation.lean) | Equal graph configurations can have different native handle observations and acceptance behavior; the actual execution cannot factor through graph configuration alone. |
| [ProgramPaymentsRuntime](../Vegas/Examples/ProgramPaymentsRuntime.lean) | The concrete bounded runtime has the specified Nash choices and exact joint typed-state, default-history and cash settlement law. |

The separate Lean-native validator parses and elaborates Paper in an isolated import
driver. It checks proof-valued declarations, ordinary command scope, and actual
axiom dependencies; the theorem libraries do not import the validator.

Every paper-stated mathematical result needs an exact guarded pin after its full local statement in
[Paper.lean](../Paper.lean). Library results have no separate pin requirement.
Central options, source policy and structural checks apply throughout the tree.
See [validation](../scripts/README.md) and [archived research](archives.md).
