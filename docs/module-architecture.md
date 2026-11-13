# Module ownership

The active production modules are the dependency closure of the paper-facing
results, the sequential monetary specialization and the checked concrete
runtime instances. Regression tests and examples are retained when their
production dependencies lie in that core. Umbrellas expose the retained
subtree; imports do not preserve unused research modules merely to keep a name.

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
The compiler generates sequential dependencies to retain public default timing;
its scheduling proof uses the unique ready event. The sole ledger application
derives default control from the graph configuration and performs bounded
automatic completion. Its raw transitions refine finite supported graph paths;
initialized histories retain reachability, cells, deadlines and quiescence.
The roster scheduler has an all-history service proof through automatic
completion, and completed native configurations freeze readout and fixed-exit
payoff. Sequential completion geometry uses finite paths and actual prefix ranks.
`Vegas.EventTimeouts graph` supplies only per-event timeout durations, measured
from readiness in clock ticks. The state, handlers and execution machinery
belong to the `Vegas.EventGraphRuntime` namespace.
The direct sequential physical-client laws compose the source continuation
with silent expiry, typed acceptance and chance sampling in
[SourceServiceFirstTurnCompletion](../Vegas/Game/SourceServiceFirstTurnCompletion.lean).
They preserve the joint typed-state/public-default law of every source profile.
The mode-parametric interfaces in
[ServiceHonestLaw](../Vegas/Game/ServiceHonestLaw.lean) require public-barrier
ordering. For compiled service graphs, that premise identifies the graph with
the same sequential graph (`serviceGraph_eq_sequential`); it adds no concurrent
compiler mode. [CompilerCorrectness](../Vegas/Game/CompilerCorrectness.lean)
realizes the law with bounded-menu clients under the supplied value-coverage
and capacity interfaces. The lower graph APIs retain genuinely nonordered
results, including the different raw reveal-order laws in
[ConcurrentRevealOrderLaw](../Vegas/Examples/ConcurrentRevealOrderLaw.lean).
The [concurrent-reveal preservation theorem](../Vegas/Game/ConcurrentRevealPreservation.lean)
uses the same native application with reveal-relaxed dependencies. Against
arbitrary native policies, effective-opening clients preserve intended Nash
equilibrium under the forfeit, with the complete source-configuration/payoff
law and no defaults or failed reveals. Its graph counterpart quantifies over
actual scheduling choices between independent reveals; neither result asserts
concurrent SE preservation.
The [physical deviation law](../Vegas/Game/AsyncDeviationReadout.lean)
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
| [CommitTimingInformationSource](../Vegas/Examples/CommitTimingInformationSource.lean) | Alice's honest expected value is one half because her first commitment cannot observe Bob's retained private bit. |
| [ConcurrentRevealOrderLaw](../Vegas/Examples/ConcurrentRevealOrderLaw.lean) | The actual raw callbacks at independent reveals yield different terminal store laws under two reveal orders. |
| [CorrelatedInitialBitsInformation](../Vegas/Examples/CorrelatedInitialBitsInformation.lean) | Actual private views identify the shared-bit component of an information fiber and support the conditional Bayes-belief transport. |
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
