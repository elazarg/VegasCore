# Module ownership

The active production modules are the dependency closure of the paper-facing
results, the sequential monetary specialization and the checked concrete
runtime instances. Regression tests and examples are retained when their
production dependencies lie in that core. Umbrellas expose the retained
subtree; imports do not preserve unused research modules merely to keep a name.

| Layer | Responsibility and main owners |
| --- | --- |
| GameTheory | Separately managed protocol, probability and equilibrium foundation. The submodule is unchanged by core pruning. |
| GameTheoryExtensions | Probability, belief transport, consistency and enforcement adapters required by the retained results. |
| Interaction | Authenticated message network, actual recall, partial observation, scheduler laws and evidence. |
| Vegas.Foundation / Vegas.Expr | Typed values, environments and executable expressions. |
| Vegas.Source | Source instructions, initial law, information and guard/completion invariants. |
| Vegas.EventGraph | Typed dependencies, execution, observations and readout. |
| Vegas.Pending | Submission, inclusion, relative deadlines, operational graph refinement, permanent-exclusion controller, service and count-audit contracts. |
| Vegas.Compile | Source-to-graph compiler and source/scheduler correspondence. |
| Vegas.Game | Ordinary compiler correctness, intended-source extension, Nash correspondence and raw non-concurrent SE preservation. |
| Tests and examples | Retained semantic regressions and concrete consumers. |

Start with [recovery preservation](../Vegas/Game/RecoverySequentialCompilation.lean),
[monetary preservation](../Vegas/Game/RecoveryPaymentPreservation.lean) and
the [one-packet raw extension](../Vegas/Game/OnePacketExtension.lean).
Their imports identify the actual proof adapters. The
[open-problems guide](sequential-se-open-problems.md) distinguishes hypotheses
from future service, audit and source refinements.

The [ordinary compiler capstones](../Vegas/Game/CompilerCorrectness.lean)
compare actual bounded clients with source and canonical graph execution.
The [operational refinement](../Vegas/Pending/GraphRefinement.lean) covers
arbitrary raw responses and schedulers, with completion conditional on service.

The [Odds–Evens raw instance](../Vegas/Examples/OddsEvensRecoveryRawEquilibrium.lean)
consumes the forced-exit theorem and the
[imperfect-evidence adapter](../Vegas/Pending/ThinnedCountCollection.lean).
The [instance guide](sequential-se-instances.md) describes their exact scope.
The [semantic client compiler](../Vegas/Game/RecoveryClientCompiler.lean) selects
a consistent bounded-menu completion uniformly for each source equilibrium.
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

Every paper-stated mathematical result needs an exact guarded pin in
[Paper.lean](../Paper.lean). Library results have no separate pin requirement.
Central options, source policy and structural checks apply throughout the tree.
See [validation](../scripts/README.md) and [archived research](archives.md).
