# Module architecture

| Package | Responsibility |
| --- | --- |
| `GameTheory` | Pinned probability and game-theory foundation |
| `GameTheoryExtensions` | Reusable simulations, mixtures, utility transport, and probability lemmas |
| `Interaction` | Message networks, explicit activations, policies, recall, inclusion, and ideal commitments |
| `Vegas.Foundation` | Shared typed contexts, values, expressions, and result interfaces |
| `Vegas.Expr` | Concrete typed expressions and distributions |
| `Vegas.Source` | Failure-aware sequential source syntax, semantics, accounting, and safety |
| `Vegas.EventGraph` | Dependency-driven typed events, cut-based execution, observations, and scheduler-parametric games |
| `Vegas.Pending` | Graph-directed pending-message runtime, strategy compilation, service, and correctness |
| `Vegas.Compile` | Source-to-graph construction and correspondence proofs |
| `Vegas.Game` | Strategic composition across source, graph, setup, and native runtime |
| `Vegas.Examples` | Concrete source mechanisms and checked incentive analyses; depends on expression, source, and game layers |
| test libraries | Executable regressions and theorem instances |
| `Paper` | Direct paper-visible theorem restatements and axiom pins |

Not all of `Interaction` is load-bearing. The Vegas capstones are parametric in
the application, and the instance they are used with is
`EventGraphRuntime.application`, so a dependency walk from `Paper` reaches the
pool, the policies and the invariants, but not `IdealCommitments`,
`MessageReplay`, `MessageApplicationPending` or `MessageApplicationLocality`.
Those characterize what the host permits, which is worth stating and worth not
mistaking for a step in a proof; their module headers say so.

The reactive protocol in `Interaction` is source-independent. Its scheduler
chooses an activation or network/application operation; a player returns
private memory and at most one transmission. Network inputs record broadcaster
and envelope, while player recall records its own outputs. Canonical policy
and execution correspondence and bounded play are checked. `Vegas.Pending`
supplies the event application, graph-policy compiler, and a reserved-service
scheduler; `Vegas.Game.ReactiveCompilation` composes the source policy edge.
`CompletionService` isolates the epoch progress, sampling, and expiry
obligations used by both services. Reactive schedule correspondence and
completion are checked through canonical execution, and fresh candidate
availability holds at every legal reactive history. Network provenance and
compiled-player packet uniqueness are checked: opponents can replay a
prescribed packet but cannot replace it under that author and event. Packet
acceptance, protection through reserved inclusion, and full compiler
correctness remain open. Passive pending-message observation is separate from
scheduling: only foreign, previously unknown packets enter private knowledge,
and the sampled subset is absent from scheduler view and recall. These laws
are checked in `Interaction.ReactiveObservation` and
`Interaction.ReactiveKnowledge`. The generic proper-root argument for an
initial pair of deterministic responses lives in `Interaction.ReactiveSubgamePrefix`.
The [uniform-inclusion counterexample](early-opening-and-spe.md) proves failure
of SPE for the current reactive compiler under its specified service.
Positive reactive SPE preservation under a suitable service contract remains open.
The paper's
command-service capstones and fixed-service coalescing comparisons have their
own stated targets and do not establish the reactive compiler theorem.

Production libraries do not import tests or the paper audit. Generic
game-theoretic results do not depend on Vegas. `Interaction` is independent of
Vegas source syntax. `Vegas.EventGraph` is independent of the source language
and backend; `Vegas.Pending` imports the graph, not source syntax or its compiler. The boundary checker
enforces these directions and keeps the prototype frontend out of the verified
compiler and shared expression modules.

Sequential and concurrent compilation share `Vegas.EventGraph` and
`Vegas.Pending`. Sequential compilation adds every earlier event as a
predecessor, enforcing completion order even under arbitrary native policies.
The graph's `BarrierOrdered` certificate requires the public and own-action
ordering edges, and permits additional dependencies. Both modes therefore use
the same backend certificate. Canonical graph execution additionally has an
exact single-source-policy deviation law in `Vegas.Compile.EventGraphDeviation`.

`Vegas.EventGraph` supplies the IR and operational interface for dependency-driven
compilation. `Vegas.Compile.EventGraphScheduling` proves full-source honest
correspondence under adaptive public scheduling. Source-order execution and
other scheduling instances share one runner. `Vegas.EventGraph.SchedulerMixture`
proves arbitrary-deviation simulation to canonical graph policies, using
GameTheory's finite predrawing theorem through an exact execution adapter.
`Vegas.Compile.EventGraphDeviation` composes that graph-local law with canonical
source-policy backtranslation. `Vegas.Game.EventCompilation` packages the
result as a finite-mixture simulation from the full source game and delegates
Nash and guarantee transport to the shared game-theory interface.
`Vegas.Pending.EventApplication`
implements an event-addressed message application. `EventService` and
`EventServiceCompletion` supply concrete adaptive public service and prove
whole-run completion under arbitrary players. `EventHonestLaw` proves exact
honest terminal-store laws for independently certified graphs;
`Vegas.Game.EventMessages` composes that edge with the source-to-graph law.
`EventStrategicLaw` proves the graph-relative native deviation mixture law,
using actual-service action locality, unchanged-owner deadline protection, and
joint predrawing of focal, wire, and ordering responses. Source backtranslation
and strategic transport belong in `Vegas.Game.EventMessageStrategic`; the
backend has no source-syntax dependency. The [EventGraph plan](event-graph-design.md)
separates source correspondence, scheduling laws, and pending-message guarantees.

`Vegas.Language` prototypes surface notation for typed bindings and nullable
guards. Its internal `SurfaceCore` representation, visibility environments,
guard evaluator, and side conditions live in `Vegas.Language`; the concrete
expression language in `Vegas.Expr` is shared
with source and backend tests and has no frontend dependency. Connecting the
prototype to `SourceProgram` requires a verified elaboration edge; type-correct
lowering alone does not establish semantic refinement. In particular, the
prototype's optional `Legal` predicate requires guard satisfiability, whereas
the failure-aware source admits unsatisfiable guards.

Concrete cryptography, ledgers, block production, and virtual machines belong
in separate target packages with their own execution semantics and refinement
theorems. The current `Interaction` service assumptions must be discharged,
not silently identified with a real network.
