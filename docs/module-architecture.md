# Module architecture

| Package | Responsibility |
| --- | --- |
| `GameTheory` | Pinned probability and game-theory foundation |
| `GameTheoryExtensions` | Simulations, utility transport, knowledge, recall, and probability lemmas |
| `Interaction` | Networks, communication and evidence, activations, policies, inclusion, ideal commitments |
| `Vegas.Foundation` | Shared typed contexts, values, expressions, and result interfaces |
| `Vegas.Expr` | Concrete typed expressions and distributions |
| `Vegas.Source` | Failure-aware sequential source syntax, semantics, accounting, and safety |
| `Vegas.EventGraph` | Dependency-driven typed events, cut-based execution, observations, and scheduler-parametric games |
| `Vegas.Pending` | Graph-directed pending-message runtime, strategy compilation, service, and correctness |
| `Vegas.Compile` | Source-to-graph construction and correspondence proofs |
| `Vegas.Game` | Strategic composition across source, graph, setup, and native runtime |
| `Vegas.Examples` | Concrete source programs and native fixtures with their checked results, including the counterexamples that delimit the compiler theorems; may depend on every other semantic layer except the surface prototype |
| test libraries | Executable regressions and theorem instances |
| `Paper` | Direct paper-visible theorem restatements and axiom pins |

Imports and declaration dependencies answer different questions. An imported
model or theorem is available to a client; it need not occur in that client's
proof. The full-language fixed-calendar SE capstone is
[SourceServiceCompilation](../Vegas/Game/SourceServiceCompilation.lean), using
the reactive pending runner. `scripts/check-se-evidence.py` checks the
declaration dependencies of its paper-visible theorem against the SE checklist.
Operational interfaces and cryptographic refinements require their own
evidence; import reachability alone does not establish them.

Search existing definitions in their owning layer before adding a model or
general proof. `rg --files` locates modules, `rg -n` finds declarations and
callers, and `python lean-defs.py <files-or-directories>` shows definitions and
theorem signatures without proof bodies. Include the pinned `GameTheory`
submodule in searches for general game-theoretic and probability results.
Tests and experimental modules can explain an interface or exhibit a boundary;
they do not supply a production theorem merely by using the same vocabulary.

The following APIs cover the main reusable parts of asynchronous SE work.
The [completion plan](se-completion-plan.md) identifies the remaining adapters.

| Requirement | Existing API | Scope that the client must respect |
| --- | --- | --- |
| Typed source results and effective disclosure | [DisclosureAliases](../Vegas/Source/DisclosureAliases.lean), [Validation](../Vegas/EventGraph/Validation.lean), [EventGraphObservation](../Vegas/Compile/EventGraphObservation.lean) | Effective FALSE and the original private intention differ. Decode observations and retain private recall through the actual compiler relation. |
| Immutable opaque meanings | [CommitmentCandidates](../Interaction/CommitmentCandidates.lean), [EventCommitmentBinding](../Vegas/Pending/EventCommitmentBinding.lean) | Preparation and freezing preserve fixed meanings. These ideal capabilities do not establish concrete cryptographic hiding or binding. |
| Accepted handles and source values | [EventBindingInvariant](../Vegas/Pending/EventBindingInvariant.lean), [SourceSession](../Vegas/Pending/SourceSession.lean) | The graph binding invariant gives typed, unique accepted handles and connects stored successes to owned immutable opening capabilities in both directions. `SourceSession.bindingInvariant` preserves it under native operations; `SourceSession.history_opening_stored` combines it with authentic pending evidence at initialized histories. |
| Frozen resolution compilation and private intentions | [SourceSessionPolicy](../Vegas/Pending/SourceSessionPolicy.lean), [ReactiveAuthorization](../Interaction/ReactiveAuthorization.lean) | Owner-local evaluation fixes the effective decision at admission; opening reads the immutable helper. The original intention is recovered from actual private submission recall by the admitted identifier. These local operations do not yet establish the full source observation, policy or assessment transport. |
| Legal source prefixes and readiness | [EventInvariant](../Vegas/Pending/EventInvariant.lean), [SourceSession](../Vegas/Pending/SourceSession.lean) | `SourceSession.history_source_invariant` preserves the existing source-runtime invariant from a supported setup under arbitrary native traffic and scheduling. Its execution adapter carries authentic packet evidence alongside reachability. Cancellation retains a partial prefix; legality alone does not establish information or equilibrium transport. |
| Pending execution, authentic envelopes and recall | [ReactiveApplication](../Interaction/ReactiveApplication.lean), [ReactiveProvenance](../Interaction/ReactiveProvenance.lean), [ReactiveSubmissionAudit](../Interaction/ReactiveSubmissionAudit.lean) | Reuse the runner and its original-submission records; a signed identifier is not a freely forgeable packet body. |
| Facts at arbitrary native histories | [ReactiveInvariant](../Interaction/ReactiveInvariant.lean), [ReactiveInvariantContinuation](../Interaction/ReactiveInvariantContinuation.lean), [ReactivePacketEvidence](../Interaction/ReactivePacketEvidence.lean) | Supply local submission, handler and environment obligations. The framework supplies history and continuation induction, including rejected calls and partial observations. |
| Accepted-receipt evidence | [ReactiveEvidence](../Interaction/ReactiveEvidence.lean), [ReactiveEvidenceKnowledge](../Interaction/ReactiveEvidenceKnowledge.lean) | A successful receipt can certify handler effects. It does not authenticate a pending packet or an unsuccessful receipt. |
| Menus and private aliases | [ReactiveMenuRestriction](../Interaction/ReactiveMenuRestriction.lean), [ReactiveAliasEquilibrium](../Interaction/ReactiveAliasEquilibrium.lean) | Menu inclusion shares an application and scheduler. Private aliases must have identical effects; a different wire format or timeout behavior is not an alias. |
| Partial collection and reporting windows | [ChallengeWindow](../Interaction/ChallengeWindow.lean), [MessageMonitoringProbability](../Interaction/MessageMonitoringProbability.lean), [ReactiveAuditCollection](../Interaction/ReactiveAuditCollection.lean) | Snapshot observation and conditional delivery bounds must be connected to actual execution. A pair witness needs joint collection; individual marginal bounds do not suffice. |
| Actual settlement comparisons | [TerminalAuditContinuation](../GameTheoryExtensions/Analysis/Protocol/TerminalAuditContinuation.lean), [TerminalAuditCoupling](../GameTheoryExtensions/Analysis/Protocol/TerminalAuditCoupling.lean) | Preserve earlier expected charges. A departure comparison requires incremental collection, rather than charging an already certain fine again. Native reports already in the outcome must not be resampled. |
| Finite-deposit feasibility | [EnforcementLimits](../GameTheoryExtensions/Analysis/EnforcementLimits.lean), [EnforcementSynthesis](../GameTheoryExtensions/Analysis/EnforcementSynthesis.lean) | Additional collection must cover the gain in the actual comparison. The scalar solver consumes finite rational certificates; it does not derive the comparisons or prove an SE embedding. |
| Beliefs and own-action reach | [ReactiveOwnPlay](../Interaction/ReactiveOwnPlay.lean), [BeliefTransport](../GameTheory/GameTheory/Analysis/Protocol/BeliefTransport.lean), [PassageRestrictionExtension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean) | Own recall supplies a common own-reach factor. Source/traffic factorization and negligible contamination at rare information values remain compiler-specific premises. |
| Perturbations, execution error and common limits | [SupportedChoiceDomination](../GameTheoryExtensions/Analysis/Protocol/SupportedChoiceDomination.lean), [ConsistencyCompletion](../GameTheoryExtensions/Analysis/Protocol/ConsistencyCompletion.lean), [LocalSimulationLimit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean) | Initialized total-variation bounds alone do not transport rare conditional beliefs. The limit theorem requires local gain bounds and one fully mixed Bayes family for fixed games and utilities. |
| Raw-action extension without common decision depths | [LocalizedEnforcement](../GameTheoryExtensions/Analysis/Protocol/LocalizedEnforcement.lean), [PassageRestrictionExtension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean) | Enforced departures need collection and a comparator shared across hidden histories. Retained deferrals require their own incentive argument. |
| Complete-play continuation horizons | [ContinuationHorizon](../GameTheoryExtensions/Protocol/ContinuationHorizon.lean), [ReactiveFiniteAssessment](../Interaction/ReactiveFiniteAssessment.lean) | Establish finite menus and a bounded terminal horizon, then reuse the terminal/full/remaining-horizon equivalences. |

[SourceSession](../Vegas/Pending/SourceSession.lean) instantiates the existing
reactive runner, packet-evidence framework and graph binding invariant for
decision admission, mandatory opening and cancellation. Authentic original
certificates agree with selected source binding values at every initialized
native history. `SourceSession.history_source_invariant` also proves that the
source configuration is reachable from a supported setup and that readiness
timestamps remain valid. Its phase identifiers are needed because admission
and opening use different packets for one source event. The event-indexed
[AsyncContract](../Vegas/Pending/ReactiveAsyncContract.lean) does not supply
phase-indexed protection by itself. The source-to-graph compiler and graph
semantics remain shared; source simulation, phase service, native collection
and the general SE capstone require proofs for this application.

The watcher is a distinct native role with zero gameplay utility. General SE
transport interfaces use the same player type on both sides, so the source
assessment needs an inactive-role lift before they can be applied here.
`GameTheory.GameSignature.reindexPlayers` requires an equivalence and its
strategic transport results concern Nash and correlated equilibrium; it does
not add a participant or prove this SE lift.

The reactive protocol in `Interaction` is source-independent. Its scheduler
chooses an activation or network/application operation; a player returns
at most one transmission. Network inputs record broadcaster
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
correctness are checked for the fixed-calendar full-language SE service.
Their general asynchronous counterparts remain open. Passive pending-message
observation is separate from scheduling: only foreign, previously unknown packets enter private knowledge,
and the sampled subset is absent from scheduler view and recall. These laws
are checked in `Interaction.ReactiveObservation` and
`Interaction.ReactiveKnowledge`. The generic proper-root argument for an
initial pair of deterministic responses lives in `Interaction.ReactiveSubgamePrefix`.
The [uniform-inclusion counterexample](early-opening-and-spe.md) proves failure
of SPE for the current reactive compiler under its specified service.
Positive reactive SPE preservation under a suitable service contract remains open.

The source-independent communication extension in `Interaction` adds optional
claims and transferable certificates at a fixed roster of public opportunities.
`Vegas.Source.Communication` supplies binding evidence and opening observations
without changing game results. Knowledge and observation recall live in
`GameTheoryExtensions`; evidence soundness, local menus, unchanged game kernels,
and the bounded communication protocol live in `Interaction`. This semantic
service has no proved native equilibrium correspondence; its synchronous
delivery assumptions are explicit in the
[communication design](ambient-communication.md).

`Interaction.ReactiveEvidence` separately interprets successful native receipts
as persistent semantic facts and proves their soundness under arbitrary play.
`ReactiveEvidenceKnowledge` lifts this to raw and restricted information games.
`Vegas.EventGraph.CommitmentEvidence` defines typed binding facts;
`Vegas.Pending.ReactiveEvidence` proves native handler decoding soundness;
`Vegas.Compile.EventGraphEvidence` relates the facts to source names using typed
context references. `Vegas.Pending.ReactiveDisclosure` proves that an openable
compiled disclosure transmits its evidence even when its guarded result fails.
Receipt evidence does not supply independent verification of pending packets
or a correspondence between communication services.

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
