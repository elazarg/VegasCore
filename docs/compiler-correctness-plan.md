# Compiler correctness: capstones and further work

The implemented tower is intended game -> source game -> dependency graph ->
ledger model. The first arrow is restriction and equilibrium extension under
its stated penalty hypotheses; the remaining arrows construct the compiled
graph, its Interaction application and actual message clients.
Ordinary outcome correctness concerns every admitted source profile and does
not assume equilibrium.

## Checked basic results

| Boundary | Capstone | Scope |
| --- | --- | --- |
| Source to graph | `Vegas.scheduled_setup_distribution` | Exact complete source configuration law under every permitted public graph scheduler. |
| Raw Interaction to graph | `Vegas.EventGraphRuntime.reactive_protocol_graph_refinement` | Every transition between initialized controls follows a finite supported graph path, including automatic completion. Every initialized raw history has a graph-reachable configuration; service completion makes all terminal fields available. |
| Ledger event to graph event | `Vegas.EventGraphRuntime.firstTurn_client_event_config_distribution` | Starting at each reached first-turn boundary, the ledger configuration at the next completion has the law of one graph event followed by automatic completion of ready events belonging to defaulted players. |
| Ledger run to graph run | `Vegas.EventGraphRuntime.firstTurn_client_config_distribution` | The recovered clients implement the full terminal configuration distribution of canonical execution on a sequentialized graph. The interface takes a graph input law, a realizable graph profile, and asynchronous service and timing hypotheses. |
| Source profile to graph client | `Vegas.compileEventProfile_realizable` | A source profile with authentic disclosures supplies graph-realizable actions at every reachable, ready event. Disclosure normalization supplies authenticity for arbitrary source profiles. |
| Source to ledger | `Vegas.sourceServiceClientPolicy_source_observation_distribution_eq` | The ledger-to-graph law composed with the source-to-graph law: those same physical clients preserve the joint typed-state/default source law for every source profile, without a finite wire catalogue, equilibrium, audit, utility-bound or independent-prior premise. |
| Original compiled profile to ledger | `Vegas.sourceServiceClientPolicy_graph_observation_distribution_eq` | The clients and canonical execution of the original profile's compiled policy have the same law through every total reader of typed state and public defaults. |
| Raw unilateral deviation to source | `Vegas.asyncClientDeviation_prefix_and_readout_distributions_eq` | One source deviation against the original opponents matches the typed cells and public default record at every event boundary and at completion. The terminal-only form `Vegas.asyncClientDeviation_readout_distribution` also covers infinite player types. |

The owners are [graph compilation](../Vegas/Compile/EventGraphScheduling.lean),
[operational refinement](../Vegas/Pending/GraphRefinement.lean) and
[direct physical compiler correctness](../Vegas/Game/SourceServiceFirstTurnCompletion.lean).
The bounded-menu interfaces in
[CompilerCorrectness](../Vegas/Game/CompilerCorrectness.lean) use the source
information graph. Generic dependency choices and nonordered graph results
have their separate [scope](event-graph-dependencies.md).
[Paper.lean](../Paper.lean) pins exactly the
mathematical results stated in the maintained manuscript; normalization,
packet, observation and induction helpers stay in their owning modules.

The operational result uses the graph reachability witness and
native finite graph paths. Thus each projected raw prefix is related by
actual graph steps with their dependent actions; bookkeeping transitions
may stutter. This establishes execution safety, not a probability comparison for
arbitrary raw policies. The exact law concerns prescribed compiled clients.

A completion boundary records a supported execution and its completed prefix. For each
such boundary, the next ledger stop has the same graph configuration distribution as
sampling the graph action, executing that event, and draining automatic completions.
The graph configuration includes its chronological history. Network receipts and the
ledger clock belong to the runtime. Several graph events can complete in one ledger round.

The whole-run law follows by iterating the boundary simulation. The source adapter applies
the typed decoder to the full graph configuration law for the normalized profile, then
uses the source-to-graph compiler theorem. Normalization preserves the original profile's
joint typed-state/default distribution. The graph history comparison uses the normalized
profile because normalization can change a player's recorded action.

## Equilibrium client compilation

The [uniform semantic compiler](semantic-client-compiler.md) takes a fixed
certified source/runtime specification and any intended equilibrium, and returns
the selected bounded raw-menu assessment with its proof and physical clients.
SE deviations stay within the configured finite menu; binding/publication and
initial binding-input value types must be finite. Nature kernels branch
finitely, and finite menus plus the horizon give finite bounded-menu histories.
Realization theorems identify strategies and complete continuation laws;
ledger clients agree at every legal raw history when no pending data is delivered.
This is separate from the ordinary all-source-profile capstones above and
from executable numerical equilibrium synthesis.

The clients have direct physical whole-continuation incentive inequalities
against every menu-admissible policy, using the selected assessment's beliefs.
Observable closure preserves arbitrary stochastic readouts of the joint law;
outcome-set coverage includes every intended SE law among clean target laws.
Larger deposits retain certification, and one common assessment is closed under
nonnegative utility combinations. These reuse the same execution and assessment
definitions and add no compiler-specification premise.

## Hypotheses and observations

The graph backend takes a sequentialized graph, a runtime with relative deadlines, and
first-opportunity timing. Its simulation theorems work for any player type with decidable
equality. A realizable graph profile requests an opening only when the binding has a value
at that reached configuration. A deferred guard may still reject the opening.
The asynchronous contract supplies all-history opportunity, protected inclusion
and completion; `AsyncTimely` requires the reaction and inclusion bounds to sum
to strictly less than each owned event's deadline. Source profiles are arbitrary.
The unilateral deviation law needs no finite-player premise and covers arbitrary
physical policies against the compiled opponents. Pending observation and
correlated initial inputs remain allowed. Finite nature,
wire-value coverage and candidate capacity are obligations of the bounded-menu
interfaces rather than premises of these direct physical laws.

A total reader may jointly retain the initial cells, entire terminal state,
public defaults, public result and executable payout list. The unfinished result
has zero probability under these service premises. The graph comparison uses
canonical execution of the source information graph used by these ledger clients. It does not assert scheduler independence for
arbitrary graph policies that inspect chronological completion order.

Raw operational safety needs no timeliness assumption. Its terminal availability
conclusion uses the completion clause explicitly. Finite protocol fuel alone
is not a proof of application completion. The SE and monetary compiler
interfaces compose the same native execution with their fixed default
payoffs, audit hypotheses and strategic comparison laws.

## Validation

Every mathematical manuscript claim has an exact guarded pin in Paper.lean;
unstated library helpers require none. Operational and ordinary laws retain
their service-hypothesis mapping and full public-default observation.

The [bounded-runtime regression](../VegasTests/CompilerCorrectness.lean)
exercises successful and failed Boolean bindings and both disclosure choices
in the actual payment service, retaining the joint full-state/payout law
without an equilibrium premise. The default build includes all source,
scheduling, correlated-prior, positive-latency and strategy-completion consumers.

Acceptance requires the full `lake --wfail build`, exact standard-axiom guards, source
policy, module boundaries, documentation checks and repository-checker tests.
The maintained manuscript must compile with resolved references, no overflow,
body at most 13 pages and total at most 16 pages, and pass visual inspection.
Commit and push each verified checkpoint in the artifact and manuscript repos.

## Optional stronger interfaces

A source-independent compiler for arbitrary canonical policies on public-barrier
graphs is a useful library extension. It needs source-independent clients,
an explicit strategic observation boundary and a generic bounded-menu outcome
law. Begin with an independently authored
sequential graph and isolate the missing local adapters before broadening the
interface. Reuse existing operations and probability APIs; do not introduce
another runtime or make this extension a prerequisite for the basic capstones.

Full-source compiler laws on further DAGs, joint backtranslation of arbitrary
Interaction profiles, and concurrent raw-runtime SE are separate targets.
The [source-prefix native theorem](../Vegas/Game/PrefixClientNash.lean) already
preserves intended Nash equilibrium under the allowed binding and reveal
relaxations. The unilateral physical deviation law above covers arbitrary
policies against compiled first-turn opponents on the information graph.
Parsing, extraction, cryptographic refinement and machine execution are outside
the typed-source-to-ledger-model boundary.
