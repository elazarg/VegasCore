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
| Source to graph | `Vegas.scheduled_setup_law` | Exact complete source configuration law under every permitted public graph scheduler. |
| Raw Interaction to graph | `Vegas.EventGraphRuntime.reactive_protocol_graph_refinement` | Every transition between initialized controls follows a finite supported graph path, including automatic completion. Every initialized raw history has a graph-reachable configuration; service completion makes all terminal fields available. |
| Compiled graph to ledger | `Vegas.sourceServiceClientPolicy_graph_law` | Actual sequential first-opportunity clients and canonical execution of the compiled graph and policy have the same law through every total reader of typed state and public defaults. |
| Source to ledger | `Vegas.sourceServiceClientPolicy_outcome_law` | Those same physical clients preserve that joint source law for every source profile, without a finite wire catalogue, equilibrium, audit, utility-bound or independent-prior premise. |
| Raw unilateral deviation to source | `Vegas.asyncDeviation_readout_law` | Every physical policy against first-turn clients has one behavioral source deviation with the same typed-state/full-default-history law on the sequential compiled service graph. No finite-player or wire-value catalogue premise. |

The owners are [graph compilation](../Vegas/Compile/EventGraphScheduling.lean),
[operational refinement](../Vegas/Pending/GraphRefinement.lean) and
[direct physical compiler correctness](../Vegas/Game/SourceServiceFirstTurnCompletion.lean).
The mode-parametric bounded-menu interfaces in
[CompilerCorrectness](../Vegas/Game/CompilerCorrectness.lean) require public-barrier
ordering. On compiled service graphs, `serviceGraph_eq_sequential` identifies
each such graph with the sequential graph; this gives no additional compiler
mode. Generic nonordered graph results and their regression fixtures retain
their separate scope. [Paper.lean](../Paper.lean) pins exactly the
mathematical results stated in the maintained manuscript; normalization,
packet, observation and induction helpers stay in their owning modules.

The operational result uses the graph reachability witness and
native finite graph paths. Thus each projected raw prefix is related by
actual graph steps with their dependent actions; bookkeeping transitions
may stutter. This establishes execution safety, not a probability comparison for
arbitrary raw policies. The exact law concerns prescribed compiled clients.

The second-pass law compares the supported compiler image. It follows by
comparing the exact source-to-ledger law with the canonical graph law through
their common typed-state/default readout. The direct source-to-ledger proof
lifts one local graph-continuation identity through actual completion ranks,
then applies source readout once. It composes omission/withholding, typed
acceptance and chance sampling. Strategy completion
and disclosure normalization preserve the original profile's joint
typed-state/default law; private intentions after failure may differ.

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

The direct forward physical laws use finitely many players, the sequential compiled
graph, a supplied runtime with relative deadlines, and first-opportunity timing.
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
canonical execution of the original compiled graph, even when the ledger uses
its sequential dependency mode. It does not assert scheduler independence for
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

Acceptance requires the full `lake build`, exact standard-axiom guards, source
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

Further general DAGs, concurrent public reveals, joint backtranslation of
arbitrary Interaction profiles, and concurrent raw-runtime SE are separate
targets. The unilateral physical deviation law above already covers arbitrary
policies against compiled first-turn opponents.
Parsing, extraction, cryptographic refinement and machine execution are outside
the typed-source-to-ledger-model boundary.
