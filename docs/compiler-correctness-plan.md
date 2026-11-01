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

The owners are [graph compilation](../Vegas/Compile/EventGraphScheduling.lean),
[operational refinement](../Vegas/Pending/GraphRefinement.lean) and
[direct physical compiler correctness](../Vegas/Game/SourceServiceFirstTurnCompletion.lean).
The mode-general bounded-menu interfaces in
[CompilerCorrectness](../Vegas/Game/CompilerCorrectness.lean) are checked under
the same public-barrier certificate. Their manuscript composition, corresponding
[Paper.lean](../Paper.lean) pins and full regression acceptance remain open.
Paper-facing acceptance must pin exactly the stated
capstones; normalization, packet, observation and induction helpers stay in
their owning modules.

The operational result reuses the existing graph reachability witness and
native finite graph paths. Thus each projected raw prefix is related by
actual graph steps with their dependent actions; bookkeeping transitions
may stutter. This establishes execution safety, not a probability comparison for
arbitrary raw policies. The exact law concerns prescribed compiled clients.

The second-pass law compares the supported compiler image. It follows by
comparing the exact source-to-ledger law with the canonical graph law through
their common typed-state/default readout. The direct source-to-ledger proof
lifts one local graph-continuation identity through actual completion ranks,
then applies source readout once. It composes omission/withholding, typed
acceptance and chance sampling without a phase-end semantics. Client recovery
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

The direct physical laws use finitely many players, the sequential compiled
graph, a supplied runtime with relative deadlines, and first-opportunity timing.
The asynchronous contract supplies all-history opportunity, protected inclusion
and completion; `AsyncTimely` requires the reaction and inclusion bounds to sum
to strictly less than each owned event's deadline. Source profiles are arbitrary.
Pending observation and correlated initial inputs remain allowed. Finite nature,
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
interfaces must compose the same native execution with their fixed default
payoffs, audit hypotheses and strategic comparison laws.

## Acceptance and maintained presentation

Manuscript acceptance requires exact capstone annotations and service-hypothesis
mapping for operational refinement and ordinary compiler correctness. The
preserved observable is terminal data, including public defaults. Every
mathematical manuscript claim needs its exact guarded pin; unstated library
helpers require none. The strategic and monetary claims retain their own
acceptance obligations.

The [bounded-runtime regression](../VegasTests/CompilerCorrectness.lean) remains
an acceptance consumer. It must exercise successful and failed Boolean bindings
and both disclosure choices in the actual payment service, retaining the exact
joint full-state/payout law without an equilibrium premise. Source, scheduling,
correlated-prior, positive-latency and recovery consumers remain part of the
required full build.

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

Further general DAGs, concurrent public reveals, backtranslation of arbitrary
Interaction deviations, and concurrent raw-runtime SE are separate targets.
Parsing, extraction, cryptographic refinement and machine execution are outside
the typed-source-to-ledger-model boundary.
