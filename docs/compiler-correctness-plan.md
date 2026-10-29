# Compiler correctness: capstones and further work

The implemented tower is intended game -> source game -> dependency graph ->
ledger model. The first arrow is restriction and equilibrium extension under
its stated penalty hypotheses; the remaining arrows construct the compiled
graph, its Interaction application and actual bounded message clients.
Ordinary outcome correctness concerns every admitted source profile and does
not assume equilibrium.

## Checked basic results

| Boundary | Capstone | Scope |
| --- | --- | --- |
| Source to graph | `Vegas.Paper.scheduled_terminal_state_law` | Exact complete source terminal-state law under every permitted public graph scheduler. |
| Raw Interaction to graph | `Vegas.EventGraphRuntime.reactive_protocol_graph_refinement` | Every transition between initialized controls stutters or performs one supported graph step. Every initialized raw history has a graph-reachable configuration; service completion makes all terminal fields available. |
| Compiled graph to ledger | `Vegas.AsyncServiceSpec.firstTurnClientProfile_graph_law` | The actual bounded first-opportunity clients and canonical execution of the compiled graph and policy have the same law through every total typed-source-store reader. |
| Source to bounded ledger | `Vegas.AsyncServiceSpec.firstTurnClientProfile_outcome_law` | Those same clients preserve the exact source law through every total typed-store reader, without an equilibrium, audit, utility-bound or independent-prior premise. |

The owners are [graph compilation](../Vegas/Compile/EventGraphScheduling.lean),
[operational refinement](../Vegas/Pending/GraphRefinement.lean) and
[ordinary compiler correctness](../Vegas/Game/CompilerCorrectness.lean).
Only the four capstones are pinned for the ordinary-correctness presentation in
[Paper.lean](../Paper.lean). Normalization, packet, observation and induction
helpers remain in their owning modules without additional pins.

The operational result reuses the existing graph reachability witness and
native completion-step relation. Thus each projected raw prefix is related by
actual graph steps with the original dependent actions; bookkeeping transitions
may stutter. This establishes execution safety, not a probability comparison for
arbitrary raw policies. The exact law concerns prescribed compiled clients.

The second-pass law compares the supported compiler image. It follows by
comparing the existing exact source-to-ledger law with the existing canonical
graph law through their common typed readout. The end-to-end law projects the
existing settlement theorem and quantifies over arbitrary total observations.
It retains the actual client algorithms, their checked disclosure normalization,
remembered private actions and bounded-menu recovery behavior.

## Hypotheses and observations

The outcome theorems use `AsyncServiceSpec`, its public-barrier ordering premise,
a source commitment interface, and first-opportunity timing. This covers
sequential and public-barrier compiler outputs. The service supplies configured
relative deadlines, finite initial/leak/builder laws, binding-value and initial
candidate coverage, candidate capacity at least the event count, all-history
opportunity, protected inclusion and completion, and a strict deadline margin.
Pending observation and correlated initial inputs remain allowed.

A total terminal-store reader may jointly retain the initial cells, entire
terminal state, public result and executable payout list. The unfinished result
has zero probability under these service premises. The graph comparison uses
canonical execution of the original compiled graph, even when the ledger uses
its sequential dependency mode. It does not assert scheduler independence for
arbitrary graph policies that inspect chronological completion order.

Raw operational safety needs no timeliness assumption. Its terminal availability
conclusion uses the completion clause explicitly. Finite protocol fuel alone
is not a proof of application completion. Permanent-exclusion SE and monetary
preservation retain their own controllers, hypotheses and capstones; ordinary
compiler correctness does not identify their off-path failure payoffs with
those of the plain source game.

## Acceptance and maintained presentation

The manuscript states operational refinement and ordinary compiler correctness,
with the exact capstone annotations and service-hypothesis mapping. It states
terminal-data preservation rather than preservation of traffic or timing.
The canonical source-graph helper is not independently stated or pinned;
existing strategic and monetary results retain the pins their claims require.

The [bounded-runtime regression](../VegasTests/CompilerCorrectness.lean)
executes successful and failed Boolean bindings and both disclosure choices in
the actual checked payment service. It checks the exact joint full-state/payout
law, including withholding and irrevocable binding failure, without assuming
an equilibrium. Existing source, scheduling, correlated-prior, positive-latency
and recovery consumers remain part of the ordinary full build.

Acceptance requires the full `lake build`, exact standard-axiom guards, source
policy, module boundaries, documentation checks and repository-checker tests.
The maintained manuscript must compile with resolved references, no overflow,
body at most 13 pages and total at most 16 pages, and pass visual inspection.
Commit and push each verified checkpoint in the artifact and manuscript repos.

## Optional stronger interfaces

A source-independent compiler for arbitrary canonical policies on public-barrier
graphs is a useful library extension. It would need graph-level disclosure
normalization preserving original private recall, source-independent clients
and a generic bounded-menu outcome law. Begin with an independently authored
sequential graph and isolate the missing local adapters before broadening the
interface. Reuse existing operations and probability APIs; do not introduce
another runtime or make this extension a prerequisite for the basic capstones.

Further general DAGs, concurrent public reveals, backtranslation of arbitrary
Interaction deviations, and concurrent raw-runtime SE are separate targets.
Parsing, extraction, cryptographic refinement and machine execution are outside
the typed-source-to-ledger-model boundary.
