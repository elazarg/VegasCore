# Active theorem map

## Source semantics

`Vegas.Source` defines `SourceProgram`, behavioral policies, execution, and
terminal states. `Vegas.Source.Accounting` proves that complete executions
resolve their obligations; `Vegas.Source.Safety` proves retained public guards
are satisfied.

See [source semantics](source-semantics.md) and the
[source rationale](source-design-rationale.md).

## Source to typed graph

`Vegas.Game.GraphCompilation` packages the exact honest decoded-state law,
unilateral deviation backtranslation against unchanged opponents, and
same-error epsilon-Nash equivalence. `Vegas.Game.GraphSetup` transports these
results through a finite private initial law using one policy independent of
the sampled initial state.

The edge covers the full failure-aware source language and requires no finite
action-domain, failure-dominance, or universal guard-feasibility premise. See
[source-to-graph](source-graph-edge.md).

## Typed graph to pending messages

`Vegas.GraphRuntime` is the concrete target. Its state and policies use
the generic `Interaction.MessageApplication`; `Vegas.Pending` modules prove binding and
opening soundness, history provenance, replay locality, service protection,
progress, honest continuation laws, and unilateral deviation extraction.

`Vegas.Game.GraphMessages` exposes the composed capstones:

- `SourceProgram.Setup.pendingGame_complete` — every supported serviced play
  terminates, including arbitrary player and wire policies.
- `pendingGame_honest_law` — compiled play has the exact source terminal-state
  law.
- `pendingGame_deviation_law` — every unilateral native replacement has one
  finite source-policy mixture chosen before private setup is sampled, with all
  opponents unchanged.
- `pendingGame_deviation_guarantee` — any real-valued terminal-state lower bound
  valid for every legal source deviation survives every native deviation.
- `pendingGame_deviation_utility_bound` — against fixed opponents, some source
  deviation achieves at least the native deviation's expected test value;
  the witness may depend on the profile and test.
- `pendingGame_approximate_nash_iff` — compiled profiles preserve and reflect
  same-error epsilon-Nash for every terminal-state utility.

`Paper.lean` delegates to selected capstones and pins their axioms. The
[typed-message edge](typed-message-edge.md) and
[deviation extraction note](pending-deviation-extraction.md) explain the proof
boundary.

## Dependency-driven graph interface

The [EventGraph core](../Vegas/EventGraph.lean) provides a typed ready-event
executor, public and player-local observations, behavioral policies, and
public schedulers. Initial values are separate from the graph, so the same
policy is used for every possible private setup draw. The executor proves
finite completion; every supported canonical run completes events in source
rank order. Independent commitments can execute in either order.

The [full-source lowerer](../Vegas/Compile/EventGraphAssembly.lean) constructs
an executable `EventGraph` for every source constructor, with typed initial
inputs, heterogeneous payloads, deferred guards, conditional chance, and
terminal payoff expressions. Its ranked node construction proves every read
has an available producer. `Initial.eventGraph` and `Setup.eventGraph` expose
the compiler without baking concrete private inputs into the graph.

Supporting results are checked:

- `EventGraph.stepThen_map_store_comm` equates the store laws of two independent
  ready events with fixed actions, including their chance kernels. It does not
  equate traces or establish policy-level scheduler invariance.
- `EventGraph.stepThen_map_storeRecall_comm` also preserves every player's
  original dependent action history under the graph's information discipline.
- `EventGraph.BarrierOrdered.informationDiscipline` proves that the
  public-barrier dependency policy gives every ready strategic event exactly
  its source-prefix public values and own bindings, with the specified
  own-action history. Foreign hidden commitments can complete out of order.
- The compiler supplies this certificate unconditionally via
  `toEventGraph_informationDiscipline`. Local evaluation laws relate compiled
  public expressions and chance tables to the source state. `compileResolve_eval?`
  equates the complete resolution kernel with the source's proposal, deferred
  registry check, and failure-on-rejection result.
- `compileEventProfile` translates the complete source strategy interface to
  actual graph policies. Its observation decoder reads public fields and own
  bindings only; its history decoder retains original actions, including a
  disclosure decision whose checked result is failure. Actual graph steps have
  the expected source state and history effects.
- `compileEventPolicy_complete_hidden` proves that completing a foreign hidden
  event does not change a compiled player's decision kernel. The public
  completion order changes, but that compiled kernel uses the source view and
  own-action history. Arbitrary graph deviations still see the order.
- `EventGraph.normalizeProfile` gives a graph-owned policy translation that
  replaces completion-order metadata with the fixed topological prefix while
  retaining visible values and original own actions. Its local invariance
  theorem covers simultaneously ready foreign commitments. Source-compiled
  profiles are already fixed points of this normalization.
- `EventGraph.BarrierOrdered.policyStepThen_map_storeRecall_comm` lifts the
  fixed-action diamond to the two actual normalized behavioral kernels. The
  resulting two-step laws agree on the typed store and every player's
  original-action recall; it is not yet a whole-run scheduling theorem.
- `EventCode.resolve_eval?_playerStore` proves owner-local prevalidation of a
  complete resolution kernel. No foreign hidden binding is needed, and guards
  may reject. This supports checking an opening before public emission; it
  does not by itself prove a public-message implementation correct.
- Terminal configurations have a total source-state readout with no invented
  payload defaults. Under typed state agreement, the readout and terminal
  payoff expressions agree exactly with their source counterparts.

Game outcomes are terminal configurations. A shared utility lift interprets
their complete typed stores and ignores scheduling metadata; utilities on the
full trace can instead use the configuration directly, with separate strategic
proof obligations.

The compiled-graph regressions include an actual step that completes the second
source commitment before the first, and a mixed source program with private
initial inputs, deferred guards, and chance.

The whole-run source-order theorem `EventLowering.canonical_setup_law` runs
the actual compiled graph under its canonical public scheduler. Its decoded
terminal-state law equals source execution, including a finite private setup
law and one profile used across that law. `Paper.source_event_graph_canonical_law`
delegates to this result. It covers every source constructor and requires no
guard-feasibility or failure-dominance premise.

The asynchronous scheduling comparison and the asynchronous pending-message
strategic certificate are the remaining compiler/proof work described in the
[EventGraph plan](event-graph-design.md). Source-order correspondence and
equivalence under other schedules are distinct obligations. The conservative
barrier compiler targets exact honest and finite-mixture unilateral-deviation
laws at both the ideal EventGraph and pending-message levels; these targets are
not yet checked. The two asynchronous ideal-graph law targets in `Paper.lean`
are explicitly admitted; their axiom pins include `sorryAx`. They do not
replace the proved ordered pending-message capstones. A separate
[failure-comparison contract](event-graph-failure-comparison.md) applies only
to broader runtimes that expose genuinely new information before a failure
choice, and is not a gate for that initial compiler.

## Outside the theorem

The target assumes ideal commitments, authentication, canonical ordered
service, bounded reaction slots, and relative deadlines. It is not a theorem
about computational cryptography, arbitrary asynchronous fairness, transaction
fees, consensus, a ledger, or the EVM. The [road ahead](a-road-ahead.md) treats
those as separate refinement edges.

The `Vegas.Language` surface-syntax prototype has its own internal elaboration
target. Its connection to this tower has no semantic or strategic theorem yet.
