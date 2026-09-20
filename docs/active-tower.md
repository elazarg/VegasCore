# Active theorem map

The checked path is `SourceProgram → EventGraph → EventGraphRuntime`.
Sequential compilation adds predecessor barriers to this same graph. The
native executor and strategic proof are shared by both execution modes.

## Source semantics

`Vegas.Source` defines `SourceProgram`, behavioral policies, execution, and
terminal states. `Vegas.Source.Accounting` proves that complete executions
resolve their obligations; `Vegas.Source.Safety` proves retained public guards
are satisfied.

See [source semantics](source-semantics.md) and the
[source rationale](source-design-rationale.md).

### The value-binding edge

A source policy may bind an unopenable candidate, which publicly coincides with
binding a value and refusing to open it. `SourceProgram.ValueBinding` names the
policies that never do it, and `Setup.valueBindingGame` is the game they play:
same program, same setup law, same public outcome, fewer strategies.
`Setup.valueBindingSimulation` is the simulation to the full source game —
inclusion on strategies, identity on outcomes, and a deviation certificate for
every policy, so `Setup.isεNash_valueBindingGame_iff` and
`isNash_valueBindingGame_iff` hold with no side condition and
`valueBindingUtilitySimulation` gives the composable form at one-player
coalitions.

Because the edge considers every deviation, it composes: reading it on whatever
map the next edge observes (`valueBindingSimulationOn`) and composing with the
pending-message certificate gives `Setup.valueBindingPendingSimulation`, from
the value-binding game straight to the public message service, with
`valueBindingPendingGame_approximate_nash_iff` its same-error Nash equivalence
against arbitrary native deviations. Commit-time failure is therefore absent
from the source side of the whole tower at no cost.

The certificate is two steps. `exists_pureMixture_publicRun` makes a behavioral
deviation a finite mixture of pure policies, drawn before the private setup law:
the induction carries a list of configurations, and `FinDist.pointCoupling`
draws a decision point's actions in advance by folding over the views those
configurations present, which suffices because a run visits a decision point
once. `PurePolicy.bindValues` then translates a pure policy into one that binds
values and refuses where it replaced a binding, with `bindValues_publicRun_eq`
its law. See [the auctions discussion](auctions-discussion.md).

## Sequential execution

The canonical graph scheduler selects the least unfinished source rank. Its
single-policy deviation correspondence is
`EventLowering.canonical_setup_deviation_law`: the backtranslated policy is uniform over private
initial setup and retains the unchanged opponents.

For native execution, choosing a fixed order of service visits is insufficient
to enforce completion order. `EventGraph.sequentialize` instead adds every
source-earlier event as a predecessor. At a ready event the completed cut is
exactly its strict source prefix, so no accepted packet, chance step, or expiry
can complete a later event first. This construction retains typed fields,
node code, payloads, and payoff expressions. It satisfies the same
`BarrierOrdered` certificate used by the concurrent backend.

The canonical law relates the two dependency choices without identifying
their native histories or packet schedules. Exact source-outcome deviation and
Nash guarantees use the common pending-message theorem.

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
  original-action recall.
- `EventGraph.BarrierOrdered.runPolicies_store_eq_canonical` proves the
  whole-run scheduling law for normalized profiles. Any adaptive public
  scheduler gives the canonical terminal-store distribution. The proof uses
  continuation-law confluence, not a fixed-trace argument.
- `EventGraph.exists_scheduler_mixture` replaces an adaptive public scheduler
  by a finite mixture of deterministic public schedulers, preserving the full
  configuration law. The mixture is chosen before private setup; player and
  chance kernels remain unchanged.
- `EventGraph.BarrierOrdered.exists_deviation_mixture` represents every
  unilateral asynchronous graph deviation as a finite mixture of canonical
  graph deviations against the original canonical opponents. It preserves the
  entire typed terminal-store law, not the completion trace.
- `EventGraph.eventSchedulingSimulation` packages the canonical and scheduled
  games in the shared finite-mixture interface.
  `eventScheduling_approximate_nash_iff` gives same-error Nash preservation and
  reflection for arbitrary utilities of the typed terminal store.
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
law and one profile used across that law. `Vegas.Paper.source_event_graph_canonical_law`
delegates to this result. It covers every source constructor and requires no
guard-feasibility or failure-dominance premise.

`EventLowering.scheduled_setup_law` composes this source-order law with graph
scheduling independence. Every adaptive public schedule of the compiled
profile has the full source terminal-state law, with one profile across the
private setup distribution. `Vegas.Paper.source_event_graph_honest_law` delegates
to this result. No failure-dominance or finite-payload premise is required.

`EventLowering.canonical_deviation_terminalState_law` backtranslates every
canonical graph deviation to a single source policy, uniformly over initial
states. `EventLowering.scheduled_setup_deviation_law` composes this result with
the graph-local scheduler mixture: every unilateral asynchronous graph
deviation has exactly the terminal source-state law of a finite mixture of
source deviations against unchanged opponents. One mixture is chosen before
private setup. `Vegas.Paper.source_event_graph_deviation_law` directly delegates to
this theorem.

`Setup.eventSimulation` packages these laws in the shared finite-mixture
interface. `Setup.eventGame_approximate_nash_iff` proves same-error Nash
preservation and reflection at compiled source profiles, for arbitrary
utilities of the public source result — the publications and public samples a
completed run produces, which is what an outcome is.
`Setup.eventGame_deviation_guarantee` transports lower bounds on that result
against unilateral deviations independently of the deviator's preferences.
These results cover the full source language and need no failure-dominance
or finite-payload premise.

The asynchronous pending-message certificate is checked independently of the
ideal-graph scheduler theorem. The conservative barrier compiler has an exact
finite-mixture deviation law for the concrete event-addressed message service.
A separate
[failure-comparison contract](event-graph-failure-comparison.md) applies only
to broader runtimes that expose genuinely new information before a failure
choice; it is not a premise of the checked compiler theorem.

### Event-addressed pending application

`Vegas.Pending.EventApplication` defines `EventGraphRuntime` independently of
source syntax. Packets address graph events, and accepted inclusions complete
ready events rather than advance a global cursor. Each strategic event has a
separate activation time and relative deadline. The application uses the shared
`Interaction.MessageApplication` host, with public malformed and replayed
traffic, private candidate preparation, explicit expiry, and chance execution.

This application is an ideal-commitment model: the semantic state retains
binding meanings and original player decisions, while public projections
expose handles, publication results, clocks, activation times, and service
grants. Authenticated player observations include this full public projection.

`EventGraphRuntime.servicedEventGame` runs a concrete bounded service: each
epoch visits every event in a permutation sampled from the full public
environment view and history, offers owner/wire/reaction opportunities and
event-addressed reserved inclusion, then advances the clock and checks expiry.
The wire policy remains adaptive within the epoch and arbitrary player
commands remain legal.

`servicedEventGame_complete` and `servicedEventGame_outcome_total` prove
terminality and total graph-outcome readout for every supported play, under
arbitrary player policies. The horizon is `eventCount * (maxDeadline + 1)`
epochs. The proof uses actual native transitions and deadline progress, not an
assumed service-correctness certificate. `Vegas.Paper.event_pending_completion`
directly delegates to the totality theorem. The
[service argument](event-service.md) gives the construction and timing boundary.

`EventGraphRuntime.compileProfile` constructs observation-local native policies
from graph policies. They normalize completion-order metadata and use three
owner opportunities for private sampling, private staging, and public
submission. Success and failure bindings use the same opaque handle and
public timing. Owner-local guard rejection emits withholding rather than an
invalid raw opening. Exact local handler laws retain both the selected
binding result and the original disclosure action.

`servicedEventGame_bindingInvariant` proves typed, distinct accepted handles
and successful-binding candidate provenance for arbitrary complete service
runs. Local laws cover the actual compiled sampling, staging, submission,
and reserved inclusion for both bindings and resolutions. For bindings,
the environment and other players receive the same joint history and
observation after the block regardless of the selected value or failure.
The graph's memoized continuation equations are also checked: privately
drawing and remembering a ready action preserves its future semantic law.
Both compiled three-invocation blocks satisfy the corresponding native law.
For prescribed owners, policy coherence, canonical-resource, packet-origin,
and replay laws protect each unfinished event through actual service prefixes.
The reachability theorem gives every unfinished unchanged-owner activation age
at most one tick. This supplies deadline protection even when a deviation sends
malformed, premature, repeated, or competing traffic; the deviator need not
restore a clean pending-pool boundary.

`BarrierOrdered.ready_public_unique` proves that a ready public event is the
only ready event. It supplies the graph-level reason that observing an honest
opening before inclusion cannot enable another graph decision in that interval.

The event-addressed honest and strategic laws are checked for the full source
language.
`servicedEventGame_honest_store_law` establishes the graph-relative edge;
`eventPendingGame_honest_law` composes it with source compilation. The proof
covers actual adaptive wire actions between submission and inclusion, and
shows that the configured deadline grace protects prescribed play.
`exists_deviation_mixture_store_law` proves the graph-relative exact deviation
mixture for every native focal policy. It jointly predraws the focal, public
wire, and public adaptive-order response functions, proves reached focal
actions are observation-local, and protects every unchanged compiled owner
through the actual service. The ideal-graph scheduling theorem alone is not
used as a substitute for this richer message-host argument.

`Vegas.Game.EventMessages` defines the actual source-to-native game, composed
policy compiler, and terminal-state readout. `Paper.lean` audits the following
capstones over these definitions:

- `Vegas.Paper.source_event_pending_honest_law`: equality with the source outcome law.
- `Vegas.Paper.source_event_pending_deviation_law`: every unilateral native deviation has
  the law of one finite source-policy mixture across private setup, with all
  opponents unchanged.
- `Vegas.Paper.source_event_pending_approximate_nash_iff`: same-error Nash preservation
  and reflection at compiled profiles for utilities of the public source result.

Two per-player transfers accompany these profile-level capstones.
`Setup.eventPendingGame_isBestResponse_compileProfile` carries a source best
response at a fixed profile to the compiled profile, against arbitrary native
deviations, without requiring the opponents to be best responding themselves.
`Setup.eventPendingGame_isBestResponse_of_isDominant` carries a dominant source
policy to a best response against every compiled opponent profile. Both
specialize `UtilitySimulation.isBestResponse_compileProfile`. The environment
ranges over compiled source profiles, so neither states dominance against
native opponents outside the compiler image.

These statements assume the concrete epoch service with deadlines of at least
two ticks; they do not assume a strategic certificate or generalized network
fairness. Their axiom pins contain only the standard Lean axioms. The deviation
mixture is selected before the private setup draw. The wire and event-order
policies may adapt to the public pool, observations, and histories exposed by
the concrete service.

`EventGraphRuntime.handle_publicView_replaceRemembered` proves that changing
the private original-action cache cannot change packet acceptance or the
resulting public view. A rejected original disclosure decision can remain in
private recall without becoming a public ledger input.

`EventGraphRuntime.handle_config_mem_step` proves that every accepted packet
performs one actual graph step at its addressed event, retaining the original
action. `environmentStep_expire_config_eq_or_mem_step` proves that expiry
stutters or performs one graph step. Exact laws identify a due activated
binding or resolution expiry with failure completion, and a ready sample
execution with the original graph chance kernel. These local facts impose no source
restrictions and do not assume a whole-run simulation. Rejected inclusion
leaves the application state unchanged by the generic message-host law, while
the traffic and rejection receipt remain public.

A concrete ledger refinement must realize commitment verification, prove that
the stored-binding check follows from accepted-handle provenance, and evaluate
openings from the submitted proposal and public guard inputs. The current
semantic evaluator is not itself public contract code.

## Outside the theorem

The target assumes ideal opaque commitments, authentication, a fixed finite
epoch protocol with publicly adaptive event permutations, fixed reaction
rounds, and relative deadlines of at least two ticks. It is not a theorem about
computational cryptography, arbitrary asynchronous fairness, transaction fees,
consensus, a ledger, or the EVM. The [road ahead](a-road-ahead.md) treats those
as separate refinement edges.

The `Vegas.Language` surface-syntax prototype has its own internal elaboration
target. Its connection to this tower has no semantic or strategic theorem yet.
