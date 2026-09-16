# Dependency-driven EventGraph: design and implementation plan

## Status and objective

This document specifies an asynchronous compiler target and the work needed
to prove its strategic correctness. The shared
[EventGraph core](../Vegas/EventGraph.lean) implements typed dependency cuts,
node execution, observations, public scheduling, and finite completion. The
full-source lowerer constructs a certified executable graph. Its whole-run
source-order law is checked for every source constructor, including private
initial-state distributions. Honest asynchronous correspondence, setup-wide
finite-mixture source deviation laws, and same-error Nash correspondence at
compiled source profiles are checked. The asynchronous pending-message game
has a concrete adaptive epoch service, a checked arbitrary-player completion
theorem, and a full-source honest outcome law. Its arbitrary-deviation and Nash
correspondence remain unproved.
The [active theorem map](active-tower.md) records the checked
source-to-asynchronous-graph and source-to-ordered-pending-message results.

Independent ready event kernels commute for fixed event actions after
projection to the typed store and each player's original action history
(`stepThen_map_storeRecall_comm`). The full compiler constructs its read
dependencies and supplies the logical information certificate
(`toEventGraph_informationDiscipline`). Local evaluation theorems relate
compiled expressions, distributions, and complete resolution kernels to source
evaluation, including deferred validation and failure on rejection.
`canonical_setup_law` equates the decoded terminal-state law of compiled
policies under canonical scheduling with source execution. The ordinary
ready-event executor supplies that canonical specialization. Normalized
behavioral policies also satisfy a checked two-step store-and-recall diamond
(`policyStepThen_map_storeRecall_comm`). Whole-run scheduling independence and
setup-wide arbitrary-deviation extraction are checked for the ideal graph;
the [scheduling proof](event-graph-scheduling-proof.md) gives their information
boundary and construction.

The objective is one compilation tower:

```text
failure-aware SourceProgram
    -> typed, dependency-driven EventGraph
    -> asynchronous public pending-message application
    -> transaction/block host and concrete code
```

Each executable representation has an operational game: player policies,
observations, environment policies, and an outcome law. The graph describes
which events may occur, not a separately maintained game tree. The pending
application executes the graph. The source theorem is a composition of the
source/graph and graph/native certificates.

For the conservative public-barrier compiler, the asynchronous capstone targets
exact honest laws and finite-mixture unilateral deviation laws at both the ideal
EventGraph and pending-message levels. Bind failure and disclosure withholding
are already graph actions. Prescribed bind traffic, including a source failure,
must retain one value-oblivious opaque commitment shape. A later, more concurrent
runtime that exposes genuinely new information before failure may instead need
the separately specified utility-dependent capstone.

The implementation must cover every current source constructor, heterogeneous
payloads, arbitrary guards, unopenable bindings, explicit disclosure failure,
private initial setup, private action recall, and conditional public chance.
It must allow genuine out-of-source-order completion where the information
and effect dependencies permit it. Replacing `pc` with a counter having the
same ordering restriction does not meet this objective.

The first target remains bounded and finitely supported. Asynchronous ordering
does not require an unbounded network model. Unbounded delay and almost-sure
termination require a separate probability and liveness extension.

## 1. Early self-disclosure and Nash preservation

### The relevant quantifiers

At a compiled profile, unilateral deviation by player `i` replaces only that
player's policy. Every opponent continues using its compiled source policy.
The environment is the same policy in the baseline and deviating executions;
it may react differently to their different public histories.

An arbitrary native player may transmit its own value at any time, whether or
not the corresponding graph publication is enabled. The runtime must not
pretend that this transmission is invisible merely because inclusion rejects
it. Delivery, pool inspection by the environment, and public receipts remain
part of native observations.

Nevertheless, early self-disclosure is not by itself a counterexample to Nash
preservation. The prescribed opponents must project native observations and
histories to their source decision inputs. An unrelated or premature packet
does not make them abandon their source strategy and react to its contents.
There need not be a source operation corresponding to every such packet.
For the initial barrier compiler, every native deviation should have an exact
finite source-policy mixture against those unchanged opponents. A utility bound
is the fallback only when a broader runtime introduces a genuine additional
informed-failure choice.

The proof must also account for indirect effects: the environment may use the
packet to change scheduling, and it may affect retries, candidate selection,
or deadlines. Observation discipline, integrity, and service protection are
needed to show that those effects remain simulatable. Ignoring a packet in an
opponent's policy is not a substitute for that argument.

### Compiler invariants and player deviations

The information-based compiler must preserve source observation boundaries
through graph dependencies and prescribed message emission. A prescribed
publication that crosses such a boundary is an invalid compilation, not an
additional kind of player deviation. The source/graph and graph/native proofs
must establish this invariant. It supplies no reason to order independent
events or retain a global source cursor.

An arbitrary player may depart from its compiled policy by disclosing early.
This is a unilateral deviation when the other players retain their compiled
policies, and the theorem must cover it. If a second player also changes its
policy to exploit that announcement, there are two deviations. That behavior
is outside unilateral Nash preservation. A stronger solution concept would
require a separate incentive analysis; changed information alone does not
establish a profitable deviation.

The runtime permits silence, expiry, and arbitrary early focal packets; none is
deleted from the native policy space. Under the first compiler's public
barriers, readiness-gated prescribed sends, value-oblivious opaque bind traffic,
and deadline-relative service, expiry realizes bind failure or disclosure
withholding already present in the graph. Exact replay/backtranslation must
cover those behaviors and the adaptive environment's reactions.

If a later runtime permits failure after a genuinely new semantic observation,
the condition is evaluated at the information available when failure is chosen.
An unconditional comparison before that observation need not survive selective
stopping. Section 6 and the
[failure-comparison note](event-graph-failure-comparison.md) state that separate
extension and distinguish it from the initial exact-law target.

## 2. Strategic dependencies

Execution prerequisites and information constraints have different purposes.
Record their reasons separately in compiler proof data, even if the executable
readiness test uses their union.

| Constraint | What it protects |
| --- | --- |
| Data availability | Typed values required by expression, distribution, or guard code exist before evaluation. |
| Observation availability | A prescribed source decision can reconstruct every value and own action it is entitled to observe. |
| Publication barrier | A prescribed public disclosure cannot expose information before an earlier source decision has become fixed. |
| Own-action order | The initial construction preserves the player's source decision history and already chosen private values. |
| Resolution conflict | Two resolutions whose order can change deferred validation cannot silently exchange their effects. |
| Binding origin and completion | Resolving a resource uses its unique accepted binding and its original payload interpretation. |

An expression read set is not a player's information set. The current source
policy interface exposes all preceding public fields and the player's own
retained bindings and action history. A strategy can use a public value even
when no guard or payout expression mentions it. See
[source observations](../Vegas/Source/Semantics.lean).

Conversely, the presence of an earlier foreign sealed field in a source
context does not expose its value. A compiler can reconstruct the hidden
observation entry without waiting for that foreign commitment to complete,
provided no required integrity, guard, or publication condition needs it.

Dependencies are part of the compiled protocol, independent of the particular
profile later analyzed. Do not infer them by inspecting one cooperative
strategy or by assuming that players disregard available information.

### Mandatory small examples

**Hidden commitments can commute.**

```text
commit A.x;
commit B.y;
reveal A.x;
reveal B.y;
```

The first two events should be enabled together. Either binding may complete
first. Both must be fixed before the prescribed opening of `A.x` becomes
eligible for transmission. The final two source disclosures remain ordered:
the source permits B's disclosure choice to depend on A's result.

**An observation edge exists without an expression edge.**

```text
sample b ~ fairBool;
commit A.x where true;
```

A's policy can choose `x = b`. Moving the choice before the sample changes
the policy space despite the constant guard. Reversing the source lines
requires protecting A's commitment from learning that future sample.

**Deferred checks have conflict edges.**

```text
commit P.x;
commit P.y where x = y;
reveal P.y;
reveal P.x;
```

With mismatching bindings and attempted disclosures, y succeeds and x fails.
Swapping the resolutions changes which result fails. Commuting raw storage
writes does not establish commutation of these semantic effects.

**Own history matters even when results agree.** An attempted but rejected
disclosure and intentional withholding can produce the same public failure.
Later choices may depend on the remembered intention. History projection must
retain the original prescribed action, not infer it from the publication result.

These are design examples. The implementation milestones below require Lean
regressions or counterexample theorems for them; this document does not count
them as existing audited results.

## 3. Graph representation and execution

### 3.1 Finite identities, dependent payload types

Use finite event identifiers and a fixed typed field layout. The layout may
contain arbitrary Lean value domains; it is the number of events and fields,
not the cardinality of every value domain, that is finite.

Each field has a declared type, visibility, and unique origin: an initial field
or a producing event. Initial sealed fields are already bound but still have
their source disclosure obligations. They are not new player choices.

The graph contains the initial field layout, not the sampled initial values.
A separate typed input environment supplies those values. One graph and one
policy type must serve the entire private setup distribution; sampling a
different graph with secret-dependent policy types would invalidate that
strategic interface.

An event contains:

- its operation: bind, resolve, or public sample;
- its owner, when strategic;
- typed references and the expression/distribution/guard code it needs;
- its unique output field and its predecessors;
- its logical decision-observation schema and own-history requirements.

Return is the terminal payout/readout specification, enabled only after all
required events complete. A separate strategic return event is unnecessary.

A canonical rank witnesses acyclicity and gives a reference linear extension.
It is not a native execution cursor and does not force the scheduler to select
the least ready rank. Event IDs, candidate handles, and packet IDs remain
distinct.

Retain an explicit payload-origin certificate. Equality of encoded result
types is insufficient: `IExpr.ResultTypes` does not require its result-type
constructor to be injective. A resolve must use the interpretation belonging
to its original binding, including for private initial fields.

### 3.2 Configurations are cuts, not prefixes

An execution configuration contains a predecessor-closed completed set `D`
and its typed output store. For example, a dependent partial store can give
each field a value only when its initial/producer availability witness exists.
An alternative is a typed optional store with a proved exact domain invariant.
Choose between these representations with a small compiling prototype, not a
large generic context framework.

The key invariant is:

```text
field available <-> field is initial or its unique producer is in D
ready(e, D)      <-> e not in D and predecessors(e) are contained in D
```

Completed bind failure and completed publication failure are stored results.
They are not absence from `D`. Candidate preparation, packet submission, and
packet delivery do not put an event in `D`.

One graph step selects a ready event, evaluates its prescribed kernel or
strategic action, and appends its immutable output. The next completed set is
`D union {e}`. Event completion happens once. The runner admits every ready
choice permitted by its explicit scheduler, not just the canonical choice.

The ideal semantic store and the public evaluation store remain separate.
Guard code and public chance code cannot inspect hidden candidate meanings.
The complete ideal store is allowed only for semantic decoding and proof.

### 3.3 Observations and the scheduler

Separate:

1. the declared logical observation used by a compiled source policy;
2. the actual observation of a player in asynchronous execution; and
3. the scheduler's actual public observation.

The actual interfaces retain visible completion order, public results, and
their specified histories. The native interface additionally retains delivered
packets, receipts, clocks, sent commands, and own candidate material. Those
inputs must remain available to arbitrary deviators. They cannot be projected
away in the definition of the target policy space.

Only prescribed policy compilation uses a logical observation projection.
Prove that this projection is available and stable under irrelevant completions.
Preserve each player's source-ordered logical history separately from its
chronological native command history.

The scheduler may use its public observation and history, including arbitrary
packet contents at the native level. It cannot inspect opaque candidate
meanings or private policy caches. Its choices need not be independent of
previous public data. Scheduler noninterference is conditional on the whole
allowed public history, not a marginal claim about each signal separately.

### 3.4 One graph, progressively concrete operational games

The graph fixes operations, typed dependencies, and deferred validation. Its
execution interpretations progressively specify the protocol and host:

| Interpretation | Public observations | Private semantic state |
| --- | --- | --- |
| Ideal commitment execution | Completed event identities and order, public samples, accepted publication results | Unopened binding meanings and original own decisions |
| Public commitment protocol | Commitment handles, all submitted payloads, opening attempts, rejections, and receipts | Player memory and the ideal commitment relation |
| Pending-message execution | Public protocol observations before inclusion, pool changes, inclusion decisions, and clocks | The same player memory and ideal commitment relation |
| Concrete host execution | The host's actual observable messages, transactions, execution results, and fees | Only what the implemented cryptographic and host interfaces justify |

These are operational games over the same graph, not separately maintained
source compilers. A semantic binding value is not a public plaintext ledger
field. A public handle implements it; its hiding, integrity, and observation
properties belong to the next edge. All-public message transport must not be
modeled by concealing submitted payloads or failed opening attempts.

Every edge must account for observations jointly with everything already
visible. Erasing additional observations in the prescribed policy does not
erase them from an arbitrary deviation or from the environment. In particular,
the graph-to-protocol proof must establish the prescribed emission rule in
Section 5.2 and account for arbitrary focal packets. The
[public-observation note](event-graph-public-observations.md) records the
rejected-opening counterexample and the necessary compiler invariant.

Scheduling restrictions are parameters or dependency certificates, not source
language restrictions. A sequential schedule is one interpretation of the
same graph; the source-order execution theorem concerns that interpretation.
An asynchronous strategic theorem separately names its scheduler observation
interface, service assumptions, outcome projection, and solution concept.
Neither exact state-law correspondence nor Nash preservation by itself asserts
preservation of correlated recommendations, transcript preferences, or other
solution concepts. Where more visibility changes such a concept, the result
must state the additional information condition or use enforced sequential
dependencies. The unrestricted operational model remains available.

In particular, a scheduling signal is not by itself a counterexample to
correlated-equilibrium preservation. Additional randomness independent of
recommendations and hidden game data preserves an incentive bound by
averaging. A profile-by-profile Nash backtranslation, however, does not
automatically supply the uniform backtranslation across recommendations
needed for a correlated-equilibrium theorem. Such a theorem needs that
uniformity proof, or an actual counterexample under the stated observation
model; it should not inherit an unsupported impossibility claim from the
mere presence of scheduling.

## 4. Compiling the full source

### Graph-level certificate

The backend consumes the graph and a source-independent causal-discipline
certificate. It does not consume a source program or a source-relative
whole-run simulation hypothesis. The certificate supplies local facts:

- unique typed producers and binding origins;
- availability of an event's evaluator inputs whenever it is ready;
- availability of its declared own bindings and logical action history;
- agreement between completed semantic public fields and the public fields
  allowed at that strategic decision;
- noninterference of independently completing hidden events with that
  decision's logical projection;
- correctness of pending/public guard operands and independence, or an
  explicit dependency, for potentially conflicting effects.

For the first compiler, a strategic event has exactly its source-earlier
semantic public results when enabled. Completion-order metadata can still
differ and remains an actual scheduler/player observation; the scheduling
proof handles it separately. This field condition does not erase arbitrary
native packets, which are handled by the native observation proof.

Prefer conditions checkable from finite predecessor relations, typed read
footprints, and event ownership, with semantic lemmas derived from them. A
certificate field stating the desired arbitrary-deviation law would merely
rename the missing proof. The source compiler proves this local certificate
for every output. Independently constructed graphs may supply it without
referring to source syntax.

Failure disincentives are a separate predicate on utilities and feasible
continuations, not a field of this structural certificate. A graph remains
well formed and executable when a player prefers failure. Only the broader-
runtime utility theorem for a genuinely additional informed-failure choice
requires an incentive premise that may not hold; the initial exact compiler
does not.

### 4.1 First dependency construction

The initial construction has genuine concurrency and a simple proof target.
Treat source samples and source resolutions as **public events**. Between two
successive public events, commitments form an interval of private choices.

Generate these edges:

1. Consecutive public events are ordered.
2. Every private commitment depends on the preceding public event, if any.
3. The following public event depends on every commitment in that interval.
4. Commitments in the same interval owned by the same player retain their
   source order. Different owners' commitments do not receive an edge merely
   because one was written first.
5. Add typed data/origin and resolution dependencies where needed, and make
   terminal readout depend on all events.

These rules preserve all preceding public observations, exclude later public
disclosures at earlier effective decisions, and preserve own private recall.
They cover the whole source language. They are conservative, not a claim to
compute the maximally concurrent strategic dependency relation.

The graph executor itself does not know about intervals or barriers. Those are
properties of this compiler's emitted edges. Every enabled event can be chosen
without waiting for lower-ranked independent events. Within an interval, one
owner can advance along its own chain while another owner is delayed, subject
to the separate deadline/service contract.

The first concrete nontrivial execution must complete B's commitment before
A's in the example above. A system that only pipelines packet submission while
accepting all bindings in source order fails this test.

### 4.2 Guard specialization

Retain the existing shared deferred-guard evaluator. The initial public-event
ordering permits the compiler to retain specialized checks:

- a prior publication is a typed reference to an available result field;
- a later publication is represented as pending;
- the current proposed result is provided only to the atomic validator.

Prove those facts from the emitted dependencies for every reachable cut.
They must not rely on a sequential cursor or on the physical store containing
every source-prefix field. Public fields from a future publication must not
silently replace a literal-pending operand.

This construction deliberately avoids a new dynamic guard language. If a later
compiler pass reorders public resolutions, it must either prove the specialized
checks and outcomes remain equivalent or introduce and verify the appropriate
dynamic lookup. It cannot reuse prefix-specialized code without that proof.

### 4.3 Source decisions on partial configurations

At a ready commitment, all prior public fields and prior own actions needed by
its source policy exist. Foreign private bindings may be unfinished; their
logical observation entries are hidden regardless. Construct the source view
from exactly these facts, without fabricating a hidden ordinary value.

At a ready resolution, the binding origin, earlier public results, and own
logical action history are available. Retain the prescribed disclosure Bool
even when the accepted public result is failure. At a sample, reconstruct the
public expression environment and execute the exact conditional kernel once.

The source/graph compiler and its correctness proof must use this construction
for every source profile, not just equilibrium or cooperative profiles.

### 4.4 Source-order proof invariant

The source-order proof follows the compiler's traversal state: the residual
source program, typed context references, publication references, retained
guard registry, and embedding of the remaining events into the whole graph.
Relate its source state and history to a canonical graph configuration by:

1. The completed cut and chronological event list are exactly the executed
   source prefix.
2. Every source cell agrees with its typed graph reference. For a private cell,
   this part compares the immutable binding, not its publication status.
3. Every private publication reference evaluates to that cell's source status:
   literal pending before resolution, its result field afterward. During
   validation, the selected cell uses the proposed result in both semantics.
4. The event identifiers and original supplied actions decode to the same
   per-player source action histories.
5. Both sides retain the same guard registry.

At initialization, the private-status clause uses `Initial.privatePending`;
the binding encoder alone cannot reconstruct arbitrary publication statuses.
Sample, commit, and reveal steps then use the local expression, distribution,
and deferred-guard evaluation laws. Terminal context agreement gives decoded
state equality and the payoff readout law. A separate policy translation and
backtranslation must establish that the two step kernels are actually selected
from corresponding observations; structural field availability alone does not
prove that policy law.

This induction concerns source-order execution. The asynchronous comparison
uses the additional [scheduling coupling](event-graph-scheduling-proof.md),
including actual scheduling observations and setup-wide finite mixtures.

### 4.5 Further dependency reduction

Possible subsequent passes include commutation of adjacent independent sample
kernels and finer treatment of public operations with proven independent
observations and effects. Each pass needs a strategic theorem in addition to
an execution-law theorem. The present source exposes all prior public results
to a decision, so many apparent expression-level independences are not
information independences.

Do not change source observations, constrain policies, assume successful
guards, or exclude source constructors to obtain more concurrency. A proposed
language-level restriction or annotation requires a separate design discussion.

## 5. Asynchronous pending-message execution

### 5.1 Application state and acceptance

Replace the global current phase by a completed cut, per-event binding/result
state, and per-event activation/deadline data. Reuse the generic
[message application](../Interaction/MessageApplication.lean) and its policy
runner, rather than implementing another transport system.

An application handler addresses an event by stable ID. It checks readiness,
ownership, binding identity, payload type, and opening verification as
appropriate. A successfully handled packet completes only that event and may
enable several successors. Accepted candidate meanings and completed outputs
are immutable; competing packets cannot overwrite either.

Keep all native behaviors: malformed data, premature and late messages,
replays, competing candidates, failed openings, explicit withholding, and
preparation unrelated to the current enabled set. A premature packet may be
visible even though its attempted inclusion has no application effect.
Replaying or resubmitting it later follows the shared pool semantics; the
compiler must not assume that rejection means automatic future acceptance.

### 5.2 Prescribed player implementation

Each ready owned event has a sample-once cache keyed by event identity:

- bind: select the source choice once, prepare its canonical candidate, submit
  its handle, and retain the logical bind action;
- resolve: select and remember the source Bool once, validate the prospective
  public result, then send its typed opening or canonical withholding packet;
- no further prescribed action for a completed event.

A prescribed opening is transmitted only after its publication prerequisites
are complete. An adversary is still allowed to send that opening earlier.
This condition belongs to the compiled policy, not a prohibition on arbitrary
players' ability to transmit raw values.

Prescribed failure traffic remains uniform in failed intention and rejected
raw value. Otherwise a guard-invalid candidate could leak a different secret
through a packet whose accepted source result is only failure.
Uniformity includes submission opportunities, not only packet contents. A
successful binding must not require an extra visible preparation round that
lets an observer distinguish it from an unopenable binding. Use the same
private preparation stages and public submission opportunity for both;
unused private stages can stutter.

The original disclosure decision belongs to the player's private recall. A
canonical withholding packet cannot tell the ledger whether the source policy
chose `false` or chose `true` for an opening that prevalidation rejected. The
compiler must preserve that distinction in player memory without requiring
the contract to infer it. In a representation containing both native state and
a semantic graph configuration, this original-action record is private or
proof state, not an additional readable ledger field. A lower contract
refinement must show that public acceptance, settlement, and environment
observations do not depend on that hidden record. A ledger-only decoder to
the entire graph completion history is neither required nor generally possible.

When several owned events are ready, the native dispatcher must select one
according to a specified observation-local rule or a public service grant.
For the initial compiler, same-owner dependency edges sharply simplify this
case. The dispatcher chooses execution work, not a new source payoff action;
its source-view reconstruction and sample-once behavior still need proofs.

### 5.3 Service relative to deadlines

Use a monotone clock and an activation time for each newly ready strategic
event. Completion of an unrelated event must not reset or consume another
event's private timeout counter. A shared clock can advance several deadlines;
the service contract must protect all simultaneously active compliant events.

Specify a finite horizon and a public, prefix-checkable service discipline:

- enough owner invocations for a continuously enabled prescribed event to
  prepare and submit;
- inclusion of its effective prescribed packet before its expiry transition;
- eventual timeout resolution of a silent or ineffective owner within the
  horizon;
- execution of each enabled sample's fixed kernel exactly once;
- enough progress to complete the finite dependency graph.

Clock advancement, expiry processing, owner invocation, delivery, and inclusion
are distinct operations. A blockchain host may bundle some of them into one
transaction or block; the abstract model must specify their order at deadline
boundaries. Expiry is an executed handler action, not an autonomous promise
that an EVM contract wakes itself up.

The contract must be expressible through observable opportunity and service
obligations, not through a field assuming whole-run strategic correctness or
the eventual desired payoff. Prove a concrete service implementation satisfies
it for arbitrary players. Deadline configurations require a feasibility
witness; do not make a universal theorem vacuous by admitting no scheduler
for impossible budgets.

First implement bounded service allowing at least two different topological
completion orders for the same graph. A public driver can grant ready events
service budgets and interleave delivery/reaction slots, with a watchdog
providing protected opportunities. It must not impose canonical source order
on independently ready events. The exact budget/watchdog construction is a
mathematical design gate before large policy proofs are written.

The existing policy runner has a fixed invocation list. A sufficiently rich
fixed polling roster can already realize out-of-order event completion through
adaptive inclusion and ready-event dispatch. If adaptive principal invocation
is needed, add that capability to `Interaction` with public activation and a
bounded runner. Do not duplicate the runner or silently claim fixed polling
covers every adaptive activation model.

Service admissibility must survive unilateral replacement. Do not condition
execution afterward on the favorable event that the scheduler happened to be
fair; that conditioning can change outcome laws. Establish service properties
for all supported runs of the admitted driver/policy implementation.

### 5.4 Minimal graph-relative backend

Build the first backend as a new EventGraph application over the existing
`Interaction.MessageApplication`, not by adding cases to the cursor-indexed
`GraphRuntime.State` and not by copying its transport runner. The old
candidate, pool, authentication, and bounded-service machinery is reusable;
its existential graph suffix, global `pc`, single `enteredAt`, name-indexed
bindings, and phase-recursive service plan are not.

For one fixed `EventGraph`, the application state contains:

- its `Config`, hence separate inputs, completed cut, typed optional outputs,
  and chronological original actions;
- accepted commitment handles indexed by graph **field identity**, including
  initial binding fields;
- the existing private `CommitmentCandidates` catalogue, with initial-field
  and player-preparation slots; and
- one monotone clock plus `activatedAt : EventId -> Option Nat`.

The activation invariant is exact: an unfinished ready strategic event has one
activation time, preserved while it remains ready and cleared on completion.
After a completion, scan the finite enabled set, retain existing times, and
stamp newly ready events with the current clock. There is no application
cursor.

`MessageApplication.handle` is deterministic. Binding and resolution handlers
should therefore consume a deterministic output interface proved equivalent to
the corresponding `EventCode.eval?` pure law. Extract that interface from the
graph evaluator; do not repeat its deferred-validation algorithm in the
backend. Sample events retain their `FinDist` kernel as environment actions.
This is an evaluator API requirement, not a restriction on guards or chance.

Protected inclusion must be addressed to an event as well as an owner.
Selecting an owner's latest packet is insufficient when that owner has
prepared several candidates or submitted packets for different events. The
service selects the newest pending packet with the granted event address and
authenticated owner, without inspecting a sealed candidate's meaning. For a
prescribed policy, a separate acceptance proof must establish that this packet
is effective; arbitrary packets can be rejected.

The public view consists of completion identities/cut, `publicStore`, accepted
handles, clock, activation metadata, and the current service grant. Candidate meanings and binding values
remain hidden. A player's authenticated view adds `playerStore`, original
`ownCompletions`, and its own prepared candidates. Reuse
`EventGraph.publicObserve` and `playerObserve`; a parallel logical-history
representation would bypass the checked information certificate.

Packets address stable event IDs:

```text
commitment(event, handle)
opening(event, handle, typedRaw)
withhold(event)
malformed(typedRaw)
```

Inclusion first checks that the event is unfinished and ready, then
dependent-pattern-matches its retained `EventCode`.

- For `bind owner payload`, authenticate owner and handle. Decode an openable
  original-payload candidate as `.success value`; accepting a fresh or already
  unopenable prescribed handle gives `.failure`. Initial successful bindings
  receive openable candidates and initial failed bindings receive unopenable
  ones, while their public handles have the same shape. Complete through
  `Config.step`, recording that same `PublicationResult` as the original bind
  action.
- For `resolve owner payload binding checks`, an opening must use the immutable
  handle associated with `binding.field`, verify its typed raw value, and agree
  with the stored successful binding. Execute `Config.step` with action `true`;
  withholding has the public effect of `false`. Private original-action
  bookkeeping may retain a remembered rejected `true` only when its evaluated
  output is that same failure. The public transition must not depend on this
  choice of private record. The node evaluator, not duplicate handler code,
  computes deferred checks and the accepted publication result.
- A sample accepts no player packet. A public command executes its unit action
  and retained kernel exactly once.

Premature, late, wrong-owner, wrong-type, malformed, and replayed packets stay
in message history but do not change application state. Readiness plus
`Config.complete` gives write-once outputs. Arbitrary focal packets remain in
the policy space.

Expiry is an explicit command `expire event`, effective only if that event is
still ready and its own elapsed time meets `deadline event`. It completes a
bind with action/output `.failure`, or a resolve with action `false`; it cannot
expire a sample or spend another event's budget. Fix whether a command advances
the clock before testing the boundary and use the same convention in handlers
and service proofs.

#### File plan and proof boundary

Keep the source-independent edge under `Vegas/Pending/`, alongside the
source-independent ordered backend until that implementation is superseded.
Event-specific modules use the following ownership:

| File | Responsibility |
| --- | --- |
| `EventApplication.lean` | Raw values, field-indexed handles, cut-based state/views, preparation, event-addressed inclusion, sample/expiry commands, and the `MessageApplication` instance. |
| `EventInvariant.lean` | Activation domain, output/handle immutability, binding provenance, observation secrecy, and command preservation. |
| `EventPolicies.lean` | Per-event sample-once caches, uniform opaque bind traffic for success and failure, retained resolve Boolean, and readiness-gated sends. |
| `EventStepLaw.lean` | Accepted bind/resolve/sample/expiry projects to the corresponding `Config.step`; preparation and rejected traffic stutter. |
| `EventService.lean` | Finite public rounds over enabled IDs: owner opportunities, adaptive wire slots, addressed reserved inclusion, clock advance, local expiry, and sample execution. |
| `EventSubmission.lean` | Public author/address selection and immunity to later unrelated packets. |
| `EventServiceLaw.lean` | Clock accounting, invariant preservation, persistent activation times, and local sample/expiry progress. |
| `EventServiceCompletion.lean` | Per-epoch progress and supported-run completion of the concrete service game under arbitrary players. |
| `EventHonestLaw.lean` | Couple compiled policies and the admitted driver to EventGraph steps, then use scheduling commutation to obtain the canonical terminal `g.Outcome` law. |
| `EventDeviationLaw.lean` | Setup-wide predrawing/locality and the exact graph-relative deviation mixture; never an application invariant. |

Reuse `MessageApplication`, its wire policies and history runner,
`CommitmentCandidates`, and the setup-wide predrawing framework. The old
prepare/submit/include/withhold and reserved-service proof pattern is useful.
Do not reuse cursor `Prefix`/`Follows`, phase frames, or `pc`-gated expiry
lemmas. Move generic typed raw/candidate helpers into `Interaction` if needed;
the new backend imports EventGraph modules and never `Vegas.Compile`.

The local `StepLaw` relation is deliberately smaller than a simulation
theorem: native cut and typed outputs equal the ideal `Config`; every accepted
binding field has one owner-correct immutable handle whose candidate decodes
to its stored binding result; public/player projections agree; and activation
times have the exact domain above. No whole-run law is a field or premise.

For a graph, information certificate, input law, compiled profile, and admitted
public driver/wire policy, the first whole-run target is

```text
map nativeReadout (nativeGame.play compiledProfile)
  = map readout ((g.canonicalGame inputs).play profile),
```

where both readouts return `g.Outcome`, discarding transport and completion-
order metadata. Prove completion separately for every native player policy in
the shared runner. The arbitrary-deviation goal remains the exact mixture in
Section 6. Do not first postulate that the wire environment factors through an
EventGraph `PublicScheduler`: it sees a richer pool/history and can select
different inclusions after different raw focal packets. The local step
relation plus graph scheduling/coupling must establish the displayed outcome
law directly.

The concrete service visits all event IDs once per epoch, in a permutation
chosen from the environment's current public observation and history. Each
event receives a public grant, its owner's invocation opportunities, adaptive
wire delivery/reactions, reserved event-addressed inclusion, and a sample
opportunity. Only after the complete sweep does the clock advance, followed by
all expiry checks. No `Fintype Player` is needed: node ownership determines
the reserved calls and a finite roster determines additional reactions.

Relative deadlines of at least two ticks leave time to serve an event enabled
after its position in the preceding epoch. The [service argument](event-service.md)
explains why one tick is insufficient and separates arbitrary-player
completion from the remaining compiled-policy protection and strategic laws.
The environment may reorder independent events and inspect all pending
payloads; it cannot add clock advances beyond the concrete service plan.

## 6. Strategic statements and composition

Fix a source program P, finite private setup law rho, a realizable service
configuration, and an admitted public environment policy E. Let C be the
actual playerwise strategy compiler and d the terminal-state decoder. Let u
interpret source terminal outcomes as player utilities. On completed native
executions, U interprets the decoded source outcome using u; completion makes
its value on missing outcomes irrelevant.

The structural and honest-law obligations are:

```text
completion:
  every supported asynchronous native execution has a decoded outcome,
  for arbitrary native player policies

honest law:
  map d (native[P, rho, E].play (C sigma))
    = map some (source[P, rho].play sigma)
```

For the initial public-barrier pending compiler, the strategic capstone is the
stronger exact statement:

```text
unilateral deviation law:
  for every player i and arbitrary native policy tau_i,
  there exists a finite law mu over legal source policies pi_i such that

  map d (native[P, rho, E].play ((C sigma)[i <- tau_i]))
    = bind mu (fun pi_i =>
        map some (source[P, rho].play (sigma[i <- pi_i])))
```

The mixture is chosen before the private setup draw. Opponents are unchanged,
and `E` is fixed as an adaptive policy rather than a preselected command trace.
This target retains arbitrary focal packets. Its proof must use readiness-gated,
value-oblivious prescribed traffic—including the same opaque bind shape for a
source failure—and deadline-relative service; none of those properties is
assumed merely from the graph syntax.

For a broader runtime with a genuine additional informed-failure choice, the
separate utility-dependent capstone is:

```text
unilateral utility bound:
  for every player i and arbitrary native policy tau_i,
  there exists a legal source policy pi_i such that

  E[U_i | native[P, rho, E], (C sigma)[i <- tau_i]]
    <= E[u_i | source[P, rho], sigma[i <- pi_i]]

consequence:
  sigma is epsilon-Nash at source
    -> C sigma is epsilon-Nash in the asynchronous native game
```

Either exact simulation or the displayed utility bound gives preservation;
honest-law equality for all compiled profiles also gives reflection at
compiled profiles, with the same error. No conclusion concerns native
equilibria outside the compiler image.

For the utility variant, the source witness can depend on `sigma`, `E`,
`tau_i`, and `u`. No finite payload-domain or guard-feasibility premise is
intended. Every program compiles; an incentive theorem is conditional on its
stated utility hypothesis, not a restriction on source syntax.

### Failure disincentives and feasible repair

This subsection concerns the broader runtime variant, not the initial
public-barrier compiler. See the
[failure-comparison note](event-graph-failure-comparison.md) for the exact
boundary.

At an additional failure decision, compare the complete failure continuation
with a feasible continuation that preserves already fixed commitments. For
each reachable information state I at that decision, require

```text
expected utility of failure at I
  <= expected utility of the feasible continuation at I.
```

Both sides include the subsequent execution, not just an immediate transfer.
The comparison must cover the actual additional information available in the
runtime. A sufficient source-level condition compares the paired continuation
utilities pointwise over compatible semantic states; averaging preserves it
under any permitted observation. A weaker information-conditional condition
may suffice where its conditioning law is established.

The continuations must form a legal strategy using the available information;
choosing a different clairvoyant repair in each hidden state is insufficient.
The proof must construct this normalization and relate its continuations to
the source condition. Unavoidable failure, including an unopenable binding
or an unsatisfiable guard, is not repaired into a nonexistent valid value.
Source-representable failure remains a source choice. The incentive comparison
is needed for the additional failure behavior removed by the normalization.

The generic [selective-stopping lemmas](../GameTheoryExtensions/Math/SelectiveStopping.lean)
already prove that branchwise continuation superiority survives informed,
randomized stopping, including a strict-margin version. They do not establish
the compiler-specific normalization or its source interpretation. Those are
explicit mathematical obligations in M0 and proof obligations in M4. A finite
backward argument must cover repeated failure opportunities and scheduler
reactions, not just one isolated Boolean choice.

Package an all-profile bound using the existing
[utility simulation interface](../GameTheoryExtensions/Core/UtilitySimulation.lean).
If the incentive condition is only established against a particular profile's
opponents, use its profile-local Nash transfer theorem; do not silently
generalize that condition to all profiles.

### Stronger exact-law results

Where deviations admit exact simulation without an incentive hypothesis,
retain the stronger certificate: a finite mixture of source deviations has
the same decoded outcome law. Use the existing
[mixture simulation interface](../GameTheoryExtensions/Core/MixtureSimulation.lean)
and its [composition theorem](../GameTheoryExtensions/Core/MixtureSimulationComposition.lean).
A finite mixture also supplies the utility bound: some component has at least
its average utility. This requires no closure assumption on source strategies.

Exact simulation additionally transports arbitrary source-outcome bounds,
including bounds protecting another player independently of the deviator's
preferences. The failure-disincentive utility theorem alone does not imply
those guarantees: an adversary unconcerned with its own utility can still
choose a harmful failure. State the two scopes separately.

Extra trace preferences require their own contract. Keep completion's
missing-result case distinct from source publication failure.

### Matching the middle game

There is one EventGraph syntax and ready-event transition semantics. Its
canonical-order runner is a scheduler specialization and a useful reference
game. Its asynchronous runners are actual games with their own scheduler
observations and policy spaces, not just alternate enumeration of final stores.

The source edge first establishes correspondence with that canonical graph
game. A graph-level scheduling theorem establishes the appropriate law and
deviation comparison for asynchronous graph execution. The native backend is
graph-relative and must discharge the same causal observation obligations
under its richer message histories.

The operational compiler theorem has a particular schedule in its statement.
Writing `C(P)` for the compiled graph, `compilePolicy` for the policy
translation, and `decode` for the terminal-state interpretation, its target is

```text
map decode (runGraph C(P) sourceOrder (compilePolicy pi)) = runSource P pi.
```

Initial environments, including their private distribution, are related by
the compiler's encoding. Event numbering follows the source order; choosing
the least ready event therefore selects the least unfinished source event.
This is source implementation by one scheduling instance of the asynchronous
semantics, not an assertion that every asynchronous policy has the source law.

Schedule-independent conclusions are separate theorems:

- With corresponding per-event actions and chance realizations, commuting
  independent events preserves the terminal binding store. Completion order
  and the physical transcript can differ.
- Equality of interpreted terminal stores implies equality of the retained
  payout expressions and of any utility supplied on those outcomes.
- Equality of outcome *laws* under policies additionally needs the appropriate
  observation and kernel-independence argument. An unchanged policy can react
  differently when the schedule changes what it observes.
- Arbitrary-deviation and Nash comparisons quantify over the asynchronous
  strategy space. They require the scheduling-information argument. The
  initial barrier compiler targets an exact comparison; only a broader runtime
  with additional informed failure uses the explicit utility condition.

These statements have different hypotheses. Final-store commutation alone
does not establish strategic preservation, and no equality of full transcripts
is needed for an outcome-based utility theorem.

When composing, the two certificates must name exactly the same middle game,
strategy compiler, outcome interpretation, and environment parameters. There
is a particular pitfall: a native scheduler sees packet contents absent from a
coarse graph scheduler's view. One cannot assume it factors through a single
graph scheduling policy independent of player replacements.

The safe initial backend interface compares each admitted native environment
directly with the canonical EventGraph game, using graph-local causal and
scheduling lemmas. For the conservative barrier compiler, both edges target
exact finite-mixture simulation and compose through mixture composition. If a
later concurrency extension demonstrably adds informed failure, convert the
exact source edge to utility simulation, prove the separate feasible-repair
bound, and compose using `UtilitySimulation.trans`.
A separate native-to-asynchronous-graph certificate is
appropriate only if its environment interface retains enough information and
its quantifiers actually match. No source-relative backend proof is needed.

This keeps a unified operational tower without pretending that an unproved
environment factorization is an implementation edge. Canonical and asynchronous
graph runs share node code and transitions. The canonical specialization must
not be the only interpreter exercised by the asynchronous headline theorem.

## 7. Proof approach and mathematical gates

### Gate A: information-safe commutation

For two simultaneously enabled independent events e and f, prove the typed
state-update diamond and the relevant kernel commutation:

```text
step(e); step(f) = step(f); step(e)
```

The equation compares laws after identifying the same completed cut and field
layout. It requires that each unchanged player's decision kernel sees the same
logical observation and own history in either order. For the first compiler,
the basic case is commitments by different owners between public barriers.
Samples require the conditional joint-law argument, not marginal fairness.
Conflicting deferred resolutions must not be classified as independent.

Do not commute the physical transcript or scheduler policy. They can observe
different completion orders. This lemma concerns semantic effects under the
identified decision inputs; strategic scheduling needs the next gate.

### Gate B: scheduler-aware action locality

Predraw the focal player's and environment's random responses over the finite
supported execution tree, jointly across the private initial law. Leave
opponents' source kernels and application chance live.

Replace the sequential-prefix relation by a relation on downward-closed cuts,
causal pasts, and actual native histories. For a reached focal event, show that
the ordinary choice extracted from its normalized continuation is determined
by its allowed source information and the predrawn responses. Separate any
genuinely additional selective-failure decision from that choice. The initial
barrier runtime is designed not to create one: a prescribed event is sent only
when ready, public events wait for all earlier events, and prescribed bind
traffic has the same opaque shape even when the source action is failure.
Source-incomparable opponent commitment completions must not reveal their
candidate meanings.
The deviator's arbitrary raw announcements remain in the replayed public
history; they are not assumed absent or harmless without proof.

Use immutable accepted bindings and verified publication results for action
extraction, never untrusted focal cache entries. For source-representable
failure, resolution can extract canonical withholding while the native policy
remembers a different intention. The replay/locality relation must carry that
native memory explicitly. For the initial compiler, prove that every such
failure is an existing graph bind failure or publication withholding choice.
Only a broader runtime with a genuinely new informed-failure choice compares
that choice with its feasible repair using the condition in Section 6.

The first mathematical proof should handle two independent owners' commitment
chains with adaptive inclusion, early focal disclosure, and a subsequent public
barrier. Write the two-run exact relation, including silence and expiry, before
porting whole-program inductions. For a broader runtime, separately write the
comparison for any additional failure. If pointwise
locality fails for a normalized ordinary action, identify the exact
counterexample; consider a conditional-law witness only with a concrete need,
not as parallel speculative infrastructure.

### Gate C: continuation laws on cuts

Define the residual outcome law from a cut using a canonical completion order
and the extracted policy. State why available semantic commutations make it
appropriate for the actual ready event. Retain unchanged opponents' sampled
actions and original logical histories, including failed true intentions.

For the initial barrier runtime, prove equality at each actual native
invocation: private preparation, submission, delivery, rejected inclusion,
accepted inclusion, chance, clock, and expiry. In a broader runtime, use a
failure-related utility inequality only at a genuinely additional informed
failure choice. Adaptive selection of one of several candidates is handled only
for the actual command in the policy's support. Do not assert every pending
packet would realize the same action.

Completion identifies the terminal decoder. For the initial compiler, compose
the equalities and use finite-mixture simulation for arbitrary randomized
deviations. For the broader-runtime extension, backward utility comparisons
eliminate the additional failure choices before finite averaging supplies the
deviation bound. Invoke generic equilibrium transport once, rather than
deriving Nash separately for each event kind. Do not infer bounds for another
player's utility from a comparison only for the deviator's utility.

### Gate D: a non-vacuous service witness

Prove the bounded driver protects prescribed nodes despite arbitrary focal
traffic and still expires ineffective nodes. The witness must support genuine
alternative completion orders. Prove predrawing preserves the driver's local
service obligations, rather than assuming arbitrary pure components remain
fair without checking them.

The design gates separate genuine obstacles from proof engineering. Failure
of a chosen pointwise invariant is not an impossibility theorem. A strategic
counterexample must fix a program, profile, utility, admitted environment,
and a profitable deviation or unattainable outcome law.

## 8. Ownership, reuse, and migration

| Owner | Responsibility |
| --- | --- |
| GameTheory / GameTheoryExtensions | Game forms, finite probability, mixture composition, Nash/guarantee transport, reusable scheduler or causal-game lemmas when genuinely language-independent. |
| Interaction | Message pool, authentication, delivery/inclusion, own histories, ideal commitments, bounded invocation/service mechanisms. No source-language dependency. |
| Vegas.EventGraph | Typed events, cuts, readiness, node semantics, actual observations, graph games, and graph-level scheduling certificates. |
| Vegas.Compile | Full source lowering, dependency generation, observation reconstruction, guard specialization, and source/graph correspondence. |
| Vegas.Pending | EventGraph message application, prescribed strategies, event-relative clocks/service, native locality and outcome-law simulation. |
| Vegas.Game | Composition and source-facing capstones. |
| A target-specific host | Transactions, blocks, fees, finality, concrete cryptography and VM execution, with separate refinement obligations. |

Reuse the shared deferred guards, expression/result interfaces, candidate
immutability and verification, public evaluation, native message runner,
predrawing foundations, and generic simulation algebra. Inspect proofs for
their actual assumptions rather than moving whole files by name.

The most substantial replacements are the prefix/cursor representation,
phase-framing and replay relations, sequential policy scans, global service
plan, and whole-run continuation induction. Build one per-event local proof
interface; do not duplicate binding, resolution, and sample case splits across
many whole-program inductions.

Keep the checked ordered theorem while the replacement is being established,
clearly separated from prospective claims. Once the same graph supports a
canonical specialization and the asynchronous native certificate composes,
port the source wrappers and remove the separate ordered Graph/runtime path.
No compatibility aliases, permanent duplicated runners, or dormant archive
trees are required. Git retains source material needed during migration.

New generic facts belong in dedicated GameTheory-namespaced extension modules
if not yet available upstream. A bounded adaptive runner or missing probability
abstraction must be reported as a concrete library requirement; do not distort
the semantic design to avoid an appropriate library addition.

## 9. Implementation milestones and stop conditions

### M0: mathematical design and smallest witnesses

Deliver the two-owner asynchronous example, the information-edge and deferred-
guard counterexamples, a precise local service construction, and the proposed
cut/replay invariant. Identify the contracts that make the initial pending
edge exact, and state feasible repair separately for any broader runtime that
violates them. Check the needed generic APIs. This document specifies the work; its narrative examples
are not a substitute for those proofs.

Exit: the graph carrier, observation contract, and service obligations are
concrete enough to state the end-to-end goal without placeholders for the
desired simulation itself. Report any change needed to source semantics
before implementing it. No source change is currently proposed.

### M1: shared executable EventGraph interface

Implement typed identities, cuts, readiness, node transitions, public and
private observations, own-action history, canonical and noncanonical runners,
and terminal readout. Define the local causal-discipline certificate. A
failure-comparison interface is not an M1 gate for the initial exact barrier
compiler. Wire every module into the build as it is added.

Exercise all node kinds and terminal expressions with small hand-built graphs,
including initial secrets, heterogeneous payloads, deferred guards, explicit
failure, and chance. Prove local execution safety, binding-origin preservation,
and readiness facts. Two independent commitments must actually complete in
either order. These witnesses validate the graph interface without waiting
for a completed source compiler.

Exit: the common interface below compiles, the witnesses run with the expected
results, and both edge owners can state their theorem against it. Pause and
report that the graph is ready for parallel compiler/proof work, not that
full-source lowering or Nash preservation is already proved.

### M2: upward edge, source to EventGraph

Implement full-source lowering, dependency generation, partial-view
reconstruction, guard specialization, initial-state encoding, and terminal
decoding. Prove that every source compiler output satisfies the graph's local
causal-discipline certificate. Port exact canonical source correspondence,
including arbitrary graph-policy backtranslation, private setup, and original
own-action recall. Preserve the distinction between source-order canonical
execution and other ready schedules.

Exit: every source constructor compiles, compiler outputs have the graph
certificate, and source/canonical-graph strategic correspondence is checked.
The theorem depends on graph definitions and local graph lemmas, not pending
messages, clocks, service, or a graph/native correctness proof.

M2 runs in parallel with M3 and M4 after M1. Backend implementation and proof
do not wait for this source edge to finish.

### M3: asynchronous native implementation and honest laws

Checked: event-readiness dispatch, event caches, source-history projection,
relative deadlines, and concrete bounded service over the shared message
runner. Integrity and completion hold under arbitrary players. The full honest
law composes graph-relative service refinement with the source-to-graph law.

Exit: the actual public-message game permits alternative binding acceptance
orders, early arbitrary packets, and adaptive delivery. Honest outcomes match
the full source, and completion is proved. This exit criterion is met; the
arbitrary-deviation obligation is M4.

### M4: asynchronous native deviation capstone

Prove information-safe commutation and the graph scheduling comparison, then
cut-based native locality and the exact finite-mixture deviation law for the
initial public-barrier pending compiler. Lift through setup-wide predrawing and
package the graph-relative certificate. The graph scheduler's observation interface remains distinct
from the richer native wire scheduler; their identification is not assumed.
The scheduling mathematics can proceed while M3 establishes the native
handlers and service facts it will consume.

The backend theorem quantifies over independently certified EventGraphs, graph
policies, and setup laws. It contains no source program or source-relative
correctness hypothesis. Its initial exact law yields arbitrary
source-observable unilateral guarantees and same-error Nash correspondence.
A broader runtime that exposes new information before failure has a separate
utility-dependent M4 extension using the feasible-repair contract; do not
weaken the initial theorem preemptively.

After both M2 and the backend certificate are complete, compose them by the
generic simulation theorem and discharge the source-facing capstones. This
join should introduce no new whole-execution induction.

Exit: the theorem names the full source compiler and actual asynchronous
native runner. Its deviator is unrestricted within that runner. Any changed
assumption is reported with a reason, not hidden by a restricted policy class.
Once expressible, only these prospective capstones belong as explicitly
unproved statements in `Paper.lean`; supporting obligations stay in their
owning modules. The milestone closes only when those proofs are discharged.

### M5: consolidation and next runtime edge

Make the dependency-driven compiler the active path. Retain canonical order
only as a scheduler instance/reference specialization of the same semantics.
Delete consumed ordered-only implementations and proofs, update public
documentation and the capstone audit, and run the complete warning-free build
and repository checks.

Exit: there is one active operational tower, the theorem quantifies over
actual asynchronous completion orders, and the next transaction/block host
can implement the event-relative integrity and service contracts. Finer
dependency reduction is a separate proof-backed pass, not a prerequisite for
claiming this first full-language asynchronous result.

### Parallel dependency structure and interface freeze

The milestone numbers identify deliverables, not a sequential work queue:

```text
            M0: shared mathematical contracts
                          |
            M1: executable EventGraph interface
                          |
              +-----------+-----------+
              |                       |
      M2: source -> graph      M3/M4: graph -> native
      lowering + exact         async runtime + service
      correspondence           + exact deviation law
              |                       |
              +-----------+-----------+
                          |
               end-to-end composition
                          |
                  M5: consolidation
```

Freeze the following common meanings before the two edge proofs expand:

1. **Execution.** Typed event and field identity, binding origins, cuts,
   readiness, atomic bind/resolve/sample effects, deferred validation, and
   completed failure versus an unfinished event.
2. **Strategies and observations.** Logical decision views, private action
   recall, canonical graph policies, actual asynchronous observations, and
   the precise canonical graph game used as the shared middle game.
3. **Outcomes and setup.** Initial layout independent of sampled input values,
   initial-environment laws, terminal readout, and utilities of graph outcomes.
   Strategy witnesses are chosen before the private setup draw on both edges.
4. **Local graph certificate.** Typed availability, causal information
   discipline, origin consistency, and effect constraints. The source edge
   proves the certificate; the backend consumes it. It contains no assumed
   end-to-end law and no source syntax.
5. **Failure comparison extension.** This is not required for the initial
   exact barrier compiler. A broader runtime that exposes new semantic
   information before failure must separately define feasible continuation and
   failure relations, their utility condition, and the information at which
   the comparison holds. See the
   [failure-comparison note](event-graph-failure-comparison.md).
6. **Certificate scope.** Matching strategy translations and outcome maps,
   all-profile versus profile-local premises, and the environment parameters
   of the exact or utility simulation being composed.

Freezing these definitions does not mean proving both edges first. It means
that independent implementers can name the same middle game and local
obligations without inventing each other's semantics. If a genuine interface
defect is found, revise it jointly; do not hide the mismatch in a compatibility
wrapper or a new source-relative backend assumption.

Assign one owner to the shared EventGraph definitions and integration. After
M1, assign separate upward and downward owners. The downward work can further
separate handler/service proofs from failure and scheduling mathematics,
provided the local runtime interface is shared rather than duplicated. Tests
and independent review can proceed alongside either edge. Keep each agent's
file ownership disjoint; one integration owner wires aggregators and build
roots. The shared checkout needs no worktrees.

Useful work before M1 includes dependency/guard mathematics, service design,
historical lemma inspection, and counterexample tests. It must feed the one
graph interface, not produce competing semantic models. No elapsed-time or
line-count estimate substitutes for the milestone exit tests.

At each milestone report source coverage, allowed asynchronous behavior,
strategic conclusion, service/information assumptions, and the next unproved
edge. File counts and local lemma counts are not completion criteria.

## 10. Required regression matrix

The matrix is a bounded acceptance checklist, not a request for a new theorem
registry. Strong source-facing statements remain in `Paper.lean`.

| Case | Required result |
| --- | --- |
| Independent A/B commitments | Both acceptance orders occur; compiled-profile terminal laws agree with source and the stated unilateral strategic guarantee holds. |
| Multiple commitments by one owner | Logical choice history and sample-once caches are preserved. |
| Focal early announcement | Packet is observable; compiled opponents retain their source kernels; deviation remains covered. |
| Silence or expiry in the initial barrier runtime | Native behavior remains allowed and backtranslates exactly to graph failure/withholding under readiness-gated uniform traffic and service. |
| Additional informed failure in a broader runtime | Feasible normalization and the failure-disincentive premise yield a utility bound; no exact law is claimed without proof. |
| Prescribed premature opening | Rejected as a compiler behavior when it crosses an information barrier, even if application inclusion would reject it. |
| Payload-inspecting environment | Excluded only when it inspects sealed private material; ordinary public-packet inspection remains allowed. |
| Deferred equality/parity guard | Publication order and failure attribution match source; invalid reorderings are detected. |
| Empty payload or false guard | Program still compiles and completes with explicit failures. |
| Initial private setup | A single source-policy witness, or mixture for an exact-law result, works across the whole initial law. |
| Chance | Correct conditional joint law, no reroll, no strategic publisher. |
| Competing candidates and replay | Accepted meaning immutable; only the actually selected packet determines the effective action. |
| Concurrent deadlines | Unrelated progress cannot censor a compliant ready event; ineffective owners resolve by failure. |
| Runtime-only fees or trace utilities | Not inferred from terminal-source-state guarantees; require a separate interpretation/refinement. |

No row may be satisfied by deleting the behavior from the arbitrary native
policy space, except a capability genuinely unavailable in the specified
runtime, such as inspecting an ideal sealed candidate without an opening.
