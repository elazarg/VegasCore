# Dependency-driven EventGraph: design and implementation plan

## Status and objective

This document specifies a proposed asynchronous compiler target and the work
needed to prove its strategic correctness. It does not describe a checked
asynchronous theorem. The [active theorem map](active-tower.md) records the
existing source-to-ordered-graph-to-pending-message results.

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
For the proposed exact-mixture theorem, there must be a source deviation, or
finite mixture, with the same decoded outcome law against those unchanged
opponents. This is stronger than merely ruling out profitable deviations.

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

Failure of exact outcome-law simulation likewise does not by itself refute
Nash preservation for a fixed utility interpretation. The plan seeks the
stronger, utility-independent exact certificate. Its conservative information
barriers are sufficient proof conditions, not a claim that every such barrier
is necessary for every game's Nash equilibria. Relaxing a barrier can instead
be justified by a separate utility-dependent theorem.
No failure-dominance premise is proposed for the asynchronous edge unless an
actual additional, source-unavailable choice is identified and shown to need it.

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

### 4.4 Further dependency reduction

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

## 6. Strategic statements and composition

Fix a source program P, finite private setup law rho, a realizable service
configuration, and an admitted public environment policy E. Let C be the
actual playerwise strategy compiler and d the terminal-state decoder.
The target theorem is:

```text
completion:
  every supported asynchronous native execution has a decoded outcome,
  for arbitrary native player policies

honest law:
  map d (native[P, rho, E].play (C sigma))
    = map some (source[P, rho].play sigma)

unilateral deviation law:
  for every sigma, player i, and arbitrary native policy tau_i,
  there exists a finite law mu on source policies for i such that

  map d (native[P, rho, E].play ((C sigma)[i <- tau_i]))
    = bind mu (fun pi_i =>
        map some (source[P, rho].play (sigma[i <- pi_i])))
```

The mixture is chosen before the draw from rho. Opponents are unchanged.
The witness can depend on sigma, E, and tau_i. E is fixed as a policy, not as a
preselected command trace, and can react to the deviator's public messages.
No finite payload-domain or guard-feasibility premise is intended.

Package the exact law in the existing
[mixture simulation interface](../GameTheoryExtensions/Core/MixtureSimulation.lean).
Use its [composition theorem](../GameTheoryExtensions/Core/MixtureSimulationComposition.lean)
and equilibrium/observable-bound consequences. Utilities range over decoded
source terminal states; extra trace preferences require their own contract.
Keep completion's missing-result case distinct from source publication failure.

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

When composing, the two certificates must name exactly the same middle game,
strategy compiler, outcome interpretation, and environment parameters. There
is a particular pitfall: a native scheduler sees packet contents absent from a
coarse graph scheduler's view. One cannot assume it factors through a single
graph scheduling policy independent of player replacements.

The safe initial backend interface simulates each admitted native environment
directly into the canonical EventGraph game, using graph-local causal and
scheduling lemmas. Then it composes with the source edge through the existing
mixture certificate. A separate native-to-asynchronous-graph certificate is
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
the effective action extracted at acceptance or expiry is determined by its
allowed source information and the predrawn responses. Source-incomparable
opponent commitment completions must not reveal their candidate meanings.
The deviator's arbitrary raw announcements remain in the replayed public
history; they are not assumed absent or harmless without proof.

Use immutable accepted bindings and verified publication results for action
extraction, never untrusted focal cache entries. Failed resolution can extract
canonical withholding while the native policy remembers a different intention.
The replay/locality relation must carry that native memory explicitly.

The first mathematical proof should handle two independent owners' commitment
chains with adaptive inclusion, early focal disclosure, and a subsequent public
barrier. Write the two-run relation and prove single-valued effective actions
before porting whole-program inductions. If pointwise locality fails, identify
the exact counterexample; consider a conditional-law witness only with a
concrete need, not as parallel speculative infrastructure.

### Gate C: continuation laws on cuts

Define the residual outcome law from a cut using a canonical completion order
and the extracted policy. State why available semantic commutations make it
appropriate for the actual ready event. Retain unchanged opponents' sampled
actions and original logical histories, including failed true intentions.

Prove conservation at each actual native invocation: private preparation,
submission, delivery, rejected inclusion, accepted inclusion, chance, clock,
and expiry. Adaptive selection of one of several candidates is handled only
for the actual command in the policy's support. Do not assert every pending
packet would realize the same action.

Completion turns this residual law into the terminal decoder. Finite averaging
then yields the arbitrary randomized deviation law. Invoke generic equilibrium
transport once, rather than deriving Nash separately for each event kind.

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
plan, and whole-run conservation induction. Build one per-event local proof
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
cut/replay invariant. Check the needed generic APIs. This document specifies
the work; its narrative examples are not a substitute for those proofs.

Exit: the graph carrier, observation contract, and service obligations are
concrete enough to state the end-to-end goal without placeholders for the
desired simulation itself. Report any change needed to source semantics
before implementing it. No source change is currently proposed.

### M1: executable EventGraph and full-source lowering

Implement typed identities, cuts, readiness, node transitions, canonical and
noncanonical runners, compiler dependencies, partial-view reconstruction,
guard specialization, and terminal decoding. Wire every module into the build
as it is added.

Exit: all four source constructors compile; two independent commitments
actually complete in either order; unsafe early prescribed publication is
prevented by emitted dependencies; guard/order examples have the specified
results. Execution safety, binding origin, and readiness are proved. Pause
and report that the models/compiler exist, not that Nash is already proved.

### M2: source and asynchronous graph strategic correspondence

Port canonical source correspondence. Prove information-safe commutation and
the graph scheduler's honest and arbitrary unilateral-deviation laws under
its explicit observation contract. Include finite private setup, not a
separate strategy chosen after each secret realization.

Exit: an actual ready-event graph game has a checked exact-mixture certificate
and same-error Nash theorem. State its scheduler interface precisely; do not
identify it with the richer native wire scheduler without proof.

### M3: asynchronous native implementation and honest laws

Replace current-phase dispatch with event readiness; implement event caches,
source-history projection, relative deadlines, and the concrete bounded
service. Reuse the shared message runner. Prove integrity, failure behavior,
completion under arbitrary players, and the full honest law.

Exit: the actual public-message game permits alternative binding acceptance
orders, early arbitrary packets, and adaptive delivery. Honest outcomes match
the full source, and completion is proved. Pause with the remaining arbitrary-
deviation obligation explicit.

### M4: asynchronous native deviation capstone

Prove cut-based native locality and continuation conservation, lift through
setup-wide predrawing, package the graph-relative certificate, and compose
with the source edge. Obtain same-error Nash correspondence and arbitrary
source-observable unilateral guarantees by delegation.

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

### Parallel work boundaries

When delegation is used, independent useful tracks are: (1) dependency and
guard mathematics with counterexamples; (2) public scheduler/service design;
(3) typed-cut representation and compiler interface; and (4) independent
review of theorem quantifiers and early-disclosure arguments. These can run
before the interfaces freeze. Assign Lean ownership by module afterward;
avoid concurrent edits to shared graph definitions and aggregators.

Suggested ownership follows the dependencies of the work:

1. During M0, keep the dependency/guard analysis and service construction
   independent; have a reviewer test whether their observation assumptions
   compose, including the early-disclosure cases.
2. During M1, give one implementer the graph carrier/semantics and another
   source dependency generation after the carrier interface is agreed. Put
   example construction and API validation in a third bounded track.
3. During M2, separate canonical source correspondence from the scheduling
   argument; both consume the same local graph certificate.
4. During M3, separate handler integrity from prescribed-policy history and
   from service protection. Do not parallelize by cloning a policy runner.
5. During M4, keep the cut-locality and residual-law interfaces under one
   owner. Other agents can prove their local premises, test counterexamples,
   or review quantifiers without competing edits to the central induction.

Use implementation agents for bounded Lean tasks and independent mathematical
review when a proof interface is unsettled. No elapsed-time or line-count
estimate substitutes for the milestone exit tests.

At each milestone report source coverage, allowed asynchronous behavior,
strategic conclusion, service/information assumptions, and the next unproved
edge. File counts and local lemma counts are not completion criteria.

## 10. Required regression matrix

The matrix is a bounded acceptance checklist, not a request for a new theorem
registry. Strong source-facing statements remain in `Paper.lean`.

| Case | Required result |
| --- | --- |
| Independent A/B commitments | Both acceptance orders occur; terminal laws and unilateral strategic guarantees agree with source. |
| Multiple commitments by one owner | Logical choice history and sample-once caches are preserved. |
| Focal early announcement | Packet is observable; compiled opponents retain their source kernels; deviation remains covered. |
| Prescribed premature opening | Rejected as a compiler behavior when it crosses an information barrier, even if application inclusion would reject it. |
| Payload-inspecting environment | Excluded only when it inspects sealed private material; ordinary public-packet inspection remains allowed. |
| Deferred equality/parity guard | Publication order and failure attribution match source; invalid reorderings are detected. |
| Empty payload or false guard | Program still compiles and completes with explicit failures. |
| Initial private setup | One source-policy mixture works across the whole initial law. |
| Chance | Correct conditional joint law, no reroll, no strategic publisher. |
| Competing candidates and replay | Accepted meaning immutable; only the actually selected packet determines the effective action. |
| Concurrent deadlines | Unrelated progress cannot censor a compliant ready event; ineffective owners resolve by failure. |
| Runtime-only fees or trace utilities | Not inferred from terminal-source-state guarantees; require a separate interpretation/refinement. |

No row may be satisfied by deleting the behavior from the arbitrary native
policy space, except a capability genuinely unavailable in the specified
runtime, such as inspecting an ideal sealed candidate without an opening.
