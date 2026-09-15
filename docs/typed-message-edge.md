# Typed graph to public-message edge

`GraphRuntime` realizes an ordered `Vegas.Graph` directly as a public-message
application. It does not pass through source syntax or `Vegas.EventGraph`.
The graph remains the strategic specification; the native execution adds
transport, candidate preparation, inclusion receipts, and relative deadlines.

## Runtime boundary

The runtime type is attached to one terminal context and directly interprets
the remaining typed graph. Its state keeps a full ideal `VEnv` as private
materialization, while `PublicValues` separately stores the only values supplied
to public expression and guard evaluation. The public state contains that
public graph prefix, the current canonical phase and its deadline state.

Accepted handle identifiers are public. An authenticated player also sees its
own prepared candidate meanings; other players and the environment do not.
The ideal commitment verifier checks an opening against its candidate. Guard
evaluation receives only the verified proposal and public fields; it cannot
query hidden candidate meanings or the private materialized environment.

Phases follow graph order, including operations without data dependencies.
Only the current phase accepts a graph-effective message. Malformed, early,
late, replayed, and rejected traffic remains ordinary native traffic: it may
remain pending, be delivered, and receive a rejection receipt, but it does not
advance the graph prefix.

Public pending means recipient-local delivery before public inclusion. A
message in the shared transport pool is not thereby common knowledge. The edge
uses the existing pool view and must not replace it by a globally visible pool.

The phase implementations are:

* `bind`: the owner submits a candidate handle. Inclusion accepts the first
  eligible handle without testing its opening. Acceptance fixes a fresh handle
  as unopenable and preserves an already prepared value. Extra preparation is
  allowed before acceptance; preparation after acceptance cannot alter it.
* `resolve`: the owner may submit an opening of the handle selected by the
  corresponding bind. The public handler computes `Graph.acceptedProposal`
  from the verified wire proposal and `PublicValues`. Successful inclusion
  atomically appends the accepted `Result` field. Withholding, absence of a
  valid opening through the relative deadline, or an authenticated,
  commitment-verified proposal rejected by its guard appends failure. A packet
  failing authentication, commitment verification, or type decoding is instead
  rejected without advancing the graph. No private guard evaluator is available.
* `sample`: once this phase is reached, a fixed application kernel draws once
  from the graph's `PublicDist` evaluated on the public prefix. Neither a
  player nor the scheduling environment selects the value, rerolls it, or
  substitutes a candidate. The chance transition appends its field atomically.
* `ret`: the completed typed environment is decoded without a layout cast.

Fixed setup generates immutable candidate material and public accepted handles
for sealed initial fields separately from the public graph code. Initial fields
do not execute a fresh source bind choice. There is no automatic disclosure:
their later graph resolution still requires an explicit opening or withholding.
Initial handles are keyed by field name. A correspondence theorem therefore
requires unique initial field names, as supplied by `SourceProgram.Initial`;
graph constructors enforce freshness of every subsequently added field.

### Binding-origin certificate

The backend's semantic certificate also retains each bound field's original
payload type. `Graph.BindingDiscipline` threads a name-to-payload map through
binds and checks it at resolves. Both `Initial.graph_bindingDiscipline` and
`Setup.graph_bindingDiscipline` prove this property for the source compiler's
complete output. It is proof data, not another runtime or a source restriction.

This distinction matters for the abstract expression interface. `ResultTypes`
does not require its result-type constructor to be injective. Two payload
types can share a representation type while their decoding equivalences assign
different meanings to the same element. For example, two singleton payload
types can share a two-element result representation: one decoder treats `0`
as failure, while the other treats `0` as success. A hand-built graph that binds
at the first payload and resolves at the second can reinterpret a failed
binding as successful. Mere equality of representation types does not exclude
that graph.

The source retains the payload identity in its private-field type and compiles
both operations using that identity. The graph certificate exposes this fact
to a source-independent backend proof. The expression interface does not need
an additional injectivity or representation-coherence assumption.

## Prescribed policies and observations

`MessagePolicies` implements the policy translation below. `MessagePolicyLaws`
connects the actual command kernels to graph choices and checks uniform failed
disclosure. `MessageServiceLaw` factors a fresh bind or resolve invocation
through its graph kernel with an arbitrary remaining native schedule and
environment. `MessageBindingLaw` and
`MessageResolutionLaw` compose prescribed submission with reserved inclusion
through the actual shared runner. Resolution installs the graph's accepted
result for both logical Booleans, including guard rejection; only successful
publication requires an opening witness. `State.initial_binding` constructs
that witness for every sealed initial field under name uniqueness.
`MessageBindingProvenance` preserves origin-indexed field/handle association
through arbitrary native policy execution, including failed binds and clock
expiry. `State.resolveSource_verified` derives the exact owner-correct verifier
for a successful resolution at a disciplined graph cursor; the local
submission law consumes this invariant instead of assuming an opening witness.
`MessageVerification` separately proves that once an opening verifies, every
supported policy-driven continuation preserves that exact verifier.

This is a strategy translation used to compare games. The contract does not
require players to run generated client software: native deviations still
range over every policy admitted by the open message runtime.

The compiled bind policy prepares the chosen encoded `Result` before submitting
its handle. This includes `Result.failure`: it may sit behind an opaque
openable handle and need not be represented by a fresh candidate. Binding has
no reveal requirement and performs no public early-failure optimization. A
compiled resolve policy prechecks the public guard computation. It submits the
raw value only when disclosure succeeds.

Withholding and guard-rejected disclosure use the same canonical public packet
shape and timing, so they do not signal the omitted logical Boolean. The Bool
is retained only in authenticated compiler memory. This failure realization is
part of the prescribed policy, not a property supplied by phase gating.
`compileAt_resolve_result` proves that the second command is determined by the
accepted graph result and public address. The compiler constructs that command
with `disclosureCommand`; a successful packet contains the canonical encoding
of its published value. The acceptance proof consumes this factorization.

Compiler-private memory records the selected bind choice even when it is
failure, and records the logical resolve Boolean. In particular,
`disclose = true` followed by guard rejection is distinguishable from
`disclose = false` at later decisions although both public fields are failure.
`MessageHistoryExtension` proves the whole original-graph scan's extension
laws for bind, resolve, and sample, and its invariance under fresh immutable
field extension. Appending a marker at the current phase leaves the earlier
logical history unchanged.
In `MessagePhaseFrame`, `runPolicies_projectLogicalHistory_before` lifts that
fact to arbitrary native policy runs: newly recorded commands cannot change the
history scan of already passed sites, for a fixed observation. Its companion
`runPolicies_running_eq_of_phase_eq` proves that a run remaining at one phase
preserves the exact typed graph, ideal values, public values, and accepted
binding addresses. Candidate preparation, clocks, pools, and receipts may
still change.
Together with the visible graph prefix, this reconstructs exactly the graph
`DecisionView`.

Compiled opponents project their native histories and views to that decision
view. They ignore unrelated pending packets, delivery state, receipts, clock
noise, and rejected raw payloads. The two protections have different roles:
prechecking prevents a prescribed player from leaking data omitted by the
graph; projection prevents an unchanged compiled opponent from acquiring a
new response to traffic sent by a deviator. Canonical phase gating alone does
not provide either property.

The implementation is a recursive policy compiler over the fixed graph,
its behavioral policy, and the public program counter. It advances graph and
policy tails together; a context or owner mismatch totalizes to native `wait`.
It uses the shared message runner, with no additional protocol interpreter.
For completed owned bindings, reconstruct logical bind history directly from
the immutable fields in the current private observation, transporting their
typed references through the completed prefix. Candidate-table lookup is
unnecessary for those past actions. Completed resolve Booleans instead come
from site-indexed own-history markers, since result fields do not determine them.
The cursor retains the original graph when traversing its current tail: the
history projection scans completed operations of that original graph.
`Prefix` in `MessagePolicyHistory.lean` is a typed prefix witness in the
`Vegas.GraphRuntime` namespace, not another execution model. Its compiler
cursor theorem equates the actual root policy with its residual policy at that
suffix. It preserves context-name uniqueness, and typed owned-field lookup
recovers the stored binding choice. The logical-history projection theorem
still requires agreement with the completed graph actions; that agreement
must be established along the execution coupling.

At a current bind, choose once and prepare slot `.prepared pc`; on the next
invocation submit its commitment, then wait. At a current resolve, choose and
remember the Boolean once; next submit the prechecked opening or the uniform
withhold packet, then wait. Own command history detects prior preparation,
memory, and submission without relying on scheduling-dependent receipts.
Both successful and failed prescribed play use the same number of local
invocations before submission. The local kernel and submission laws, initialized
provenance invariants, and whole-run honest law are checked. Observation-local
extraction of arbitrary native deviations remains proof work.
`MessagePolicyCommands` proves that every supported compiled command is
addressed to the active phase, never malformed or replayed. Once a submission
is recorded for that phase, the policy waits while it remains active. These
restrictions concern unchanged compiled players; deviations remain unrestricted.
In `MessagePreparationInvariant`, `runPolicies_initial_preparationInvariant`
derives exact agreement between one compiled player's preparation history and
its candidate catalog from the actual empty-pool initialization. Other player
and environment policies are arbitrary. The invariant combines authenticated
message provenance, canonical prepared-slot values, and the fact that every
own commitment follows a preparation. It rules out acceptance of a still-fresh
canonical handle of that player; already prepared handles retain their value
through acceptance. No candidate/history agreement is assumed for the initial
run, and arbitrary deviators are not required to follow this invariant.
`MessagePolicyFreshness` derives the corresponding own-history invariant from
the actual initial execution and preserves it through the shared runner with
arbitrary opponents and environment. All recorded phases are at most the
current phase, and the three compiler caches are empty at strictly future
phases. This is a phase bound, not the still-needed equality with graph
decision histories.

## Concrete bounded service

`MessageService` expands the fixed graph into a list of invocations for the
shared runner. Each binding or disclosure phase gives its owner two calls,
then a parameterized number of wire/reaction rounds, a reserved inclusion of
the owner's latest pending submission, and `max 1 (deadline phase)` expiry
opportunities. A wire/reaction round gives the arbitrary wire policy one call,
followed by player calls from a supplied finite roster. Chance has one reserved
progress call. No new execution interpreter is introduced.

Expiry is gated by the expected graph phase: if inclusion already completed
that phase, its reserved tick waits. This prevents an early successful message
from spending a later phase's deadline. The wire policy receives its actual
history and public pool and may deliver, include, or wait. It cannot insert
additional application ticks. Player commands at reaction slots are unrestricted.

Early wire inclusion can advance the application into a later graph phase
before the current service block has finished. The proof must therefore allow
the runtime to be ahead of the planned phase, rather than treating every
reaction as a stutter. `MessageServiceCursor` proves that the environment's
actual history selects the intended slot after any supported invocation prefix.
Reserved inclusion selects the newest allocated identifier if it is still
pending, not an arbitrary older pending message. The unchanged player's
one-submission-per-active-phase property is needed to show that this selection
protects its prescribed packet.

`MessageApplication.Authorship` connects sender-local serials to the actual
authenticated submission history and is preserved from the empty initial
pool through arbitrary policies. In particular, a pending envelope's exact
identifier looks up that same envelope, even when replay produces duplicates.
`MessageServiceProtection` uses this invariant, exact envelope retention,
and the unchanged sender's counter stability to prove phase advancement at
reserved inclusion. That statement alone also permits earlier expiry.
`runPolicies_service_reactions_clock` separately proves that the entire actual
reaction prefix preserves the application clock. Its wire slots execute the
supplied wire policy and cannot request application ticks. The combined bind
service theorem therefore distinguishes clock-preserving early advancement
from advancement at reserved inclusion. Honest chosen-value preservation still
requires preparation and disclosure agreement throughout the actual service.

These are service restrictions, not a characterization of every deadline-fair
environment. The graph-to-message capstones quantify over every supplied wire
policy, roster, reaction-round count, deadline function, and source profile.
Positive reaction counts with an appropriate roster exercise pending delivery
and reactions before reserved inclusion. Other service realizations can be
added after the exact certificate is established for this concrete one.

An application tick combines clock advancement with expiry/chance execution.
A lower transaction runtime must realize that progress service through actual
calls. Clock observation alone does not run a contract. Separating clock
advancement from progress also requires rejection of openings after their
deadline even if an expiry call has not yet been included.

`MessageProgress` proves a finite tick budget for every graph and its decrease
through arbitrary native actions. `MessageServiceTermination` uses the actual
environment cursor and phase-gated expiry blocks to prove that every supported
play of the concrete service terminates, with arbitrary player and wire
policies. The typed suffix invariant allows early inclusion to advance past
planned phases. This theorem composes to `Setup.pendingGame_complete` for the
actual source compiler's target, including its finite private initial law.
It establishes completion independently of timely inclusion.
`MessageHonestServiceSafety` separately proves that each prescribed owner block
advances before its expiry slots. `MessageServiceSafety` lifts this fact through
the full graph, including executions already ahead of the nominal service phase.

## Private initial setup

`SourceProgram.Setup` supplies a finite distribution of initially pending typed
states. One behavioral policy is used across the distribution. Its checked
source-to-graph deviation law uses a backtranslation independent of the sampled
state. `Setup.pendingGame` initializes the native host from the same law and
uses the concrete composed `compilePendingStrategy`.

This quantifier order matters. For each fixed hidden bit, some constant guess
is correct; that observation proves nothing about guessing a fair private bit
using one uninformed policy. A native deviation mixture may depend on the setup
law, profile, and wire policy, but must be chosen before the realized hidden
state. Predrawing separately at each realized initial state is insufficient.

## Honest law and remaining strategic proof

The operational host, policy compiler, local laws, and service termination are
checked. The shared-prior predrawing theorem and whole-run honest continuation
identity are checked as well. `GraphRuntime.servicedGame_honest_law` proves the
graph outcome law, and `Setup.pendingGame_honest_law` composes it with source
compilation under the same private initial law. `Paper.lean` delegates its
completion and honest-law capstones to these repository theorems.
Observation-local extraction and the deviation law remain proof work; the
deviation-mixture and epsilon-Nash capstones are the two explicit admissions.
No supporting library lemma is admitted.
The checked `Setup.pendingGame_approximate_nash_of_compiled` gives the reverse
incentive direction already: an epsilon-Nash compiled target profile has an
epsilon-Nash source profile. It uses honest utility equality for every source
profile, including compiled source deviations. It does not bound arbitrary
native deviations and therefore does not prove source-to-target preservation.

### Reachable-prefix invariant

For a fixed graph and its actual service plan, the proof tracks a native
execution prefix, the unconsumed service instructions, and a typed graph
suffix. The invariant must establish:

1. the native completed phase count equals the typed graph prefix length;
2. the concrete public values equal the public projection of the ideal typed
   environment, including failures and chance values;
3. each accepted bind handle has the binding meaning represented in the
   ideal environment, privately to its owner;
4. every compiled principal's projected observation and compiler memory equal
   its graph observation and own logical action history; and
5. any prescribed choice already sampled for the current phase is retained
   with its original graph decision view and kernel until that phase completes;
6. the residual service supplies the required submission and inclusion
   opportunities before the phase's expiry slots.

The last item matters because sampling and inclusion are different native
steps. A bind kernel is sampled during private preparation, and a disclosure
kernel during private Boolean recording. The residual outcome law carries
that draw through intervening wire actions; it must not sample again or
evaluate the policy at a later observation. The service cursor is essential:
with an arbitrary tick schedule, a prepared choice could expire before
inclusion, so treating it as the fixed successful continuation would be wrong.

The relation deliberately does not equate the raw native transcript with a
graph trace. The decoded outcome may contain the full typed graph environment,
including privately represented binding meanings. Pending and malformed
packets, delivery records, and receipts have no graph counterpart.

Local extension lemmas cover one effective bind, resolve, or sample transition
and native actions that do not advance the graph. Such public transitions are
not information-free: recipient-local delivery, pending packets, and receipts
can affect later native responses. Pointwise replay must retain them while the
compiled policies' canonical handles, packet timing, and failure packets avoid
signalling information absent from graph observations.

Deadline-relative service is used to show prescribed effective messages are
included before their phase expires and hence to prove the honest completed
law. It must protect unchanged players throughout every supported deviating
execution, not just the all-prescribed run. Arbitrary focal delay or withholding
maps to the graph's failure choice. Sufficient clock progress must separately
ensure completion; inclusion fairness alone does not make time advance.

### Target finite-run deviation theorem

Fix a graph profile, a focal principal, one admissible adaptive environment,
and a bounded finite invocation schedule long enough for guaranteed completion
under the stated service and clock contract. Replace only the focal compiled
policy by an arbitrary native behavioral policy. The target construction is a
finite distribution of pairs

```text
(focal deterministic response, environment deterministic response)
```

and, for every supported response pair, an extracted focal graph policy whose
continuation law agrees with the native execution. Binding over the
response-pair distribution must give:

* exactly the original deviating native trace law on the native marginal;
* a finite mixture of graph laws with only the focal graph policy replaced;
* unchanged graph kernels for every opponent and for graph chance; and
* equality of the decoded full graph-environment law at the completed boundary.

For the probability argument, an outstanding prescribed draw must be treated
as already sampled. A useful continuation law at a native prefix is the graph's
remaining terminal-outcome distribution, with the current action fixed if its
prepare/disclosure marker has already been recorded. Before that marker it
still averages over the graph decision kernel. After inclusion, the same law
is the ordinary continuation at the next graph node. This is equivalent to a
coupling whose graph side may be one step ahead while a prescribed submission
awaits inclusion.

`MessageContinuation` defines this residual `continuation` law over a typed
graph suffix, explicit logical histories, and cached runtime commands. The
checked `continuation_empty_eq_runWith` identifies it with graph execution
when caches are empty, including arbitrary starting logical histories and
later chance kernels. `continuation_initial_eq_run` supplies the initial
case. The bind and resolve averaging laws identify the uncached continuation
with the graph kernel averaged over continuations containing the recorded
prepare or disclosure command. This evaluator is proof data; it adds neither
a game nor an operational interpreter to the compilation tower.

In `MessageContinuationPolicy`, `continuation_compiled_player_invoke` proves
the expectation identity for every actual
compiled player invocation at a typed prefix of the original graph. Fresh
bind and resolve decisions sample the graph kernel. Previously sampled
decisions, public submissions, and waits preserve the cached continuation.
The theorem derives the decision view and uses the resulting authenticated
history, without an abstract policy-kernel premise. Only the invoked player
must use its compiled policy. This covers player invocations, not the complete
interval through packet acceptance and expiry service.

`MessageContinuationAt` evaluates that same residual law using the actual
native state and a `State.Follows` witness. Typed-prefix uniqueness removes any
dependence on the chosen witness. The domain excludes off-graph states; this
definition introduces no runtime state or operational interpreter.
`continuationAt_compiled_player_invoke` reads both sides of its equation at
the actual executions, rather than a fixed suffix supplied for all successors.
Its initial and terminal equations connect graph execution to the actual
terminal ideal environment.

`continuationAt_initialized_wire` proves the full-graph wire invocation law.
The bind case derives the cached raw value's type from the actual originating
prepare command. Without that reachability condition a fabricated wrong-typed
cache would make the equation false: the handler installs failure while the
typed continuation has no cached choice. The disclosure case uses the actual
emitting checkpoint and its persistent verifier. Sample and terminal cursors
reject all application messages, so wire traffic changes only transport state.
The shared accepted-handler rule handles delivery, rejection, and inclusion
once for these cases. `MessageContinuationClock` treats actual public chance
ticks with their probability law and proves the waiting case separately.
`MessageContinuationService` transports the same wire law to the actual
reserved `includeLatest` slot by equality of the current environment kernels,
retaining the full plan and the actual environment-history cursor.

`MessageServiceSafety` proves the expiry premise for every reached prefix of
the actual plan. A matching expiry can therefore execute only at a chance node;
prescribed bind and resolve blocks have already advanced. The generic
`runPolicies_map_bindOnSupport_conservation` composes the local equations along
labelled invocation opportunities without giving a residual value to an
off-invariant state. `MessageHonestLaw` combines this identity with the initial
and terminal continuation laws to obtain exact whole-run honest preservation.

Packet acceptance has a separate origin obligation. For an actual run from
an empty pool, `runPolicies_initial_pending_submission_origin` recovers the
original sender invocation, the selected submission command, its allocated
identifier, and supported runs before and after that command. This remains
true when another player replays the packet. The binding acceptance theorem
then identifies any accepted current packet with the compiled owner's exact
prepared value. Disclosure acceptance must additionally retain the public
precheck result and opening verification from emission to inclusion.
`accepted_initial_compiled_resolve_packet` discharges this obligation from an
actual initialized run: it recovers the emitting invocation, derives the
compiled Boolean decision, and proves that acceptance installs its exact
graph result. The same-phase frame is used backwards to identify the emitting
typed cursor from the accepting one. Initial binding discipline and unique
field names supply verification provenance; the source compiler establishes
these graph properties.

These cache equations concern prescribed players. An arbitrary deviator may
write a misleading prepare or disclosure marker, choose a different candidate,
or withhold despite recording `true`. Its native markers cannot fix the focal
graph branch. For deviation simulation, the staged relation must instead use
the focal graph action obtained by deterministic phase replay, consulting
compiler caches only for unchanged players. Establishing that this extracted
action depends only on the focal graph observation is a separate obligation;
the honest continuation evaluator does not establish it.

The local obligation is therefore `V(e) = invoke(e).bind V`, at the actual
invocation cursor and on reachable states, with this staged interpretation of
`V`. At completion, `V` is the point mass at the decoded terminal environment.
Finite bind associativity gives the checked whole-run honest law.
For arbitrary focal deviations, the continuation must instead use an
observation-local extracted focal policy and protect every unchanged player's
outstanding action; that extension is unproved.
The checked safety induction is over graph-indexed service blocks; finite-run
conservation then composes individual invocation laws. Both retain the complete service plan and
environment history: replacing the service environment by one for the
remaining instructions would reset its cursor incorrectly. Every inner step
uses the actual typed suffix, which may already be beyond the nominal block.
At a block boundary the runtime follows the nominal suffix at its base ordinal.
For bind and resolve, the owner calls, reactions, and reserved inclusion must
establish strict progress beyond that ordinal before expiry. Exact one-step
advancement is not required. Phase monotonicity then makes every tagged expiry
slot wait. Sample blocks use the actual chance-tick equation when current,
and wait if already passed. The terminal residual law supplies the final
outcome; the initial residual law supplies graph execution.

The checked `runPolicies_initial_bind_full_service_block_advances` and
`resolve_full_service_block_advances` provide that strict-progress conclusion
from actual initialized reachability and the real service cursor. They derive
canonical submission, retained packet identity, and the latest sender counter
internally. The resolve theorem allows a general intervening instruction
list; progress alone must not be described as acceptance if that list contains
expiry instructions. Its whole-service instantiation uses the compiler's
wire/player-only reaction rounds. These block results supply the expiry
protection input; they are not whole-run probability or deviation theorems.

Typed prefix restriction composes via `policyTail_trans` and
`profileTail_trans`. Prefix witnesses at a fixed typed cursor are subsingleton,
so choosing a witness recovered from an operational invariant cannot change
the residual policy. `MessageContinuationStep` uses these composed witnesses
and the full original-graph history scan at each bind, resolve, and sample
successor. These are the transition equations required by the induction,
not a substitute for its service-protection premise.

An arbitrary shorter prefix need not be terminal. Its corresponding statement
uses graph prefixes, not a fabricated terminal outcome.

`MessageApplication.exists_joint_response_mixture_tracePolicies_setup` is the
checked reusable first step. For a fixed finite schedule it predraws focal and
environment responses jointly before sampling the initial execution. It
preserves the complete trace law and all opponent kernels, and requires
neither finite command/view carriers nor a `Fintype` instance.
`exists_joint_response_mixture_runPolicies_setup` gives the actual shared-runner
projection. The mixture ranges over the finite union of reachable information
sites across the entire initial law; it does not select a different policy
after learning the realized secret. Explicit wait fallbacks make the total
response-function law independent of the chosen initial model, including at
unreachable sites. The generic finite-site protocol lemma is separately owned
by `GameTheoryExtensions/Protocol/FiniteSupportPredraw.lean`.

For a fixed response pair, pure extraction replays the environment response and
graph-ineffective public transitions on the native prefix paired with the
current graph prefix. The extracted graph action may inspect only the visible
graph prefix and the focal player's own logical history. Hidden candidate
meanings of other players and recipient-undelivered messages are never graph
policy inputs. Native details may guide deterministic replay of the fixed
response pair, but must not be smuggled into the extracted graph observation.

The crucial two-run obligation concerns the extracted focal action: with the
same predrawn response pair and the same focal graph decision view, that action
must agree across supported executions, including different private initial
samples. Equal focal information does not imply equal full residual outcome
laws when hidden opponent values differ. The outcome-law proof must instead
retain the opponents' respective live kernels in its execution coupling.

The whole finite-mixture law is the proof goal of this edge, not a consequence
already supplied by predrawing. It requires this extraction invariant and
composition of the local probability and service laws with one arbitrary focal
policy; the all-prescribed continuation theorem alone does not supply that
composition.

### Sharp information test

Let an unchanged prescribed player possess correlated private values `x` and
`z`, with its attempted opening of `x` certain to fail. If compilation still
submits raw `x`, a focal opponent can deviate by reading the delivered rejected
packet and using it to predict `z` at a later graph decision. The graph exposes
only failure, so this unilateral native deviation need not have a graph-policy
preimage. Prescribed prechecking removes the leak; opponent projection
additionally handles arbitrary raw packets sent by the focal deviator. A payoff
premise may bound incentives in a later theorem, but it cannot prove this exact
information or outcome-law correspondence.
