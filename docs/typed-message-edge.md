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

## Prescribed policies and observations

`MessagePolicies` implements the policy translation below. `MessagePolicyLaws`
connects the actual command kernels to graph choices and checks uniform failed
disclosure. `MessageServiceLaw` factors a real preparation/submission/inclusion
run through the graph bind kernel. `MessageBindingLaw` and
`MessageResolutionLaw` compose prescribed submission with reserved inclusion
through the actual shared runner. Resolution installs the graph's accepted
result for both logical Booleans, including guard rejection; only successful
publication requires an opening witness. `State.initial_binding` constructs
that witness for every sealed initial field under name uniqueness. Preserving
the association between later graph fields and accepted handles remains part
of the whole-program argument. `MessageVerification` already proves that once
an opening verifies, every supported policy-driven continuation preserves that
exact verifier, even with arbitrary players and environment.

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

Compiler-private memory records the selected bind choice even when it is
failure, and records the logical resolve Boolean. In particular,
`disclose = true` followed by guard rejection is distinguishable from
`disclose = false` at later decisions although both public fields are failure.
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
invocations before submission. The local kernel and submission laws are checked;
the whole-program observation and provenance invariants remain proof work.
`MessagePolicyCommands` proves that every supported compiled command is
addressed to the active phase, never malformed or replayed. Once a submission
is recorded for that phase, the policy waits while it remains active. These
restrictions concern unchanged compiled players; deviations remain unrestricted.
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
It establishes completion, not timely inclusion of prescribed messages;
the honest-law proof must also show that unchanged players' messages succeed
before expiry.

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

## Proposed strategic proof

The operational host, policy compiler, local laws, and service termination are
checked. The shared-prior predrawing theorem is also checked. Supported-pair
coupling, extraction, and the whole deviation law remain proof work.
`Paper.lean` contains a proved completion capstone and three
explicitly admitted capstones for the actual source-to-pending honest law,
deviation-mixture law, and epsilon-Nash correspondence. No supporting library
lemma is admitted.

### Supported pair

For a fixed graph, initial-state law, finite invocation schedule, and adaptive
environment policy, a supported pair consists of a reachable graph
configuration and a native trace prefix such that:

1. the native completed phase count equals the graph prefix length;
2. every completed public native field decodes to the corresponding graph
   field, including failures and chance values;
3. each accepted bind handle has the graph binding meaning represented in the
   graph configuration, privately to its owner;
4. every compiled principal's projected observation and compiler memory equal
   its graph observation and own logical action history; and
5. any prescribed choice already sampled for the current phase is retained
   with its original graph decision view and kernel until that phase completes.

The last item matters because sampling and inclusion are different native
steps. A bind kernel is sampled during private preparation, and a disclosure
kernel during private Boolean recording. The coupling carries that draw
through intervening wire actions; it must not sample again or evaluate the
policy at a later observation. The local bind factorization already exposes
the draw before its continuation. A whole-run proof should retain this branch
evidence directly, rather than reconstructing its probability from the final
store. At checkpoints with no outstanding prescribed draw, the remaining
graph kernel is the one determined by the paired graph decision view.

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

### Completed finite-run deviation theorem

Fix a graph profile, a focal principal, one admissible adaptive environment,
and a bounded finite invocation schedule long enough for guaranteed completion
under the stated service and clock contract. Replace only the focal compiled
policy by an arbitrary native behavioral policy. The target construction is a
finite distribution of pairs

```text
(focal deterministic response, environment deterministic response)
```

and, for every supported response pair, an extracted focal graph policy such
that the coupled native prefix and graph run satisfy the supported-pair
relation pointwise. Binding over the response-pair distribution must give:

* exactly the original deviating native trace law on the native marginal;
* a finite mixture of graph laws with only the focal graph policy replaced;
* unchanged graph kernels for every opponent and for graph chance; and
* equality of the decoded full graph-environment law at the completed boundary.

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

The whole finite-mixture law is the proof goal of this edge, not a consequence
already supplied by predrawing. It still requires the supported-pair induction,
observation projection, chance-kernel step, timely inclusion, and final
decoding proofs.

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
