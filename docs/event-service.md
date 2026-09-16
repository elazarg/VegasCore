# Public event service

`Vegas.Pending.EventService` supplies a bounded environment for the
event-addressed message application. It composes the shared message-policy
transitions; player histories, message pools, receipts, and native chance stay
in the execution. It does not change the source language or graph readiness.

## One epoch

At the start of an epoch, an environment policy samples a permutation of all
graph event IDs from its current public observation and command history. The
observation includes the entire pending pool. The policy cannot inspect hidden
commitment meanings. For each event in that permutation, the service:

1. Publishes a grant identifying the event.
2. If the event has an owner, offers three owner invocations, then the configured
   wire slots and player reactions, then one reserved inclusion opportunity.
3. Executes a sample command for that event. This invokes the retained chance
   kernel only if the event is a ready sample; otherwise it has no effect.

After the complete sweep, the service advances the block clock once and checks
expiry at every event. Expiry checks do not themselves advance time.

A grant is a public service announcement, not an authorization check on
packets. Arbitrary players can submit, replay, and prepare competing candidates
at their invocations. The wire policy can deliver or include any pending
packet at its slots, including a packet for an event other than the grant. It
cannot insert extra clock advances or sample triggers.

The reserved selector uses only the authenticated sender and public event
address. It selects the latest matching pending packet; a later unrelated
packet cannot consume the reservation. It does not inspect candidate meanings
or search for a semantically successful opening. Invalid focal submissions
can be rejected and eventually resolve through timeout.

The reserved permutation is fixed within an epoch and can be chosen afresh
adaptively between epochs. Wire delivery and inclusion remain adaptive within
the epoch. This is a particular concrete service discipline, not every fair
asynchronous scheduler.

## Completion argument

Let `n` be the event count and `D` the maximum event deadline. The driver runs
`n * (D + 1)` epochs. Completion is independent of the player policies:

- Native transitions only extend the completed dependency cut.
- A ready event stays ready until it completes. A ready strategic event keeps
  its activation timestamp; unrelated traffic cannot restart its timeout.
- A ready sample completes at its next sample opportunity.
- A ready strategic event completes no later than the expiry check after a
  full deadline window, even if every owner invocation withholds or sends
  invalid traffic.
- A nonterminal finite acyclic graph always has a ready event. Each full
  deadline window therefore increases the completed-event count, unless the
  graph is already terminal. At most `n` windows suffice.

`EventGraphRuntime.runService_terminal` checks this argument for every
supported execution from an invariant state. `servicedEventGame_complete`
specializes it to the actual game with private initial inputs sampled inside
play; `servicedEventGame_outcome_total` gives total typed outcome readout.
`Paper.event_pending_completion` directly delegates to that result.

The bound is deliberately uniform, not a claim of optimal latency. Completion
alone does not prove preservation of honest outcomes: an environment can
terminate a game incorrectly by expiring compliant actions too early.

## Deadline-relative protection

The configuration `ServiceFeasible` requires each relative deadline to be at
least two block-clock ticks. This leaves a full service epoch for an event
that becomes ready after its position in the preceding sweep.

For example, visit `b` before `a`, where completing `a` enables `b`. If `a`
completes at clock `c`, then `b` activates at `c`. A deadline of one would make
`b` expire at the immediately following clock tick despite never receiving a
ready owner opportunity. With a deadline of two, `b` is still timely at clock
`c + 1`, when the next epoch visits every event before advancing time again.
Repeating a fixed number of same-clock sweeps does not remove this issue: an
adversary can wait until the final sweep to enable a dependent event.

`withinDeadline_of_age_le_one` checks the arithmetic part of this argument.
The honest service proof combines it with the compiled policy's proved use of
the reserved invocations to remember, prepare, and submit the correct event
action. This protection argument is separate from arbitrary-player termination.
No outcome or strategic law is a field of the service configuration.

## Prescribed policies and local refinement

The prescribed policy uses a public grant only when that event is ready and
owned by the player. Readiness is computed from public completion identities.
The three uninterrupted owner opportunities have a fixed shape:

1. Sample the normalized graph policy and privately remember its action.
2. Privately prepare the opening material, or repeat the remembered action
   when no material is needed.
3. Submit the event-addressed packet.

A binding uses the same opaque handle and submission time for success and
failure. Its handle is derived from its owner and event identity, independently
of the selected value. A resolution sends an opening only when owner-local
prevalidation succeeds. A withheld or rejected disclosure sends the same
withholding packet. The private remembered action retains the distinction
between choosing `false` and choosing `true` whose guard rejects the opening.
Policies outside this prescribed image remain unrestricted.

`runServicePlan_compiled_bind_block` proves an exact distribution law for the
three actual owner invocations: one normalized graph-policy draw followed by
its private preparation and submission. The empty cache, unused staging
history, grant, and readiness premises are explicit. This is a local block law;
it does not assume that arbitrary service prefixes satisfy these premises.
`runServicePlan_compiled_resolve_block` gives the corresponding law for
resolution events, including a true disclosure rejected by its guards.

`runServicePlan_compiled_bind_includeLatest` additionally includes the actual
reserved message inclusion. Under fresh candidate and sender-serial entry
conditions, its configuration law is exactly the normalized graph-policy
kernel followed by the graph step. The proof uses the real message pool,
authenticated event-addressed selection, packet handler, and acceptance receipt.
It covers both successful bindings and failed bindings. Intervening wire and
reaction instructions are covered by the honest block laws below.
`runServicePlan_compiled_resolve_includeLatest` proves the matching resolution
law under typed accepted-handle provenance and a fresh sender serial.

Private preparation and remembering preserve the full environment observation
and every other player's native observation. The binding block's joint
history-and-observation laws for the environment and other players are point
masses at the same fixed opaque submission, independently of the selected
value or failure. These are local hiding laws, not a whole-execution
noninterference theorem.

`handle_commitment_eq`, `handle_opening_eq`, and `handle_withhold_eq` relate
accepted packets to the graph's actual binding and resolution kernels. These
are local laws with explicit readiness, deadline, and provenance premises;
they do not assume a whole-run correspondence.

`handle_resolutionSubmission_eq` connects the packet computed from the owner's
actual native observation to that resolution kernel. Its binding-provenance
premise supplies the accepted handle and matching immutable candidate for a
successful opening. False disclosure and rejected true disclosure both execute
correctly through withholding, retaining their distinct private actions.

`State.BindingInvariant` records typed, distinct accepted handles and the
candidate backing each successful binding. Every native transition preserves
it, including competing commitments, rejected or withheld disclosures, chance,
and expiry. `runServicePlan_bindingInvariant` lifts preservation through service
prefixes, and `servicedEventGame_bindingInvariant` proves it for every supported
complete execution, under arbitrary player, wire, and ordering policies. This
provenance theorem needs no deadline-feasibility premise.

The compiler's public-barrier dependencies address early visibility of an
honest opening. `BarrierOrdered.ready_public_unique` proves that a ready
public event is the only ready event in that cut. While its opening awaits
inclusion, no different event can complete. Once it completes, its successful
value is graph-public. This fact covers both publications and chance nodes;
it is a consequence of the dependency discipline, not a restriction on what
packets an adversary may send.

## Honest outcome law

`servicedEventGame_honest_store_law` proves exact equality of terminal typed-store
laws for every `BarrierOrdered` graph, every behavioral profile, and every
private input distribution. The order and wire policies remain arbitrary within
the concrete service. The additional deadline condition is `ServiceFeasible`:
each relative deadline is at least two ticks. Source compilation supplies the
graph certificate, so `eventPendingGame_honest_law` gives the full-source result
without imposing a source-language fragment.

The proof carries `HonestBoundary` between event blocks. Its pending pool is
empty; every unfinished event has an empty cache, no previous staging or
submission, no accepted output, and a fresh unused canonical handle. Completed
events retain their actual histories and cached actions.

For a ready binding or resolution, the three owner invocations draw, stage, and
submit the prescribed action. During the reaction slots all prescribed players
wait. The wire can still deliver or include the packet, and these actions retain
their histories and receipts. The singleton-packet invariant shows that either
the packet is still pending or it has already been accepted exactly once.
Reserved inclusion flushes the former case and leaves the latter unchanged.
Both cases implement the graph kernel and restore the boundary. A ready sample
executes its original chance kernel; an unavailable event block stutters.

`ready_event_block` packages these configuration and boundary laws. At a clean
boundary, `State.continuationLaw` equals the graph's canonical continuation:
remembered actions at completed events cannot affect future execution.
The graph's barrier-order commutation theorem shows that any ready event kernel
preserves this distribution-valued potential. `runEventSweep` composes the
actual block laws, including the adaptively chosen event order.

At epoch entry, each live activation is at most one tick old. Every event
already ready then completes during the sweep. Any activation left unfinished
was created during that sweep, so after the tick it is only one tick old.
Deadlines of at least two ticks make the expiry sweep inert. This establishes
both deadline protection and the next epoch's age invariant.

`serviceEpoch_honest` and `runService_honest` conserve the continuation law through
the concrete service. At its proved completion horizon, the continuation is a
point mass at the terminal semantic state. Projecting to the store yields the
graph-to-native law; composing with the source-to-graph theorem gives
`Paper.source_event_pending_honest_law`. Equality concerns semantic outcomes,
not chronological traces.

## Remaining arbitrary-deviation edge

An arbitrary deviator can leave pending packets and staged candidates behind;
the honest-boundary invariant is therefore not a unilateral-deviation theorem.
The native binding-provenance and completion results already hold under arbitrary
policies. What remains is the setup-wide deviation law against unchanged
opponents, followed by the Nash transfer.

The richer wire process cannot simply be treated as an ideal public graph
scheduler. A deviator may publish its own private information in arbitrary
packets, and wire decisions can depend on those packets. Consequently, the
effective scheduling law need not factor through the graph's public
observation. A unilateral extraction must account jointly for the deviator,
the wire process, and the service ordering. The information argument must
show that extra observations reveal no unavailable opponent information at
a focal decision; it need not prevent the focal player from signaling its
own information. Local handler refinement and completion alone do not supply
this argument.
