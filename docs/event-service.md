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
Full honest protection additionally requires proving that the compiled policy
uses its reserved invocations to remember, prepare, and submit the correct
event action. That policy theorem and the whole-run honest/deviation laws are
separate from termination. No such strategic law is a field of the service
configuration.

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
candidate backing each successful binding. Initialization and preservation by
private commands and completions that cannot introduce a binding success are
checked. Its preservation through successful binding acceptance and all
native transitions still needs to be established.

The compiler's public-barrier dependencies address early visibility of an
honest opening. `BarrierOrdered.ready_public_unique` proves that a ready
public event is the only ready event in that cut. While its opening awaits
inclusion, no different event can complete. Once it completes, its successful
value is graph-public. This fact covers both publications and chance nodes;
it is a consequence of the dependency discipline, not a restriction on what
packets an adversary may send.

## Remaining strategic edge

The whole-run proof must establish binding provenance and the block entry
conditions throughout execution, effective reserved inclusion, and deadline
protection, then compare actual outcome laws and unilateral deviations with
the graph game.

A candidate honest-law coupling advances a proof-only ideal configuration
when an honest owner first samples its event action. Native preparation,
submission, and inclusion subsequently implement that already selected action.
The coupling must relate outstanding remembered actions to the difference
between the ideal and native cuts. Public-barrier ordering permits outstanding
independent hidden bindings, while a ready public event excludes another
ready decision. Normalized observations must agree at each fresh policy draw,
and service protection must ensure the native state eventually catches up.
The pointwise `canonicalContinuation_step` law can then handle each ready
ideal step without factoring the wire process through a public scheduler.
This is a proof plan, not an established coupling or a new runtime model.

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
