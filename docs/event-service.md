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

## Remaining strategic edge

The graph-to-message proof must construct the prescribed native policies,
prove their sample-once and prevalidation behavior, and compare their actual
outcome laws and unilateral deviations with the graph game. It must account
for the public pool and this service's richer observation history; it cannot
assume that the wire environment is already an ideal-graph scheduler.
