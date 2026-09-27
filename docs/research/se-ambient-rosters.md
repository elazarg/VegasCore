# Monitored transmission opportunities between source choices

## Current boundary

`RevealService.block` currently grants one event, activates its owner once,
includes the latest matching packet, activates the watcher, and finishes the
timeout service. Arbitrary raw responses at those activations do not include
arbitrary additional activations. The generic reactive runtime already permits
the latter; this is a service-calendar restriction, not an impossibility result.

## Smallest useful enlargement

Parameterize each event's block by a finite list of additional player visits.
Use the existing `.player`, `.includeLatest`, `.wire`, tick and expiry
instructions. No new interpreter, source operation, or private scratch state is
needed. All actual visits retain the full bounded raw response menu and the
existing passive observation rule.

The simplest first adapter has one current-owner visit and arbitrarily many
visits by other players before and after it. This would already permit Alice to
broadcast before Bob's source choice. It is an intermediate theorem scope:
allowing repeated current-owner visits requires the additional refinement below.
It must not be presented as covering every bounded interaction calendar.

The retained menu at an off-turn visit contains silence and already-published
replays. At the owner's visit it also contains the canonical opening. A terminal
audit deters fresh traffic outside that menu; it does not remove that traffic
from the full target. Withholding remains legal and must not be fined.

## Repeated current-owner visits

A phase rule should permit a matching canonical opening while its event is
granted and ready, regardless of which owner visit emits it. Rejecting an early
owner opening solely because it missed a designated microstep would require
additional authenticated scheduling evidence and would enforce an incidental
compiler schedule.

One credible interpretation allows the owner to defer through several visits;
the first accepted canonical opening fixes the source revelation choice, and
expiry fixes withholding if none was included. Reserved inclusion after each
visit removes competing canonical packets. All other retained visits carry only
already-public traffic. This is a proposed source-to-native sequential refinement,
not a checked SE theorem: the extra deferral choices and private recall must be
handled in the common consistency construction. Existing one-owner prefix laws
do not establish that refinement automatically.

## What is now proved about public replays

`Interaction.ReactiveApplication.runRounds_published` applies to the actual
round evaluator, arbitrary finite activation/wait windows, adaptive schedulers,
and every passive sampling rule. If all pending identifiers are already
published, and every supported response is silence or replay of a published
identifier, then application state, receipts, and every current player view
remain unchanged, and all pending identifiers remain published.

`runRounds_published_application` gives the exact resulting configuration law.
`EventGraphRuntime.reactiveLatest_replay_published` separately proves that such a
replay cannot change reserved current-event inclusion, even when another player
authored the envelope.

These results do **not** erase own action recall, pending copies, network input
history, audit records, or scheduler recall. Arbitrary schedulers can react to
those records. If unpublished packets coexist, an arbitrary sampling rule can
also react to the changed pending list; the clean-checkpoint premise matters.

## Audit evidence and attribution

`TrafficRecord` contains the public application observation, ledger and
network input. The application observation carries the grant and public event
progress, but no global step index. Equal application views
can recur. A checker using only those records cannot distinguish two owner
visits in the same unchanged phase; the phase rule above does not need to.

Admitting a replay because it was already published needs evidence of publication
**before that transmission**. Terminal ledger membership is insufficient: fresh
misconduct can be included later. The record therefore retains the preceding
ledger, authenticated along with its phase. Partial observations must
not turn missing records into a proof of absence.

The envelope authenticates its original author, not a subsequent broadcaster.
At a retained clean checkpoint, every known envelope is already published, so
every extra effective response is a fresh submission. Attribution for that
first-departure comparison can use its author without identifying rebroadcasters.
Accountability after arbitrary earlier misconduct is a stronger requirement:
charging a rebroadcaster requires separately authenticated transmission evidence.

The immediate implementation gate is therefore: insert finite ambient windows;
prove the clean-prefix and source-information correspondence using the checked
window lemma; classify every fresh extra response against a semantic phase rule;
then apply the existing conditional terminal-audit collection and SE extension.
Repeated-owner deferral and adaptive service timing remain explicit proof gates,
not established obstructions or silently excluded target actions.
