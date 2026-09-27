# Monitored transmission opportunities between source choices

## Current boundary

`RevealService.block` currently grants one event, activates its owner once,
includes the latest matching packet, activates the watcher, and finishes the
timeout service. Arbitrary raw responses at those activations do not include
arbitrary additional activations. The generic reactive runtime already permits
the latter; this is a service-calendar restriction, not an impossibility result.

## Bounded phase design

Parameterize each event's block by a finite list of additional player visits.
Use the existing `.player`, `.includeLatest`, `.wire`, tick and expiry
instructions. No new interpreter, source operation, or private scratch state is
needed. All actual visits retain the full bounded raw response menu and the
existing passive observation rule.

The intended phase has a fixed finite roster, containing at least one visit by
the current owner and possibly repeated visits by every player. It ends with
protected current-event inclusion and deadline settlement. There may be foreign
observations between submission and inclusion; adding an inclusion after every
owner visit would impose a different, stronger service contract.

The retained responses are silence, replay of already-published envelopes, and
replay of the phase's canonical opening once possessed, even before it is
published. The owner may submit at most one fresh canonical opening envelope at
any of its visits. A terminal audit deters other fresh traffic; full raw target
menus retain it. Withholding remains legal and must not be fined. These are
proposed conformance rules, not yet an instantiated roster menu theorem.

## Repeated current-owner visits

A phase rule should permit a matching canonical opening while its event is
granted and ready, regardless of which owner visit emits it. Rejecting an early
owner opening solely because it missed a designated microstep would require
additional authenticated scheduling evidence and would enforce an incidental
compiler schedule.

Before the first submission, both source outcomes remain available. After it,
protected final inclusion must guarantee revelation despite later silence and
exact-envelope replays. Expiry implements withholding when there was no opening.
One fresh submission has one identifier; including it publishes that identifier
for every remaining replay copy. A second fresh envelope has a different
identifier and is an attributable multiplicity departure. A rebroadcaster need
not be attributed or punished merely for retransmitting the original envelope.

This is a proposed source-to-native sequential refinement. The extra deferral
choices and private recall require one common consistency construction;
the checked single-owner calendar theorem does not establish that refinement.

## Checked phase distribution and deferred-choice algebra

`GameTheoryExtensions/Math/Probability/DeferredChoice.lean` constructs behavioral
opening hazards from a source probability `q` and a conditional timing law `t`.
It proves exact first-opening mass `q * t(slot)`, exact withholding mass `1-q`,
and corresponding binary-outcome payoff equality. Fully supported timing and
`0<q<1` make opening and waiting positive at every opportunity. Concentrating
timing on the final owner opportunity gives zero earlier opening hazards and
the source probability at the final one, including when that probability tends
to one.

`Vegas/Pending/ReactivePolicyMixture.lean` connects a scheduled response family
to the actual existing `runInteractionPlan`: one behavioral policy has exactly
the complete execution law of first choosing an opening slot, or never opening,
and running that component policy. This holds for arbitrary finite plans,
intervening player responses, network policies and passive observation rules.
`Interaction/ReactivePolicyMixture.lean` proves that a latent choice unused
before a phase retains its intended prior at that phase, with actual earlier
own recall. The latent mixture is a proof device realized as a behavioral
policy; it adds no player scratch-memory state, action or computation cost.

These results do not yet establish SE for the broader roster. The scheduled
family must implement the stated canonical opening/replay rules, preserve every
source outcome through the service, and be fully mixed over that retained menu.
At the next meaningful source decision, the joint timing/sampling/replay
transcript must preserve the source posterior throughout the common perturbation
sequence. Unconditional execution-law equality alone does not prove this.

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

`Interaction/DeferredObservation.lean` handles two parts of a delayed-inclusion
phase: an owner's activation adds no passive information when every foreign
pending envelope is already known or published; and including the selected
identifier makes remaining copies of that envelope published. Other players
can still read the owner's unpublished envelope. This does not assert identical
sampler laws for pools with different replay multiplicities.

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

The implementation gates are: instantiate the deferred policy in the actual
retained phase; prove protected final inclusion and the next clean checkpoint;
derive the conditional source-belief and local-incentive correspondence; classify
fresh departures under the phase rule; then apply the existing conditional
terminal-audit collection and SE extension. The phase factorization retains an
arbitrary sampler. Whether a further sampler restriction is needed for the
conditional SE argument remains open; no such restriction is assumed by the
checked phase-law theorem.
