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
menus retain it. Withholding remains legal and must not be fined.
`RevealServiceRosterMenu` instantiates these retained responses as an existing
finite response menu; its inclusion in the full raw menu is checked. Coverage
of the prescribed policy at every complete-game information site and the
roster audit extension remain separate obligations.

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

`Vegas/Pending/ReactiveOpeningWindow.lean` instantiates the family with an actual
canonical opening and a fully supported policy for silence or any known-envelope
replay. `openingWindowMixture_law` proves its behavioral realization.
`openingWindow_coupling` couples every actual finite roster, including repeated
owners and opponents, across hidden states with the same auxiliary starting
transcript and focal source information. It retains pending-copy multiplicity,
all message/action/emission recall, and the focal player's complete recall. No
sampler-obliviousness assumption is added.

`Vegas/Pending/ReactiveOpeningPosterior.lean` proves the one-phase conditional
claim: `openingOutcome_posterior` starts with an arbitrary correlated law of the
hidden execution and chosen source result. After conditioning on that result,
the actual timing/sampling/replay transcript leaves the hidden-state posterior
unchanged. Thus the source disclosure probability may depend on hidden type.
The proof fixes the auxiliary starting transcript; induction over that
transcript's distribution across multiple phases remains necessary.
`openingWindow_owner_posterior` separately proves that the owner's observations
at an arbitrary roster prefix reveal no additional hidden opponent information
within a coupled initial information fiber, without conditioning on the future
source result.

`Vegas/Pending/ReactiveOpeningSettlement.lean` proves protected final inclusion
for the actual roster followed by its reserved inclusion instruction.
`openingWindow_settlement` settles the unique fresh canonical opening exactly
when a slot was selected. Afterwards every pending, leaked and remembered
network envelope identifier is published, including duplicate replay copies.
`openingWindowMixture_settlement` lifts this to the actual behavioral timing
mixture: its application law is exactly the source opening/withholding mixture,
independently of the conditional opening-time distribution. The
[expiry proof](../../Vegas/Pending/ReactiveOpeningExpiry.lean) turns the
never-opening branch into source failure, and the
[typed source step](../../Vegas/Game/RevealServiceRosterBlock.lean) proves store
and decoded-history agreement. `PublicCheckpoint.reveal_roster` then preserves
the full source/public checkpoint under arbitrary retained policies.
`initialized_roster_prefix_support` propagates it through every actual phase
prefix, including all withholding choices and correlated initial inputs; it
also derives actual uniform-source support. These operational results still
need the multi-phase information and incentive argument.
`openingWindow_inclusion_coupling` also couples the
complete auxiliary transcript through inclusion itself. Successful receipt
equality is derived from acceptance of the canonical opening; withholding
requires no agreement on the undisclosed value.

`Vegas/Game/RevealServiceRosterPolicy.lean` supplies one native policy over all
events and visits. It recovers the source law from the current application
observation and uses the fixed roster's own-response offset.
`rosterPolicy_phase_data` proves that its source law and opening data remain
unchanged along every supported activation-window prefix, including early
openings. `rosterPolicy_window_eq` identifies its actual execution law with
the local timing mixture. Thus the phase family is implemented by one policy;
it is not selected separately for each hidden execution history.

[`roster_owner_fullSupport`](../../Vegas/Game/RevealServiceRosterSupport.lean) proves positivity of
every retained owner response at every actual legal phase prefix, including
early off-path openings, under fully supported source/timing laws.
`roster_window_posterior` identifies the owner's exact recall-conditioned
timing law: condition on unpassed slots before opening, and pin the actual
slot afterwards. Its selected-slot test agrees with the opening recorded in
actual own recall. These statements quantify arbitrary policies generating
the prefix and arbitrary current passive samples.
[`roster_owner_policy_limit`](../../Vegas/Game/RevealServiceRosterLimit.lean) proves the
limit of the single global `rosterPolicy` sequence is exactly the explicit
`rosterLimitPolicy`, at all such owner prefixes. Source disclosure probabilities
may tend to zero or one. This is a policy-limit theorem, not yet a consistent
assessment or an equilibrium theorem for the complete roster service.

`Interaction/ScheduledOpening.lean` proves that a supported first opening pins
the latent slot and makes every subsequent response use the waiting policy.
`openingWindowMixture_after_open` instantiates this with replay/silence.
`Interaction/ScheduledOpeningSupport.lean` proves full support for every lawful
pre-opening replay history. `Interaction/ScheduledOpeningPosterior.lean` computes
the actual recall-conditioned hazard and proves the explicit common policy
limit: wait at earlier visits, use the source mixture at the last, and stop
fresh submissions after every legal opening. The last case includes histories
of limiting probability zero. Evaluating a zero-weight mixture's fallback
directly is not a valid substitute for this checked limit.

The broader-roster SE gate still requires the multi-phase conditional noise
invariant, instantiation of the checked local support and limit facts at every
actual retained-menu information site, one common
consistent limiting assessment, and local sequential incentives.
The one-phase posterior theorem does not prove those remaining obligations.
The proof chain is: define the finite retained menu and prove all-history
coverage; propagate the semantic/public checkpoint and auxiliary noise law;
construct one fully mixed compiled sequence and its source-state posteriors;
transfer the two source continuation values to owner visits and equal values
to replay-only visits; apply the existing one-shot principle and audit extension.

The conditional-on-result argument is specific to revelation. A fresh hidden
commitment does not make its value public at phase end, so distinguishable
submission timing requires a separate source-belief argument. This is a
possible signaling channel, not by itself an equilibrium-preservation
impossibility: independent timing may still support a forward refinement.

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

The [roster service](../../Vegas/Game/RevealServiceRoster.lean) is connected to
the existing scheduler evaluator. Its
[response counts](../../Vegas/Game/RevealServiceRosterCounts.lean) hold for
arbitrary raw policies. The
[initialized prefix theorem](../../Vegas/Game/RevealServiceRosterPrefixSupport.lean)
composes protected inclusion, expiry, public checkpoints and the actual source
decoder through every permitted phase. It retains pending copies and private
observations. The
[local policy limit](../../Vegas/Game/RevealServiceRosterLimit.lean) holds at
all actual retained owner prefixes, including early openings with zero limiting
probability; its policy explicitly stops opening after such a response.

The [decision-support bridge](../../Vegas/Game/RevealServiceRosterDecisionSupport.lean)
connects every legal retained protocol history to those initialized source
prefixes, including histories reached only through trembles. A fixed activation
schedule and own response recall determine decision depth; no scheduler cursor
is added to observations. The
[compiled-prefix law](../../Vegas/Game/RevealServiceRosterPrefixLaw.lean)
holds for every source behavioral profile and timing distribution. The
[complete phase coupling](../../Vegas/Pending/ReactiveOpeningExpiryCoupling.lean)
retains service recall through protected inclusion, ticks and expiry, subject
to equality of the actual public application result.

The remaining implementation gates are to derive the multi-phase conditional
source-belief and local-incentive correspondence, classify fresh departures
under the phase rule, and apply the existing conditional terminal-audit
collection and SE extension. The phase factorization retains an
arbitrary sampler, including in the checked one-phase posterior identity. The
multi-phase SE proof remains open; no extra sampler restriction is currently
assumed or established as necessary.
