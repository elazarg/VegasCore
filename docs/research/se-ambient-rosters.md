# Monitored transmission opportunities between source choices

## Service contract and theorem boundary

The roster service grants one event, visits a fixed finite list of players,
includes the current event's protected packet, and finishes the timeout service.
The list may repeat the owner and other players. Every visit retains the full
bounded raw response menu and passive observation rule. The fixed finite service
calendar is an explicit restriction on scheduling; arbitrary extra visits are
not obtained merely by quantifying over all responses at the declared visits.

The [source-to-roster theorem](../../Vegas/Game/RevealServiceRosterEquilibrium.lean)
preserves every original source SE for reveal-only programs with initially
openable bindings and at least one owner visit per event. The retained strategy
is the fixed playerwise compiler. The
[audited compilation theorem](../../Vegas/Game/RevealServiceRosterCompilation.lean)
then gives a standard SE of the full bounded raw game, with the same joint typed
source outcome and realized settlement-payoff law. Its service assumptions are
the fixed finite roster, protected inclusion, authentic partial terminal audit,
positive conditional record coverage and collectible deposits. It is a forward
existence result for the full raw game; it does not identify all native equilibria
or provide a fixed playerwise off-path raw strategy compiler.

Full-source compilation, including fresh bindings and sampling, remains open.

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
finite response menu. Its inclusion in both the effective and full raw menus,
and coverage of the prescribed policy at every legal history, are checked.
The source-to-roster incentive correspondence is discharged by the local
comparisons and common limit construction below.

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

The extra deferral choices and private recall use one common consistency
construction. Its checked limit waits until the final owner visit on path and
stops fresh submissions after an earlier opening at an off-path visit. The local
continuation comparison proves sequential rationality of this same fixed limit.

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

The multi-phase conditional noise invariant, actual-history support, and common
consistent limiting assessment are checked below. The broader-roster SE gate
still requires local sequential incentives.
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
The retained menu admits every known replay, including pending envelopes, so
every extra effective response is a fresh submission. Attribution for that
first-departure comparison can use its author without identifying rebroadcasters.
Accountability after arbitrary earlier misconduct is a stronger requirement:
charging a rebroadcaster requires separately authenticated transmission evidence.

The [roster checker](../../Vegas/Game/RevealServiceRosterTraffic.lean) compares a
fresh envelope's serial with the number of its author's entries in the prior
ledger. `roster_fresh_iff_serial` proves that this public test is exactly the
owner's private stopping test at every legal retained activation. A second
fresh opening has an incorrect serial; replaying the first preserves its
identifier. Thus one authentic sampled record can witness the departure;
the auditor need not observe two transmissions together or infer anything from
missing records. The proof uses the actual allocator and protected inclusion,
not a uniqueness assumption imposed on raw player responses.

The [departure theorem](../../Vegas/Game/RevealServiceRosterDeparture.lean)
classifies every extra effective response at every retained history. The
[conformance theorem](../../Vegas/Game/RevealServiceRosterTrafficSound.lean)
proves every retained history passes, including foreign rebroadcasts of pending
openings. These are first-departure and retained-history guarantees, not a claim
of nonframing after arbitrary prior misconduct. Deployment still needs authentic
phase and prior-ledger evidence and a positive conditional collection rate.

[`roster_audited_sequential_equilibrium`](../../Vegas/Game/RevealServiceRosterAudit.lean)
composes these operational facts with the generic audit extension. A fixed
deposit for each player is its full finite continuation-payoff range divided by
a positive lower bound on conditional detection probability. The theorem
quantifies every retained SE, so the checker and deposit do not select an
equilibrium. It restores every bounded raw response and preserves the joint
readout and realized randomized settlement law. The terminal audit is an
explicit service assumption, with no strategic watcher activation. It may
return only a partial authentic sample; its coverage bound must hold for a
forbidden record whenever that record is present.

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

The [finite roster compiler](../../Vegas/Game/RevealServiceRosterMixing.lean)
has proved admissibility at every retained history. Fully mixed source choices
and strictly positive timing give exactly the retained response support, even
after an earlier opening. The
[common convergence theorem](../../Vegas/Game/RevealServiceRosterConvergence.lean)
uses one source sequence and one timing sequence for every native information
site. Its limit is the explicit policy that waits until the final owner visit
and stops after any earlier opening. It does not use a zero-probability
fallback of the timing mixture as the limiting continuation.

The [initialized traffic factorization](../../Vegas/Game/RevealServiceRosterPrefixNoise.lean)
now covers every completed source prefix. Conditional on a player's source
observation, the full accumulated message transcript and that player's native
recall carry no additional information about the hidden source state. The
proof derives initialization from the empty network and iterates the actual
grant, response, inclusion, tick and expiry instructions. It permits arbitrary
correlated initial states, source profiles, timing distributions and passive
sampling rules.

The [native Bayes theorem](../../Vegas/Game/RevealServiceRosterBayes.lean)
identifies the actual finite game's owner belief with the original source
posterior at every legal owner history. It conditions on full native recall and
the current passive sample, including histories following an early own opening.
The [common consistency construction](../../Vegas/Game/RevealServiceRosterConsistency.lean)
uses one subsequence for all native sites and preserves those belief marginals
at the fixed limiting policy. No player observes a new scheduler cursor.

The [phase continuation law](../../Vegas/Game/RevealServiceRosterPhase.lean)
connects an intermediate window to the original source step and the entire
remaining source program, with the actual guarded terminal readout. Its finite
coupling keeps the native final ledger, receipts and serials, so the existing
public checkpoint applies at the next phase. The
[local evaluation bridge](../../Vegas/Game/RevealServiceRosterLocalEvaluation.lean)
identifies one finite-menu response alternative followed by the physical global
policy, at every legal history and at the standard assessment horizon.

The [initialized finite-profile law](../../Vegas/Game/RevealServiceRosterInitialized.lean)
preserves the original source profile's complete typed outcome distribution at
the actual finite assessment horizon. The
[owner history values](../../Vegas/Game/RevealServiceRosterOwnerHistoryValue.lean)
identify every local response's continuation value at every legal owner history.
The [harmless comparison](../../Vegas/Game/RevealServiceRosterHarmlessComparison.lean)
proves equality of the complete alternative and prescribed outcome laws when
the player is a nonowner or has already opened. It permits arbitrary native
beliefs because its proof holds separately at every compatible hidden history.

The [common timing construction](../../Vegas/Game/RevealServiceRosterTiming.lean)
requires each event owner to appear at least once in its finite roster. A
positive uniform component provides every opening time; its vanishing weight
bounds the earlier timing mass at every site. The
[source payoff range](../../Vegas/Game/RevealSourcePayoffBounds.lean) bounds the
two source continuation values uniformly over legal histories and assessments.
It imposes no global boundedness assumption on the source state carrier or
utility outside reachable source histories.

The strategic proof combines these laws with the owner posteriors and
the local incentive bounds at every native information site. Along the perturbation
sequence, conditioning on no earlier opening generally changes the eventual
disclosure probability. Exact equality with the original source action law at
every approximant is therefore not a valid premise. The checked
[local comparison theorem](../../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean)
allows a uniform incentive error tending to zero, retaining one common sequence.
`FinDist.deferredRemaining_error` bounds the conditional probability change by
the timing mass already passed, uniformly even when the source probability tends
to one. The [owner incentive comparison](../../Vegas/Game/RevealServiceRosterOwnerIncentives.lean)
bounds each local native gain by one actual original-source deviation's gain,
plus this vanishing error. The finite source payoff range bounds the error
uniformly over all sites and all local alternatives. One common consistent
assessment limit supplies SE of the fixed compiled profile. Nonowners may learn
the impending publication early; the harmless comparison justifies their local
alternatives directly.

Full-source SE compilation remains open. It additionally needs the evolving
binding/guard checkpoint and stopped native continuation comparison described
in [se-hidden-binding.md](se-hidden-binding.md).
No extra sampler restriction is currently assumed or established as necessary.
