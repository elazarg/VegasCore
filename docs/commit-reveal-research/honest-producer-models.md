# Two simple honest-producer candidates

This is a mathematical research note by Codex. These are candidate finite
ledger interfaces, not adopted runtime assumptions or new checked theorems.
Compiler parameters and collateral are chosen from public service properties
before selecting the producer configuration or the source equilibrium.
The purpose is to identify what honest production actually buys: inclusion,
information delivery, and finality are separate properties.

The relevant source distinction is also separate. The checked settle-late
comparison requires a protected opening and forbids withholding there.
A source language with lawful refusal has another action and potentially
another payoff and observation. Its refusal cannot be identified with a lost
late transaction without a correspondence proof.

## What is assumed about producers

In both candidates, production times and transaction selection are exogenous
rules fixed before play. Producers have no utility depending on a game
player's win, no side agreement with a player, and no access to private game
state except through delivered messages. Model two additionally interprets
its selection rule as maximizing declared fee revenue. This is stronger than
merely excluding collusion, but much simpler than modeling strategic miners.

These candidates are abstractions, not descriptions of Ethereum. Ethereum's
documentation distinguishes broadcasting a pending transaction, a producer
selecting it, and later finalization; it also specifies bounded block gas and
notes that slots can be empty. Those facts motivate separating the three
events rather than assuming an unconditional block or finality deadline.
[Transaction lifecycle](https://ethereum.org/developers/docs/transactions/),
[block production and capacity](https://ethereum.org/developers/docs/blocks/).
Its fee documentation describes priority fees as incentives for inclusion,
not guaranteed inclusion, and producer revenue can also involve MEV.
Consequently maximum declared fees is an explicit simplification here.
[Fees](https://ethereum.org/developers/docs/gas/),
[MEV](https://ethereum.org/developers/docs/mev/).

Both models broadcast plaintext. Each relevant observer eventually receives
every broadcast packet, including packets excluded from a block or rejected
by the application. No model assumes that pending contents remain invisible.
Different recipients can receive the same broadcast at different times.

## Candidate one: enough capacity and bounded delivery

Public constants are a transaction delivery bound Delta, a maximum gap B
between block-selection times, and an additional finality bound F. A valid
call broadcast at time t reaches every subsequent block's producer by
t+Delta. It reaches every relevant game observer by t+Delta as well.
Recipients retain its contents permanently. A producer includes every
eligible call it has received. Every block's eligible workload fits its
capacity, including all deviations permitted by this candidate's finite
action interface. This last condition needs an actual traffic bound or
reservation; it is not implied by work-conserving selection alone.

An included block becomes irrevocable and available to the relevant players
within F additional time. Eligibility includes ordinary validity and the
application's deadline. Calls whose applications have expired may be
ineligible, but their broadcast contents still reach observers.

There are no strategic bids, replacement transactions, nonce dependencies,
additional transmission channels or outcome-dependent ordering rules in this
candidate. Fixed fees must be included in both source and target utilities,
or compared separately as costs. They are not presumed to disappear.

### Paper lemma: the inclusion bound

A call valid throughout the required interval, broadcast at t with an
application deadline strictly later than t+Delta+B, is included by
t+Delta+B and finalized by t+Delta+B+F.

**Proof.** It is available to producers at t+Delta. By the public block-gap
bound there is a selection opportunity no later than t+Delta+B. The call
remains eligible there and sufficient capacity forces its inclusion.
The finality bound gives the second conclusion. A boundary convention for
simultaneous arrival and selection can instead use a strict inequality or
an arbitrarily small guard interval. Nothing here proves either bound for
an unrestricted consensus protocol.

The conclusion is a service bound, not an SE theorem. Owners must still get
an opportunity to submit, and inclusion order must respect the application's
causal and informational dependencies.

### Paper lemma: a decision with enough observation slack sees all packets

Suppose every allowed broadcast relevant to a receiver's irreversible
decision occurs no later than T_emit. If its decision is at T_answer with
T_answer >= T_emit+Delta, its information contains every such packet's
contents, regardless of inclusion, rejection or expiry.

**Proof.** Apply the delivery bound to each packet separately. Retention
ensures that an earlier received packet remains known at the decision.
There are finitely many permitted broadcasts, so the statement holds
simultaneously for all of them.

This is a physical timing condition. T_emit is the last permitted physical
transmission time, not the last source event index. A source horizon alone
does not imply this slack. A transmission made outside the candidate's
interface is not covered merely because it carries the same value.

Under this condition the partial-observation premise of the checked
settle-late result is absent: its final observation parameter cannot remain
strictly below one for the admitted packets. This rules out that particular
proof mechanism, not all timing-based SE obstructions.

For a single fixed-value disclosure phase with no intermediate receiver
choices, no extra messages and at most one emission, the existing
[fully public phase paper theorem](../full-public-disclosure-phase-preservation.md)
then supplies an exact outcome positive under its remaining payoff and
prior hypotheses. That theorem permits lawful withholding with its specified
forfeit, and finite value-dependent inclusion rates. It does not cover a
general commit-reveal sequence merely because this delivery lemma holds.

If transmissions have a public, deterministic arrival schedule and block
selection times are public, sufficient capacity also makes each transmission
either surely timely or surely late. The uncertainty in the settle-late
inclusion lottery is then absent. A weaker upper delivery bound does not
have that consequence: an arrival near a selection cutoff can still be
uncertain within its allowed interval.

### What this candidate does not guarantee

Work-conserving service with arbitrary load need not provide sufficient
capacity. All-calls inclusion does not stop a player sending an opening
before a source-authorized disclosure time, and plaintext can be informative
before its application call becomes eligible. Event dependencies alone
therefore do not establish source-information fidelity. Extra bids, raw
messages, traffic-dependent ordering and retained hidden state require their
own analysis. Waiting and finality costs can also change incentives.

The strong bounds are plausible interface goals for a reserved-capacity
service during an expressly stated availability period. They are not a
claim that a public L1 offers them unconditionally.

## Candidate two: one opening slot and maximum fee revenue

The public production calendar has blocks at times 1, 6 and 11. A protected
opening broadcast at time 0 is available for block 1. Two optional late
opportunities are at times 3 and 5. Their application deadline permits
block 6, but not block 11. Thus both late calls compete for the same last
block. There is one unit of capacity in that block; all eligible calls
occupy one unit.

The protected block has no competing traffic. At time 5.5, independently of
all game types, choices and prior observations, a background call arrives
with probability epsilon, where 0<epsilon<1. It offers fee h>f>0. Otherwise
no background call arrives. Each opening offers the fixed fee f. A producer
always includes the eligible call with greatest fee, choosing uniformly
among equal-fee openings. It never receives a side payment or uses a game
payoff when making this choice. When the pool is empty it produces an empty
block. Finality at these block times is an idealized assumption of this
candidate, not a consequence of maximizing fees.

All opening broadcasts reach the producer before the applicable selection
time. The generic call identifiers in this candidate are independently
eligible identifiers. An Ethereum account's sequential nonce rules do not
automatically implement this retry menu; that is one missing adaptation.

### Paper lemma: honest fee selection supplies no uniform late-failure floor

For a sole late opening,

\[
q=1-\epsilon.
\]

For two late openings, each is included with probability q/2 and neither is
included with probability 1-q. Protected inclusion is certain.

**Proof.** Background traffic wins whenever present. In its absence a sole
opening wins, or the uniform tie rule chooses one of the two openings.
The protected block has no competitor.

All producers obey the same rule for every epsilon. As epsilon decreases to
zero, late inclusion approaches certainty without collusion, strategic
censorship, payload-dependent selection or a higher application fee. Hence
honesty and this selection rule alone imply no public delta>0 satisfying
q<=1-delta for the whole class. A public lower bound on epsilon would be an
additional load assumption. A theorem using it must choose collateral from
that bound before selecting epsilon.

Allowing fee upgrades makes the limitation more direct. An application bid
above h wins whenever eligible, so its timely success probability is one.
Whether that upgrade is profitable depends on its actual fee cost. The
point is that a failure-floor assumption must cover all permitted bids; it
cannot be inferred from the reliability of the prescribed fee f.

A fixed bid is a restriction of this comparison interface, not a consequence
of fee auditability. An auditable public bidding rule need not fix the actual
paid fee, but must account for permitted fee signals, priority effects, costs
and collectible departures. [Fee policies and the conditional enforcement
bound](fee-policy.md) study that separate interface. Adding fee actions does
not automatically extend the SE negative below.

### Bounded public propagation still allows unequal observation

To specify the contents available before settlement, suppose a receiver has
an intermediate observation at time 4 and its irreversible reply at time 7.
Each ordinary opening broadcast has an independent receiver delivery delay

| Delay | Probability |
| --- | --- |
| 1 | lambda |
| 4 | (1-lambda) lambda |
| 6 | (1-lambda)^2 |

where 0<lambda<1. These delays are independent of background traffic and
the producer's tie-breaking. The recipient permanently retains received contents.
All deliveries are public and occur within six time units. The producer's
faster delivery path does not imply a secret transaction: every other
recipient still receives the same plaintext by the stated bound. An included
block has a faster public propagation path and reaches the receiver before
time 7, exposing whichever opening it contains.

The first late opening is seen at time 4 with probability lambda. If it was
not yet received then, it arrives by time 7 with conditional probability
lambda. The second late opening arrives by time 7 with probability lambda.
Consequently the unconditional ordinary-delivery probabilities at the reply
are

\[
s_1=1-(1-\lambda)^2> s_2=\lambda.
\]

This is an explicit bounded-delay realization of the comparison's opening
observation probabilities. An excluded first opening arrives by time 9 at
the latest; an excluded second opening arrives by time 11 at the latest.
Failure to know one at the time-7 decision is temporary delivery latency,
not permanent invisibility. There is no block between the late sending
opportunities, so the sender learns no admission result before choosing
whether to retry. Background load is drawn only after its final choice.

For exact comparison observations, the player interface reports delivered
contents at its two decision activations, with the sender identifiers and
included-call metadata of that comparison. Extra arrival timestamps,
continuous monitoring, alternate relays or observations of producer pools
are additional information. A native embedding must analyze them rather
than silently erase them. The physical delivery construction alone is not
such an embedding.

### Paper negative for an explicitly restricted audited interface

One can complete this candidate to a finite comparison game using exactly
the sender menus, receiver menus, observations and base payoffs in
[the settle-late comparison](quantifier-orders.md#the-finite-game-behind-the-checked-negative).
Raw signed bit signals and the receiver's intermediate notification use an
explicit fast auxiliary message channel and do not consume the opening
slot. They are reported at the corresponding scheduled observations.
The receiver's notification has its fixed comparison cost. There are no
other transmission, bidding or observation actions in this restricted game.

For clarity, its source gives the sender a bit with probability 9/20 of
being one and an independent uniform label A, B or C. The required opening
discloses the bit, but not the label. After success the receiver chooses Safe
for reward 2/5, or guesses the label for reward one if correct. Safe pays
the sender R/2; a label guess pays R for labels A and B, and zero for C.
After failure the receiver guesses the bit. Guess one pays sender label A
R; guess zero pays label B R; all other failed-case sender rewards are zero.
The receiver's failed-case reward is one exactly for a correct bit guess.
The remaining signals and observations are exactly the linked finite
comparison's declared menus and views, not an unrestricted network game.

Assume an escrow audit at settlement charges c once for any raw sender
signal or any emitted opening not accepted by the application deadline.
It also collects a forfeit D_phys when no opening is accepted. These are
explicit additional settlement assumptions. Eventual public delivery alone
does not prove that the native audit identifies, dates or charges every
packet this way. In particular, subsequent stale publication must not erase
the deadline charge. Both deductions must be funded.

The accepted opening pays its fixed actual fee f once, whether protected or
late; an excluded call pays no producer fee. Write

\[
D_{\rm eff}=D_{\rm phys}-f.
\]

The monetary deductions enter additive, quasilinear utility in this
proposition. An unavoidable cash fee need not cancel under an arbitrary
utility function of terminal wealth.
Adding the constant f to the sender's utility at every terminal history
normalizes successful rewards to the comparison's base rewards and failed
rewards to base minus D_eff minus any audit charge. This normalization
changes no incentive, SE consistency or rationality condition. The source
and target actual successful payoffs both remain base minus f; no claim of
fee-free payoff fidelity is being made.

**Proposition, paper proof.** Fix reward R>0, D_eff>R, c>R/2,
lambda in (0,1), and any finite receiver notification cost. For all
sufficiently small epsilon>0 the restricted audited game has no SE with
the mandatory-opening source outcome. All constants, including f and
collateral, are fixed before epsilon is selected. This is not a new Lean
theorem, an impossibility for lawful source refusal, or a native compiler
claim.

**Proof.** Choose q=1-epsilon above the explicit threshold in the
[checked quantifier statement](quantifier-orders.md#what-the-checked-theorem-says),
using D_eff. The sole-opening and exposure laws are the checked ones;
only the retry law differs, having each retry included with probability
q/2 instead of q/(1+q).

The generalization follows the dependencies already inspected in
[the hidden-rate argument](miner-assumptions.md#the-negative-comparison-also-survives-a-hidden-inclusion-rate).
At the last sender turn, raw signals and duplicate openings incur the audit
charge pathwise; never opening incurs the forfeit. The strict comparison
with one opening uses only q, so every purported preserving SE has the
same core play: send if no opening has been emitted, otherwise remain silent.
The consistency face proof uses positive core history weights and continuous
retry coefficients multiplied by duplicate-action probabilities. Those
probabilities tend to zero. Its decisive cross products remain q squared
and zero, since 0<q/2<1/2. Thus the same missing-label alternative and
receiver best response follow. Under core play the opposite timing
preferences and profitable protected deferral calculation use only the
sole-opening law q. They give the same contradiction. The additive fee
normalization transfers it to actual utilities.

Two independent mathematical reviews accepted the delivery probabilities,
fee normalization and retry-law proof dependency argument. The complete
finite-interface proposition remains a paper proof, not a checked theorem.

The probabilistic environment in this proposition is produced by independent
background traffic and honest fee maximization. The terminal audit and
restricted player information and action interface remain separate premises.
It is therefore a complete paper negative for that finite interface, not
a claim that producer honesty alone causes nonpreservation.

If epsilon is hidden with a finite common prior, independent of source
types and with no extra pre-selection observations, marginalizing it replaces
q by its mean and the retry coefficient by mean(q)/2. The same proof applies
when the prior is supported above the bad q threshold. This is a direct
Bayesian argument, not an inference from pointwise fixed-q failures.

## What these candidates tell us to choose

The capacity-rich model suggests a small positive target: public admission
and propagation bounds, adequate physical slack before irreversible choices,
and an explicit audit for additional actions. Its concrete single-phase
positive still needs all the phase theorem's information and payoff
restrictions. General retained-state commit-reveal sequences remain open.

The fee model suggests a small negative test: one uncertain last block,
independent competing load, and two unequal observer delivery ages. Neither
malicious miners nor permanently secret pending packets are needed for those
physical premises. The native theorem is blocked by the action, information,
audit and fee adapters, not by the retry lottery's particular formula.

The useful public properties are accordingly more specific than
non-collusion: who receives which packets by which physical times, which
calls fit, what bids are allowed, what counts as final, and what evidence
collects an incremental charge. No unique minimal ledger interface follows
from these two examples.

## Owning APIs and unproved adapters

The current
[asynchronous contract](../../Vegas/Pending/ReactiveAsyncContract.lean)
provides bounded owner opportunity, protected sole-identifier inclusion and
terminal completion over all legal raw histories. It does not itself provide
these candidates' network propagation, block revenue or finality model.
[Complete pending observation](../../Interaction/CompletePendingObservation.lean)
and its
[raw decision corollary](../../Interaction/ReactiveCompleteObservation.lean)
prove visibility under the expressly complete observation rule; they do not
derive that rule from a real network delay bound.

A common finite game with all retained source information and all actual
allowed actions must still be exhibited before either candidate is claimed
as a compiler theorem. For the negative, the independent identifiers,
observer timestamps, raw channel, final audit and lawful refusal are material
adapter questions. For the positive, the corresponding questions include
early authentic disclosure, retained correlated secrets, competing players'
capacity effects, and off-path continuation equilibrium completion. No Lean
files, checklist boxes or adopted semantics are changed by this note.
