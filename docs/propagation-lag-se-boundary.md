# Public packets can arrive after an irreversible decision

Analysis by Codex. Complete observation at every player activation is a
useful idealized runtime assumption. It is stronger than eventual public
availability with a bounded network delay. A packet can be public and still
arrive too late to affect another player's irreversible choice. This gives
a physically coherent interpretation of the selective observation diagram
used by the negative `LateLeak` comparison game. It does not yet provide a
checked embedding of that game into the full Vegas native interface.

## An explicit clocked observation diagram

Consider a required opening with ledger admission deadline $T=10$. The
service guarantees admission for protected submissions made at least four
time units before that deadline. The sender has a sure protected turn at
$t_0=0$ and two later submission opportunities at $t_1=7$ and $t_2=9$.
Both late opportunities fall outside the protected guarantee.

Use two public transport paths:

- ordinary transaction propagation to the receiver takes three time units;
- submission to the builder and propagation of an included block to the
  receiver take a total of $0.2$ time units.

The builder includes either late opening with a type-independent
probability $q\in(0,1)$. Inclusion occurs before $T$ and its public block
is seen before the receiver's decision. On the failure branch, the packet
is not included before that decision. It is still broadcast on the ordinary
public transaction path. There is no permanent hiding or deletion of its
contents.

The receiver makes an irreversible decision at $t_*=11$. Its observations
are then:

| Sender action | Admission result | Value observed before the decision |
| --- | --- | --- |
| Protected opening | Success | Yes, from the public ledger |
| First late opening at 7 | Success | Yes, from the public ledger |
| First late opening at 7 | Failure | Yes, transaction arrives at 10 |
| Second late opening at 9 | Success | Yes, from the public ledger |
| Second late opening at 9 | Failure | No, transaction arrives at 12 |
| Never opening | Failure | No packet exists |

The failed second packet becomes observable later. Its absence from the
receiver's view at time 11 is propagation delay, not a claim that public
pending packets are physically invisible. The timing constraints are

$$
t_1+\Delta\le t_*<t_2+\Delta,
\qquad t_2+\delta<T,
$$

where $\Delta$ is transaction propagation delay and $\delta$ is the faster
builder/block path. Different message classes or routes can have different
delays. The construction is conditional on those transport properties; it
does not claim that every deployed blockchain supplies them.
The receiver obtains neither the failed second packet's contents nor its
submission metadata before time 11. At that instant, second failure and
never sending have the same receiver observation. An earlier global
submission oracle, or a separate faster metadata feed, changes that
information partition and must be analyzed separately.

A bounded-delay guarantee gives an upper bound, not instantaneous knowledge.
The example selects executions attaining that bound on the transaction path.
A theorem meant to hold for every network satisfying only that upper bound
must cover these executions. An additional guarantee that failed pending
contents reach the receiver before its decision would exclude this
diagram. So would automatic inclusion of expired packets into a public block
before that decision, even if those inclusions no longer count as successful
openings.

If the receiver can strategically postpone its choice until after time 12,
the game changes. The diagram assumes an actual irreversible response
deadline, or equivalent incentives and an execution schedule forcing the
same decision order. Merely announcing that the receiver normally acts at
11 does not establish the premise. Likewise, a raw option to query a faster
pending-data source could invalidate the proposed observation interface.

## What the existing negative theorem would then establish

Take the finite strategic comparison game with exactly this observation
diagram, the `LateLeak` action menus and payoff rules, and its stated
`DeferralPays` parameter conditions. Its extensive form is the already
checked selective-disclosure game: failure at the first late turn reveals
the value before the receiver acts; failure at the second does not.
Later disclosure after the final choice has no strategic effect when there
are no later decisions and payoffs depend only on the already fixed result.

For that comparison game, the existing negative theorem applies. No SE
preserves the selected intended source outcome, and the checked
[timing-erased result bound](../Vegas/Examples/LateLeak/ObservableOutcomeSeparation.lean)
gives a strictly positive total-variation gap. Thus eventual disclosure does
not by itself substitute for disclosure before every strategically relevant
decision. Public transport with positive latency can preserve the exact
observation distinction required by the negative example.

This is a conditional comparison-game conclusion. It does not establish
that every public-mempool chain lacks a preserving SE, that the actual
Vegas compiler fails, or that the full native game is strategically
equivalent to the comparison game. Extra native actions can change off-path
continuation games and their consistent beliefs. In particular, one cannot
ignore legal source withholding, arbitrary raw packets, early submissions,
or additional receiver choices when claiming an actual-runtime theorem.

## The current carrier and the missing operational adapter

The current `MessageNetwork.ObservationRule` takes an observer and a pending
packet list, and samples packet identifiers. It has no physical clock,
send timestamp or recipient delivery queue. A stateless observation rule
alone therefore does not express a uniform age-based propagation bound.

A clocked transport primitive could realize the relevant diagram by
delivering the first late packet between the two late sends and retaining
it in the receiver's recall, while delivering the second packet only after
the final action. A fixed stateless observation rule does not acquire this
ability merely by inserting a scheduler probe: the first and second
submissions can have identical identifier and payload, and thus identical
pending lists at their respective final observations. It cannot return
different deliveries based on packet age that is absent from its input.
A runtime proof needs a clocked transport adapter or an explicit coupling
to per-recipient delivery queues. No semantics change is made here.

The existing `CommittedResolutionService` fixture is not already such an
embedding. It has one live late opportunity before expiry; its next owner
activation follows expiry. It also publishes the latest opening at a later
stage, including a stale opening, before activating the other player.
That publication makes the packet visible in the ordinary public ledger
and defeats the selective second-failure observation. Removing that
publication and adding a probe would not create the missing second live
late opportunity.

A native candidate would need a new primitive schedule with two live late
opportunities, a public observation probe between them, and no stale
publication before the receiver's irreversible action on the failure
branch. It must independently prove the all-history asynchronous service
contract and the observation law. The required expired-message omission
is not a pointwise support refinement of the existing fixture, whose
corresponding stage deterministically includes the latest packet.

The remaining equilibrium adapter must then account for the complete raw
player menus and lawful source `FALSE`, rather than importing the restricted
comparison-game impossibility. These are substantial proof obligations.
The clocked diagram establishes that the selective observation premise can
have a legitimate latency interpretation; it does not discharge them.

## Relation to the fully public positive result

The [fully public disclosure-phase theorem](full-public-disclosure-phase-preservation.md)
assumes every emitted value is observed before the receiver acts, whether
or not it was included. Under that assumption, a fixed immutable-value
phase admits a preserving target SE for every source Nash outcome, even
with arbitrary finite inclusion probabilities and arbitrary receiver
failure preferences. Its global tremble calibration uses equal type
posteriors at successful and failed emitted-message observations.

The delayed second-failure branch removes precisely that information
premise. This is a meaningful boundary between two public-transport models,
not a contradiction between the positive and negative results. Neither
instantaneous complete pending observation nor permanent hidden pending
traffic should be treated as the only possible physical model.

## Positive polling hazard: an exact observation-advantage argument

A useful alternative already fits a stateless packet-selection interface:
at each observer activation, independently select each pending packet with
a fixed hazard $h\in(0,1)$. Learned packets remain known. If a failed first
send is pending for $N$ more observations than a failed second send, and
both get one final observation, their disclosure probabilities are

$$
s_1=1-(1-h)^{N+1},\qquad s_2=h,
\qquad N\ge1\Rightarrow s_1>s_2.
$$

Every pending packet has positive disclosure probability at every poll.
Under indefinitely repeated polling it is eventually disclosed with
probability one. No zero-probability invisibility assumption is required.
This is a polling model, not by itself a deterministic bounded-delay
guarantee. For the native runtime, observer activations are also strategic
player turns; replacing their full action menus by automatic passive polls
would need a separate justification.

For the following comparison-game calculation, fix the `LateLeak` sender
and receiver payoff menus, equal late inclusion probability $q\in(0,1)$,
and type-independent failed-packet disclosure probabilities $s_1>s_2$.
After an observed failure the receiver knows the bit and strictly prefers
guessing it truthfully. Unseen first and second failures may even have
different timing metadata: let $\gamma_j$ be the probability of guessing
bit one after unseen failure at turn $j$. Such an observation does not
itself reveal the bit. The never-send reply can be separate again.

Write $g_j(w)$ for the receiver's probability of any label guess following
a successful opening at turn $j$ with public bit $w\in\{0,1\}$. Set

$$
p_w=\frac{qR}{2}(g_1(w)-g_2(w)),
\qquad
z_w=(s_1-s_2)w+(1-s_1)\gamma_1-(1-s_2)\gamma_2.
$$

The sender's first-send value minus its second-send value is exactly

$$
\Delta_{w,A}=p_w+(1-q)Rz_w,
\quad
\Delta_{w,B}=p_w-(1-q)Rz_w,
\quad
\Delta_{w,C}=-p_w.
$$

The common failure forfeit and dropped-packet charge cancel because the
inclusion probabilities coincide. For labels $A$ and $B$, any successful
label guess pays $R$ and the safe answer pays $R/2$; for $C$, a guess pays
zero and safe pays $R/2$. After failure, $A$ wants bit one and $B$ wants
bit zero. These payoff identities explain both pulls in the formula.

Since $z_1-z_0=s_1-s_2>0$, at least one bit has $z_w\ne0$.
At that bit the three differences include both a strictly positive and a
strictly negative value, for every $p_w$. If $p_w=0$, $A$ and $B$ have
opposite signs. If $p_w>0$, $C$ is negative and one of $A,B$ is positive;
if $p_w<0$, $C$ is positive and one of $A,B$ is negative. Thus some two
types with the same public bit strictly prefer opposite late turns.
This holds for every positive observation advantage, not only probabilities
close to the original deterministic first-seen/second-unseen example.

To remove the last-turn never-send alternative independently of all
off-path failure replies, it suffices to assume

$$
qD-(1-q)c>R.
$$

Any emitted opening then pays at least $-(1-q)(D+c)$, whereas never
opening, or an immediate failed source choice with no further opening
opportunity, pays at most $R-D$. The former strictly exceeds the latter.
This strong bound also permits timing-specific never-send replies; it does
not normalize arbitrary raw actions that retain further opportunities.

Under that bound, successful-emission path weights still have exactly the
form

$$
\pi_i d_i a_i q,
\qquad \pi_i d_i(1-a_i)b_i q,
$$

where $d_i$ is protected-turn deferral, $a_i$ first-turn sending, and
$b_i$ second-turn sending. Monitoring chance enters failed outcomes and
does not change these success weights. The existing consistency argument
uses precisely these weights and opposite strict timing preferences:
some late success posterior has a missing label. With only two remaining
labels, one has posterior at least $1/2$, exceeding the receiver's safe
payoff $2/5$, so the receiver must guess there.

If additionally

$$
qR-(1-q)(D+c)>R/2,
$$

a suitable $A$ or $B$ type gains by deferring from the protected safe
outcome to that guessing continuation. Hence the same preservation
contradiction has a paper extension to this finite polling comparison
game. The primitive payoff difference, opposite preferences, polling
advantage and strong last-send bound are checked in
[ObservationAdvantage.lean](../Vegas/Examples/LateLeak/ObservationAdvantage.lean),
whose targeted warning-strict build passes. The algebra and success-path
consistency mechanism are explicit, but the extended polling game and its
complete SE impossibility theorem have not been formalized in Lean. The
checked results for this polling extension are its primitive bounds.
A separate [full native obstruction](commit-reveal-research/native-se-obstruction.md)
is checked for the actual bounded raw runtime, full authentic audit and fair
partial samples at fixed $R>0$, $D>R$, $K_A>R$, $K_B>1$. It excludes the
source's joint terminal-store and realized-payoff law in every native SE;
it does not formalize this extended polling game or prove a public-result-only
impossibility.

The operational direction is therefore more substantial than an appeal
to unspecified robustness under chance perturbations. A fixed positive
sampling hazard can produce the needed strict observation advantage in
the existing carrier interface. Completing a native theorem for this polling
extension still requires
an actual all-history service schedule with two live late opportunities,
no forced stale publication before the answer, and a proof controlling
all strategic actions at the intervening observer activations.

The same comparison admits a preserving weak-PBE assessment. Give every
off-path late success information set the original uniform label posterior,
so the receiver answers safe. Disclosed failures are answered truthfully;
unseen failure replies can be justified by freely chosen off-path beliefs.
Choose a sequentially optimal sender continuation at each late turn under
these fixed replies. Protected opening gives every type $R/2$, while every
late send is bounded above by

$$
qR/2+(1-q)(R-D-c)<R/2
$$

when $D>R$ and $c\ge0$; never sending gives at most $R-D<0$.
Hence every type optimally uses the protected turn, and the on-path
receiver answers safe under the actual original posterior. All late
information sets are off path, so weak PBE does not require their beliefs
to come from one global tremble sequence. The strict opposite preferences
therefore coexist with a preserving weak PBE. The SE obstruction is the
success-posterior consistency requirement, not the existence of any
equilibrium on a public network. This weak-PBE statement is also a paper
proof for the comparison game, not a compiler capstone.
