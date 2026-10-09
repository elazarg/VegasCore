# Two late openings in the actual message runtime

This note tests the native runtime, including its full bounded raw response
menu, rather than adding a hypothetical private scheduler or allowing a reveal
to cross a commitment barrier. The construction below is a paper analysis of
an explicit finite configuration. Its full native SE theorem has not been
entered into Lean. The typed source, initial law, utilities and source-prefix
facts are checked in
[LateOpeningRuntimeSource.lean](../../Vegas/Examples/LateOpeningRuntimeSource.lean).
The exact initialized Safe joint law of every intended source SE, and a
source SE permitting failed publications with that same law, are checked in
[LateOpeningRuntimeSourceEquilibrium.lean](../../Vegas/Examples/LateOpeningRuntimeSourceEquilibrium.lean).
The [checked runtime boundaries](checked-runtime-boundaries.md) distinguish
additional operational and belief lemmas from that missing full theorem. In
particular, the checked settle-late comparison is not itself the native result
stated here.

The proposed obstruction uses one immutable opening, two opportunities to
send it after its protected window, and an intervening observation of pending
traffic. A later guess really occurs after the opening has either succeeded or
expired. Extra raw packets are included in the incentive argument. With a
sufficiently large fixed audit deposit, they are unprofitable on the particular
clean histories used by the argument; arbitrary behavior after an earlier
charged departure remains possible.

## Native facts used

The declaration surfaces of the following owning modules were inspected with
`lean-defs.py`, after reading the project architecture and checklist.

| Native component | Fact used here |
| --- | --- |
| [OpeningEvidence.lean](../../Vegas/Pending/OpeningEvidence.lean) | An opening certificate concerns an immutable candidate. It can be retained and forwarded. A readiness token names the event and is issued only after all predecessors complete; it does not contain an emission timestamp. |
| [EventSubmission.lean](../../Vegas/Pending/EventSubmission.lean) | Preparing a candidate requires an emitted commitment submission. An opening submission does not secretly prepare another candidate. |
| [EventApplication.lean](../../Vegas/Pending/EventApplication.lean) | The message author must own the addressed event. An opening must concern the selected binding. An event completes at most once. Every submission creates a new message identifier. |
| [ReactiveAsyncContract.lean](../../Vegas/Pending/ReactiveAsyncContract.lean) | The scheduler reads its public environment history and view. Its opportunity and protected receipt promises quantify over every legal raw history. A protected receipt may report rejection. |
| [ReactiveSettledVerdict.lean](../../Vegas/Pending/ReactiveSettledVerdict.lean) | A completed event permits an emitted packet only when that identifier was accepted and the final content checks pass. An accepted late canonical opening is clean; an unsuccessful extra identifier is not. |
| [ReactiveServiceAudit.lean](../../Vegas/Pending/ReactiveServiceAudit.lean) | There is one capped charge per author, not a fresh fine for each packet. A missed binding is also charged. |
| [ReactiveRiskMenu.lean](../../Vegas/Pending/ReactiveRiskMenu.lean) | After a late opening has been emitted, the sender can have the entire effective menu. The analysis below allows the larger raw menu from the beginning. |
| [Forfeit.lean](../../Vegas/Source/Forfeit.lean) | The source forfeit counts failed reveals. Silent withholding has its original failure payoff minus that forfeit. |

The checked native [late recovery example](../../Vegas/Examples/CommittedResolutionRecovery.lean)
already establishes that a sole late canonical opening can be accepted,
publish its immutable value, and remain clean under the settled audit. The
additional issue here is the equilibrium effect of having two such sending
opportunities.

## Source program and utilities

There are two players, Alice and Bob. The initial context contains an Alice
commitment to a Boolean bit `b`, and an Alice-only private input `l` in
`range 0 2`, encoding labels A, B and C. The initial commitment is successful
in every supported state. Nature chooses `Pr(b = true) = 9/20` and an
independent uniform label. The label is an ordinary private input, so it has
no outstanding reveal obligation.

Concretely, use source cell names zero for the bit and one for the label,
initial context `[(0, commitment Alice bool), (1, privateInput Alice
(range 0 2))]`, initial obligations `{0}`, and instruction names two for
the bit publication, three for Bob's binding, and four for its publication.
The initial law has six supported typed states. The guard on Bob's binding
has no checks. All its six values are admitted and the initial bit binding
is successful, so this is a finite well-formed intended source setup.

The program has exactly three strategic instructions, in this order:

1. Reveal Alice's initial bit commitment.
2. Bob commits an unguarded answer in `range 0 5`.
3. Bob reveals that answer.

The answer domain encodes Safe, three label guesses and two bit guesses.
The final `ret` can have an empty expression-payoff list; the game utility
interface reads the initial parameter `(b,l)` and the typed public outcome.
These are the existing source utility interfaces, not a utility of an
unaccepted privately attempted binding. The initial context and obligations
can therefore be instantiated using `CellTy.commitment`,
`CellTy.privateInput`, `SourceProgram.reveal`, `SourceProgram.commit` and
`SourceProgram.ret` from [Basic.lean](../../Vegas/Source/Basic.lean).

If Alice's reveal succeeds, Bob receives `2/5` for Safe and one for a correct
label guess. A bit guess pays zero. Alice receives `R/2` for Safe; any label
guess pays labels A and B `R` and label C zero. If Alice's reveal fails,
Bob receives one for a correct bit guess and zero otherwise. Alice then
receives `R` for a guess of one when her label is A, `R` for a guess of zero
when her label is B, and zero otherwise. A failed Bob answer reveal pays
both players zero gross. All Alice gross utilities lie in `[0,R]`, and all
Bob gross utilities lie in `[0,1]`.

Use the native source forfeit scalar `D > max(R,1)`, and target audit deposits
`K_A > R` and `K_B > 1`. These three constants are fixed before the builder is
chosen. For the main calculation the authentic audit observes the whole
actual signed traffic list. This is one allowed audit instance; a positive
coverage variant is given below.

Choose a scheduler-command horizon `H` containing the complete padded
calendar, and native `MessageBounds.candidateCount >= H >= 3`. Choose a
finite raw-value set containing both Boolean values, the three typed label
values and the six typed answer values.
This covers every source binding choice and every initial candidate value.
The argument also permits any finite superset of that alphabet. The raw
menu still includes every event/principal handle, malformed call, optional
private opening material, and bounded owned or known-forwarded evidence
request. The alphabet is not restricted to canonical packets. The fixed
physical schedule has finitely many commands and each response emits at
most one packet; thus its histories, observations and response menus are
finite. The initial law has six states, each pending-observation draw is a
finite subset draw, and every scheduler lottery has finite support.
`Control.remaining` counts scheduler commands, not player responses; the
calendar's wait padding fixes that command count even at conditional
activation stages. Its native protocol traces have length at most
`2H+1`, and the scheduler returns wait beyond the finite calendar.

In the intended source, both reveals are mandatory. Bob always chooses Safe
after the bit is revealed, because each label still has probability `1/3`,
strictly below `2/5`. This gives an SE with initialized joint law

`(b,l, successful bit b, successful answer Safe, R/2, 2/5)`.

It is also a selected SE of the source with lawful withholding and the stated
forfeits: withholding either reveal yields a net reward below zero, whereas
opening gives a nonnegative reward. A type-independent fully mixed
withholding sequence supplies the ordinary Bayes beliefs at source failure
histories. Thus this example does not change what lawful source withholding
means.

## A public finite builder

Call the three events `A`, `B`, `C`. Use sequential execution, so the
Alice reveal must complete before Bob's answer binding is ready, and that
binding must complete before Bob's answer reveal is ready. Set the relative
deadline durations, opportunity delays and protected inclusion bounds to

| Event | Deadline duration | Opportunity delay | Inclusion bound |
| --- | ---: | ---: | ---: |
| Alice bit reveal `A` | 3 | 0 | 2 |
| Bob answer binding `B` | 3 | 2 | 0 |
| Bob answer reveal `C` | 4 | 3 | 0 |

Every row satisfies `delay + bound < duration`. These deadlines start when
the event becomes ready, exactly as in the runtime; they are not absolute
source-calendar deadlines.

The builder follows the finite public schedule below. Any inclusion command
selects the latest pending identifier of the specified author, and lets the native handler
accept or reject its content. In particular, the protected Bob receipts are
issued for wrong content as well as for successful typed responses.

| Clock | Public operations |
| ---: | --- |
| 0 | Activate Alice. Include her emitted packet, if any. |
| 1 | Activate Alice at the first late turn. Activate Bob, allowing a pending observation. Include Bob's emitted packet, if any. |
| 2 | Activate Alice at the second late turn. Resolve the late Alice inclusion lottery described below. |
| 3 | Expire `A` if it is still unresolved. Activate Bob and issue a receipt for his emitted packet, regardless of its addressed call. If `B` is now completed, activate Bob again and issue its packet receipt; otherwise provide no second binding activation. |
| 6 | Expire `B` if needed. Activate Bob for the newly ready or still ready `C`, and issue a receipt for his emitted packet. |
| 10 | Expire `C` if needed. End the execution. |

Clock advances are individual commands. Conditional branches can be padded
with waits to give a fixed finite physical horizon. All branch conditions
above inspect only the public cut, pending envelopes and public receipts.
There is no prediction of source chance, hidden private service state or
private candidate value.

The clock-zero Alice receipt is certain. After an initially silent Alice,
neither late opening is included before the final late turn. A sole proper
late opening is then included with probability `q`, where `0 < q < 1`.
For two proper openings, choose either identifier with probability
`q/(1+q)` and neither with probability `(1-q)/(1+q)`. Other late envelopes
may be ignored. A proper opening here means its public call, certificate
and token have the canonical opening shape for Alice's initial handle;
authenticity and initial immutability fix its bit. The scheduler need not
read a secret value to recognize that shape.

At each player activation, independently sample each foreign pending
identifier with probability `lambda`, where `0 < lambda < 1`. Native passive
learning keeps any certificate already received. A dropped opening remains
pending after expiry and may be sampled at Bob's answer activation. No
claim is made that pending packets are invisible.

The later Bob reveal activation is conditional on the binding already being
completed. Otherwise a Bob wait at clock three would grant another binding
choice and another pre-commit sample. The conditional activation excludes
that extra information-gathering strategy. Waiting until the clock-six
activation cannot rescue the binding: it has already expired.

### Universal contract obligations

The promises must hold for raw deviations, not only the intended execution.
The following checks determine the schedule above.

Alice's initial reveal is ready at zero and its owner is activated at zero.
Any sole addressed initial packet gets its receipt immediately, even if it
is rejected. Alice's sole late packet cannot activate the protected receipt
obligation before expiry: a clock-one packet needs `1+2 < clock`, and a
clock-two packet needs `2+2 < clock`, whereas the event completes or expires
at clock three. After a duplicate the sole-identifier premise is false.

Bob's binding becomes ready at clock zero, two or three. The clock-one or
clock-three activation occurs before the opportunity promise would require
an earlier ready activation. Its first addressed packet gets an immediate
receipt before another clock advance. It expires by clock six even if every
response is invalid or silent. A binding ready at zero is already outside
its duration-three deadline at clock three; the genuine successful binding
callback on that branch is clock one. A late Alice resolution instead
makes the clock-three binding callback live and protected.

Bob's reveal becomes ready at clock one, three or six. Readiness at one
gets an activation at three, readiness at three gets the second activation
at that same clock, and a newly ready reveal after the clock-six binding
expiry is activated at six. These meet its delay-three promise and
duration-four deadline. Every sole addressed reveal response gets an immediate
receipt. Expiry at ten completes every remaining reveal. Thus the intended
finite schedule supplies opportunity, protected receipt and final
completion uniformly over the raw response tree.

## Full raw actions on the relevant clean histories

The following comparisons use only terminal bounds. They do not assume that
raw messages are absent, or that another player's reply is honest.

Alice owns only event `A`. A packet which is not its proper initial-handle
opening is terminally forbidden. This does not mean that every such packet
is rejected by the handler: a correct private opening with no public
certificate can be accepted, while its final settled content is still
forbidden. The proper public packet is precisely the permitted opening:
selected initial handle, immutable Boolean value, matching public opening
fact, and the issued event token. All raw submission representations which
emit that same packet are included as aliases. A second emitted
packet leaves at least one unaccepted identifier, because `A` completes at
most once and every response creates a fresh identifier. Under the stated
audit, either case collects `K_A` at the final settled record. Therefore any
such continuation has utility at most `R-K_A`.

At the protected root, sending the proper opening and then remaining quiet
has utility at least zero. A permanently forbidden first packet is strictly
worse. After a protected silence, sending a sole proper late opening, or
holding the already emitted first late opening, has utility at least

`-(1-q)(D+K_A)`.

If

`(1-q)(D+K_A) < min(D,K_A)-R`,                      (1)

every extra raw packet at these clean late histories is strictly worse.
After a first late silence, never submitting is also strictly worse: it
gives at most `R-D`. Thus the remaining equilibrium late controls are
exactly: send at the first late turn and then hold, or wait and send at the
second late turn.

These are local claims about histories with no earlier forbidden Alice
packet. Once a charge is already unavoidable, its marginal cost is zero;
additional signals in that dirty continuation are not ruled out.

Bob's premature packet cannot complete a not-yet-ready binding, since it
lacks its readiness credential. His own wrong-event and extra packets are
likewise forbidden. Such a deviation yields at most `1-K_B < 0`, whereas
quietly waiting for the protected answer choice gives a nonnegative reward.
At his actual answer binding, a correct fresh handle and a typed registered
answer has a protected, free continuation. An unopenable or wrong-typed
binding fixes its selected candidate to failure; later registration cannot
change that immutable meaning, and its failed reveal loses `D`. This has
utility below zero. Once a
typed answer is bound, eventually opening it successfully is strictly
better than allowing its reveal to fail or emitting a forbidden replacement.
Its owner may postpone a protected clock-three opening to a still-live
protected clock-six callback, when both are available. That postponement
does not alter the immutable answer and is permitted by the proof. All six
typed answers remain available; the
wrong-branch answers simply give zero and are strictly inferior to an
appropriate guess or Safe.

This includes retained certificates and private candidate preparation.
Creating or forwarding an additional certificate is not an uncharged new
move on these histories. It requires an extra signed identifier, or cannot
change the selected immutable binding. Bob cannot resolve Alice's event by
forwarding her certificate: the handler also checks the message author.

## The consistency argument

Suppose a native SE has exactly the selected source joint law, including
initial parameters, typed results and net utilities. It must use the proper
protected Alice opening at every type. Every execution starting with silence
has a strictly positive chance that Alice fails, regardless of its finite
late raw strategy. An initialized forbidden packet would also change the
specified net utility. The selected law excludes both.

Take the fully mixed sequence witnessing this hypothetical SE. Fix a bit
`b`, and write `d_l,n` for Alice's protected-silence probability and `a_l,n`
for her probability of a proper opening at the first late turn, conditional
on that silence. Both are actual native behavioral probabilities; `d_l,n`
may vanish at different rates for different labels.

There are two clean Bob late-success records. In record `E`, his clock-one
observation already contained the proper pending opening. In record `U`,
it contained none. His clock-one public state still had Alice unresolved
in both cases. At the answer choice, his ledger contains the one accepted
Alice opening, with identifier zero and public bit `b`. Both late sending
times otherwise produce the same remembered native views. In particular,
identifier zero does not reveal the emission time.

An earlier Alice raw emission would shift a later accepted identifier to at
least one, so it cannot enter these records. A Bob raw emission at the
observation turn changes his own remembered action, so it also cannot enter
the records with his own prior silence. An unseen extra Alice packet after
the first proper opening can enter the same observation fiber, but its
probability tends to zero uniformly relative to the corresponding first
opening prefix: at every such finite Alice information set, (1) strictly
forces the second response to be quiet. This remains true after any Bob
raw signal. Consequently the contaminating mass is bounded by a vanishing
factor times `sum_l pi_l d_l,n a_l,n`; it does not depend on a favorable
ratio between the protected deferral trembles.

After summing actual finite native histories and removing these vanishing
terms, the Bayes weights are

`E: pi_l d_l,n a_l,n`,

`U: pi_l d_l,n (1-lambda a_l,n)`.

More precisely, if `r_E,l,n` and `r_U,l,n` denote these full native label
masses, there are common positive constants `c_E,n,c_U,n` and a sequence
`eta_n -> 0` such that, uniformly over the three labels,

`r_E,l,n = c_E,n pi_l d_l,n a_l,n (1+e_E,l,n)`,

`r_U,l,n = c_U,n pi_l d_l,n (1-lambda a_l,n) (1+e_U,l,n)`,

where `|e_E,l,n|,|e_U,l,n| <= eta_n`. The error includes the probability of
not sending the second proper opening after a first silence, of an extra
packet after the first proper opening, and of a Bob premature packet at an
otherwise clean observation. At each finite relevant information set these
probabilities tend to zero uniformly. For `E`, every possible contribution
still has the first proper-opening prefix and its factor `d_l,n a_l,n`.
For `U`, its clean coefficient is bounded below by `1-lambda`. These facts
give multiplicative errors even if a label's deferral tremble is arbitrarily
smaller than the other strategy trembles. Probabilities of raw submission
aliases are summed before making this bound; their packets and private
candidate states after a proper opening have the same physical effect.

The common service and leak factors cancel. The second denominator stays
at least `1-lambda` times the deferral mass. For the first record, the
relative extra-packet bound above applies even when its total mass vanishes
faster. This is a full-history likelihood calculation, not an arbitrary
choice of off-path beliefs.

Let `mu_E,mu_U` be the limiting label beliefs. The resulting cross identity
is

`mu_E(h) mu_U(s) a_s (1-lambda a_h)`
` = mu_E(s) mu_U(h) a_h (1-lambda a_s)`.                (2)

Bob's later typed answer reveal is protected and immutable, so the binding
choice implements the genuine Safe-or-guess decision. If a limiting
success belief excludes one label, a remaining label has probability at
least `1/2 > 2/5`. Safe is then strictly suboptimal.

## Opposite choices and a profitable deferral

Leave Bob's failure belief with no observed bit completely unrestricted.
Let `x` be the probability that he guesses one at that record. It is one
native information set shared by both bit values. Raw histories can affect
its belief; the proof does not require it to retain the source bit prior.
Whenever Bob has the proper opening certificate, authenticity fixes the
bit throughout his information fiber, and his protected answer uniquely
guesses that bit.

Write `s_E(b),s_U(b)` for the Safe probabilities on the two late-success
records. The difference between Alice's first-late-send value and her
wait-then-second-send value is, for labels A, B and C,

`(P+T, P-T, -P)`,

where

`P = q lambda R (s_U(b)-s_E(b))/2`,

`T = (1-q) R lambda (1-lambda) (b-x)`.                 (3)

The extra first pending observation accounts for `T`: the first opening
can be learned at either of two Bob activations, whereas the second can be
learned only at the answer activation. The same forfeit and one-time audit
loss occur on either failed sole-opening route and cancel in the difference.

Some bit has `b-x != 0`. For that bit, `T != 0`. Whatever `P` is, one label
strictly prefers the first late send and another strictly prefers the
second. Call them `s,h`, so `a_s=1` and `a_h=0`. Substitution in (2) gives
`mu_E(h) mu_U(s)=0`. At least one successful record excludes a label and
therefore makes Bob choose a label guess.

If that record is `E`, an Alice with label A or B can defer and send first.
Her utility is at least

`q[lambda R+(1-lambda)R/2]-(1-q)(D+K_A)`.

At `U` she gets at least `R/2`; if Bob also guesses there she gets `R`.
If the guessing record is `U`, she can instead defer and send second,
obtaining at least `qR-(1-q)(D+K_A)`. Both bounds beat the source reward
`R/2` whenever

`q > (D+K_A+R/2)/(D+K_A+(1+lambda)R/2)`.           (4)

This contradicts sequential rationality at her protected root.

## Result and scope

The setting is ideal hiding, binding and authentication with the native ideal
opening certificates and readiness tokens. Participants are already funded,
and the builder is an exogenous public chance process. The finite symbolic
game includes all declared bounded raw messages and the actual sampled
settlement. It omits fees, utility of elapsed time, financing and participation
choices, strategic producer incentives, coalitions, outside communication and
external financial positions. There is no computational-equilibrium claim or
certification of a deployed chain's capacity, propagation or finality.

For the explicit finite native configuration above, (1)--(4) prove the
following independently reviewed paper theorem. For every fixed `R>0`,
`D>max(R,1)`, `K_A>R`, `K_B>1`, and `0<lambda<1`, choose

`q > max(1-(min(D,K_A)-R)/(D+K_A),`
`        (D+K_A+R/2)/(D+K_A+(1+lambda)R/2))`.

That maximum is strictly below one. The source has the stated SE, but no
SE of this full finite raw target has its joint initial-parameter, result
and net-utility law. This refutes an existential forward preservation
claim for this builder family with the full raw response menu. It does
not assert that the target has no SE, or that every public-mempool game
lacks SE. Its failure branch and all raw histories
remain part of the finite target.

For a numerical example, take `R=1`, `D=K_A=K_B=2`, `lambda=1/2`
and `q=24/25`. These satisfy both thresholds. Alice's source reward is
`1/2`; the first-send deviation bound is
`(24/25)(3/4)-(1/25)4=14/25>1/2`.
Thus this fixture fails at 96% sole-opening inclusion, with both deposits
equal to two reward units and a 4% late failure probability.

The more general authentic sampler that observes all actual traffic with
fixed probability `alpha>0` and observes none otherwise gives a coverage
variant. Replace the bad-packet upper bounds by `R-alpha K_A` and
`1-alpha K_B`; use `alpha K_A>R`, `alpha K_B>1`, and retain the conservative
sole-opening lower bound using `D+K_A`. No independence between packet
contents and observed traffic is needed for those bounds. A native claim
under an arbitrary audit still needs its stated conditional coverage
assumption; mere authentic-subset sampling does not provide it.

For this variant choose `q` using
`(1-q)(D+K_A) < min(D,alpha K_A)-R`, together with (4). The positivity
conditions again make the common threshold strictly below one. The
complete-audit threshold cannot be reused unchanged when `alpha<1`.

The construction does not require late fresh value choices or failed-binding
erasure. Its sender's value is an immutable successful initial commitment.
Bob's only fresh binding is his ordinary source answer. It therefore avoids
the separate gap caused by retained evidence about an unaccepted privately
attempted value. Those richer late-binding cases remain separate.

The configured late service is type independent and uses only public
envelopes. The independent Bernoulli observation rule is author-only: it
reads the observer, pending authors and identifiers, not packet contents.
The public builder can also satisfy the actual
`EventGraphRuntime.BlindToLatePackets` predicate from
[ReactiveLateBlind.lean](../../Vegas/Pending/ReactiveLateBlind.lean), including
its quantification over arbitrary environment views and command recalls.
This needs the following total extension of the finite schedule, rather
than an assumption about its initialized paths.

Use the length of the public command recall as the stage index. At the final
Alice lottery, form the
finite set `S` of all pending identifiers, including malformed packets.
If `n=|S|>0`, choose each identifier with probability
`q/[1+(n-1)q]`, and wait with probability
`(1-q)/[1+(n-1)q]`; for `n=0`, wait. On legal fixture histories this gives
the stated sole and duplicate laws. Using a set of identifiers makes the
extension well defined even for arbitrary views with duplicate identifiers.

Erasing a pending identifier leaves exactly `n-1` pending identifiers,
after the native serial renaming. Restore maps them bijectively to the
retained original identifiers. The `n`-identifier law is exactly the
mixture of including the erased identifier with weight
`q/[1+(n-1)q]` and the restored `(n-1)`-identifier law with the remaining
weight. For an absent identifier the inclusion weight is zero. All
other inclusion stages use the latest pending envelope of the prescribed
author: if it is the erased identifier, give that include command weight
one; otherwise erasure and restoration leave the selected command unchanged.
The activation gates read only the application's public cut, which native
packet erasure preserves. Erasure also preserves recall length. These are
the required mixture identities on every view, not merely legal views.

Thus neither the approved author-only observation restriction nor this
particular late-packet erasure restriction by itself removes the mechanism.
Complete pending observation `lambda=1`, immediate resolution between the
two late turns,
a single late callback, or different opportunities for the receiver are
outside this calculation.

The contradiction uses joint off-path SE consistency. It does not prove
PBE impossibility: a weaker notion requiring Bayes' rule only at positively
reached information sets has additional freedom at both late-success records.
For `K_A>R` and the other baseline bounds, the
[reviewed full native weak-PBE construction](native-weak-pbe.md) preserves
the same selected source law for every `0<q<1`. It covers every raw
continuation and uses Bayes' rule only at positive-reach information sets.
Stronger PBE conventions remain separate questions.

## Smaller sender deposit

For this same finite native configuration, the negative can be strengthened
to `K_A>R/2`, keeping `D>max(R,1)` and `K_B>1`. No runtime assumption is
added. The stronger local comparisons use Bob's rational answer after a
successful late opening, including histories where his earlier raw response
has already made his own audit charge unavoidable.

The relevant Alice histories have her protected silence, no earlier
forbidden Alice packet, and an unresolved `A` throughout Bob's clock-one
observation. Consequently Bob cannot already have completed `B` there. If
his observation response was silent, his canonical prepared slot zero is
still fresh. If he emitted any raw packet, that packet could not have been
accepted at an owned ready event: `B` and `C` are unready, and he cannot act
as the owner of `A`. His packet is permanently forbidden, so under the
complete audit `K_B` is the same sunk deduction on every continuation.

Private preparation cannot exhaust Bob's resources. Every earlier response
can prepare or freeze at most its one authored commitment handle. Initially
all prepared slots are fresh. The bound `candidateCount>=H` therefore
leaves a fresh prepared slot at the live clock-three binding choice. After
Alice succeeds, Bob can bind typed Safe to that slot and subsequently open
it at an available protected `C` callback. This is an actual full raw move,
even when its handle has a noncanonical serial:

- `Submission.register` and `Submission.candidateAfter_eq` fix the supplied
  typed value before its commitment is transmitted.
- `handle_commitment_eq`, or equivalently
  `freshServiceAcceptable_accepted`, accepts the owned, unused handle at a
  ready binding within its deadline. The handler imposes no canonical
  serial requirement.
- The stored value is Safe, the selected handle belongs to Bob, the resolve
  node has no guard checks, and the matching owned opening fact and issued
  `C` token give the conditions of `handle_opening_eq`.

These are the declarations in
[EventSubmission.lean](../../Vegas/Pending/EventSubmission.lean),
[ReactiveFreshCallAcceptance.lean](../../Vegas/Pending/ReactiveFreshCallAcceptance.lean)
and [EventApplication.lean](../../Vegas/Pending/EventApplication.lean).
The noncanonical binding is itself an audit offense, but adds no charge
after Bob's earlier forbidden packet. When no earlier charge exists, use
the still-fresh canonical slot zero instead. Thus Bob can obtain `2/5`
minus his already sunk charge with no failed reveal.

An answer binding is immutable, including a binding with no supplied
opening material. The authored commitment freezes that candidate to
unopenable; a later registration cannot fill or change it. In particular,
accepting an empty handle does not grant a delayed logical answer choice.
A wrong-branch bit guess after Alice's success gives Bob zero gross; an
unopenable or wrong-typed binding, or permanently declining its reveal,
also loses `D`. Both are strictly worse than the Safe fallback. At this
live binding choice no Alice decision remains, so signalling cannot create
a further reward. Bob's eventual successful answer is consequently Safe
or a label guess, irrespective of his earlier raw observation response or
poisoned candidate slots. A delayed opening publishes that same answer.

For Alice's labels A and B, every such success gives at least `R/2`. For
label C, gross reward always lies in `[0,R/2]`, on every success or failure.
Let `delta=1-q`. The local comparisons on these late histories are therefore

| Alice label | Sole proper send, or hold its pending opening | An extra or permanently forbidden packet | Never submit after first silence |
| --- | ---: | ---: | ---: |
| A or B | at least `qR/2-delta(D+K_A)` | at most `R-K_A` | at most `R-D` |
| C | at least `-delta(D+K_A)` | at most `R/2-K_A` | exactly `-D` |

The single margin

`delta(D+K_A+R/2) < min(D,K_A)-R/2`                     (5)

makes every required comparison strict. It is feasible for every fixed
`K_A>R/2`. Hence the same uniform relative-likelihood bounds, cross identity
(2), opposite timing preferences (3), and profitable root deviation (4)
apply. The resulting sufficient builder threshold is

`q > max((D+K_A+R-min(D,K_A))/(D+K_A+R/2),`
`        (D+K_A+R/2)/(D+K_A+(1+lambda)R/2))`.

Both terms are strictly below one. Thus for every such fixed collateral,
some builder in this explicit native family has no preserving full raw SE.

The success floor was established only for these relevant late histories.
It is not asserted at an arbitrary post-protected history where Bob has
already irrevocably selected a bad answer. The hypothetical preserved joint
law itself forces Alice's initialized proper protected opening and excludes
initialized audit offenses. This supplies the root reward `R/2`; the proof
does not need an independent universal floor on all post-protected raw
continuations.

There is also a partial-audit version for the exact all-traffic-or-none
sampler with a fixed probability `alpha`. Assume `alpha K_B>1` and
`alpha K_A>R/2`. After a forbidden Bob observation packet his expected
traffic charge is `alpha K_B` under every later accepted-binding strategy.
Omitting the binding can only increase that charge via the public omission
branch. The Safe fallback and wrong-answer comparison therefore retain
the same sunk deduction. Replace the extra-packet bounds in the table by
`R-alpha K_A` and `R/2-alpha K_A`, keep the conservative sole-opening bounds,
and impose

`delta(D+K_A+R/2) < min(D,alpha K_A)-R/2`,              (6)

together with (4). A `q<1` satisfying both again exists. This smaller-deposit
variant is not derived from arbitrary conditional coverage alone: such an
audit can change its collection probability with later packet content, so
the dirty Bob fallback need not have the same sunk expected charge.

Status: the complete paper proof passed independent mathematical review,
independent native source/scheduler/resource review, and the coordinating
review. The reviews include the full raw-menu comparisons, relative rare-site
likelihood bounds, universal raw-history contract promises, and all-view
late-packet erasure identity. They also cover the smaller-deposit corollary,
its fresh-handle fallback and its exact partial-audit accounting.
The [checked runtime boundaries](checked-runtime-boundaries.md) give the
current Lean evidence: the actual source equilibrium law, native alphabet and
capacity, finite nature, complete all-raw scheduler contract and all-view
erasure independence, typed readout invariants, audit cleanliness, and exact
initialized pending-observation prefixes. Checked actual information-set
incentives additionally force early Bob silence, Alice's final opening after
silence, no duplicate after a genuine pending opening, and Bob continuation
value at least one half after Alice's failure. One admissible builder gives
both Alice laws with collateral fixed first. Actual permitted Alice envelopes
are classified through their complete emitted ledger identity.
Complete raw receiver optimization after failure is also checked: every
supported current response fixes a maximizing Boolean guess, with no
posterior assumption. An authentic remembered bit certificate forces correct
clean publication throughout the supported continuation. First-late sender
repair excludes nongenuine packets using her unchanged future policy and
actual legal final-callback descendants. Preserving even the public Alice
publication marginal forces protected acceptance almost surely.
A checked native SE counterexample is still missing. Successful-publication
receiver optimization is checked, including clean settlement and Alice's
success floor on positive receiver-belief histories. The full native history
groups are connected to physical prefix probabilities and actual consistent
conditional-belief limits. One common SE consistency witness controls all
three sender response errors uniformly. The remaining obligations include
transferring successful settlement to deviation histories assigned zero Bob
belief, legitimate first-versus-second timing comparisons, observation-specific
relative likelihood calculations, and the SE cross-identity and initial
deviation argument.
These are formalization tasks for the explicit configuration, rather than
an assumed private runtime interface.
