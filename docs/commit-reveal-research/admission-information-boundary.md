# Admission risk and information gained before the next decision

Analysis by Codex. This note studies a boundary for accepting late calls
normally: can their information advantage be controlled by the risk of
failure, without requiring a uniform positive probability of failure?
The new statements are paper proofs. No runtime, source semantics, audit,
Lean declaration or checklist box changes here.

There is a useful positive for one immutable disclosure with one late
opportunity. There is also a bounded-propagation counterexample to a much
broader claim. The difference concerns the available decisions and their
information, not whether a pending plaintext packet exists.

## The comparison that would make vanishing risk harmless

Fix an information set, the opponents' continuation policies, and the
belief used to evaluate whole remaining policies. Let g be the base payoff
gain from a deviation over an available lawful continuation. Let r be its
incremental probability of a collectible charge K. Then its net gain is
g-Kr. If g<=Cr for every allowed continuation, choosing K>=C deters them
even when r can approach zero. A positive lower bound on r is unnecessary.
If r=0, the condition instead requires g<=0.

This is a comparison, not a mechanism or an SE extension theorem. The
increment must be relative to the lawful continuation: a charge already
paid in both continuations is not r. Base utility must include any other
actual costs. The receiver policies and conditional beliefs must belong to
one consistent assessment. They cannot be chosen independently to make each
comparison convenient.

Here is a useful way to derive such a bound from a protocol coupling rather
than assuming the desired payoff inequality.

**Paper coupling lemma.** Let target residual utility and a coupled lawful
source utility both lie in the same interval of width W. Outside the union
of a transport-failure event F and an observation-mismatch event L, their
terminal utilities agree. Suppose, conditionally at the decision under
study and under every allowed later policy,

\[
\Pr(F)=p,\qquad \Pr(L\setminus F)\le Cp.
\]

Suppose the coupled lawful source policy is no better than the assessed
lawful continuation, and that the deviation creates incremental collection
probability at least alpha p, with alpha>0. Its net gain is at most

\[
\bigl(W(1+C)-K\alpha\bigr)p.
\]

**Proof.** The utility difference is zero outside F union L and at most W
inside it. Its expected positive difference is at most W(1+C)p. Add the
source policy comparison and subtract the incremental charge.

For a concrete application, matching decoded transitions and each player's
entire remembered observation outside those events must prove the coupling
for the actual continuation policies. Source sequential rationality can
supply the source policy comparison only after its conditional-belief and
policy correspondence is established. Ordinary initialized output
closeness does not supply either fact. This lemma is deliberately a
conditional incentive bound, not a generic compiler theorem.

In particular, the probability that a failed packet's contents arrive can
be small while the eventual equilibrium's successful receiver replies
change substantially. That equilibrium effect is not bounded by pretending
that the receiver always uses the source reply.

## A complete one-late disclosure positive

### Finite source game

Nature draws a type i from a finite nonempty set with full-support prior pi.
The sender knows i. Its immutable committed value is v(i) in a finite set.
The receiver initially does not know i. There are no preceding strategic
choices or later phases in this game.

The source offers Open, which succeeds and discloses v(i), or lawful
Withhold, which fails without disclosing the value. After success the
receiver chooses from a finite nonempty menu A_v; after failure it chooses
from a finite nonempty menu B. Sender base utilities u_i^S(a), u_i^F(b)
lie in [0,R]. A failure subtracts the intrinsic source forfeit D>R.
Receiver utilities may be arbitrary functions of the type, publication
result and reply. Both players have perfect recall. Utilities are additive;
there are no fees, financing costs or outside payoffs in this statement.

Every source Nash equilibrium opens at every type. Withholding pays at
most R-D<0, whereas opening pays at least zero against any receiver policy.
Because every type has positive prior probability, withholding at any type
would create an ex ante profitable deviation. The selected source outcome
is therefore determined by receiver success replies beta_v, best responses
to pi(i|v). Write S_i for the sender's resulting expected success reward,
so 0<=S_i<=R. This covers every source weak PBE and SE as well.

A mandatory-opening source can instead omit Withhold. Its source success
outcomes are the same ones. The two source menus are different, even when
their initialized equilibrium laws agree.

### Finite target interface

The sender can Open at a protected opportunity, succeeding surely, or
Defer. After Defer there is exactly one owned late decision: Send or Never.
Send emits one fixed authenticated opening of v(i). It succeeds with
probability q(v(i)), where 0<q(v)<=1, and success reveals v(i). A failed
send pays D+c, where c>=0 is a fixed additional failure charge. Never pays
D. Accepted late sends have no extra charge.

The receiver makes no intermediate strategic move. It answers after the
resolution. After protected or late success it has the same legal menu
A_v and observes v and the route. After failure it observes a finite symbol
o and has menu B. A sent but failed opening produces o with probability
K_v(o); Never produces o with probability K_N(o). These are probability
kernels. They may reveal all, some or none of the emitted value, and their
supports may overlap. K_v depends only on the immutable value, not on any
remaining private component of i. K_N is independent of i.

Thus the receiver need not distinguish an unobserved failed send from Never.
The observation symbol can also encode public routing information and
failure metadata, subject to the stated kernels. No retries, other messages,
strategic value choices, receiver notifications, private bids or additional
timing decisions are allowed. All owned Send decisions use the single late
opportunity; multiple raw activations cannot silently be collapsed into it.

These are primitive finite menus and chance kernels. No receiver posterior
or off-path best response has been assumed.

### Paper theorem

If

\[
q(v)D-(1-q(v))c>R\quad\hbox{for every used value }v,
\]

then every source Nash equilibrium's joint initialized law of the type,
publication result, receiver reply and realized payoffs is implemented by
a target SE. In that assessment the sender opens at the protected
opportunity and sends after every off-path deferral. No penalty is paid on
initialized play. This is outcome implementation, not literal copying of
the source failure beliefs, menu or entire assessment, and not reflection
of every target equilibrium.

**Proof: the late choice.** Against any receiver continuation, Send pays at
least -(1-q)(D+c) and Never pays at most R-D. Thus Send exceeds Never by
at least qD-(1-q)c-R>0. This comparison holds at every sender type and
does not require a receiver belief or a failure-observation convention.

**Proof: one global consistency sequence.** At every type choose Defer with
probability epsilon and Open otherwise. At every late decision choose Never
with probability epsilon and Send otherwise. Perturb every receiver reply
lottery toward its full-support uniform lottery with weight epsilon.
Use the same epsilon tending to zero everywhere.

At a protected success revealing v, type weights are
pi_i(1-epsilon). At a late success they are
pi_i epsilon(1-epsilon)q(v). In each case the common factor cancels among
types with the same v. Both limiting type posteriors are exactly pi(i|v).
Prescribe the selected source reply beta_v at both successes.

At a failure observation o, marginal type weights, after canceling the
common root epsilon, are

\[
\pi_i\bigl[(1-\epsilon)(1-q(v(i)))K_{v(i)}(o)
                  +\epsilon K_N(o)\bigr].
\]

Let d_o be the sum of pi_i(1-q(v(i)))K_v(i)(o). If d_o>0, their normalized
limit is proportional to pi_i(1-q(v(i)))K_v(i)(o). If d_o=0 but
K_N(o)>0, it is pi. If both vanish, that observation is chance-impossible
and supplies no reachable information set. This handles q(v)=1 without
assigning arbitrary beliefs to a possible Never history. Choose any receiver
best response at each of these limiting failure beliefs.

The full history beliefs, rather than just their type marginals, are the
Bayesian beliefs along this one sequence. They converge: all finite history
weights are products of fixed chance coefficients and the displayed
epsilon lotteries, and every positive information-set denominator has a
leading positive coefficient. Taking these limits proves exact
Kreps-Wilson consistency. Receiver utilities depend on type, result and
reply, so the type calculations prove receiver sequential rationality.

**Proof: the root and whole continuations.** With these success replies,
Send after deferral pays at most

\[
q(v(i))S_i+(1-q(v(i)))(R-D-c)\le S_i.
\]

Never pays at most R-D<0<=S_i. Protected Open pays S_i. There are only
these two remaining sender continuations after deferral; arbitrary mixtures
cannot improve on their maximum. Hence protected Open is rational against
every whole continuation policy. The late choice is strictly rational by
the first comparison. Receiver optimality and the global consistency
sequence complete the SE proof. If q(v)<1 the root preference is strict;
if q(v)=1 it may be a tie, which is sufficient for implementation.

Two independent mathematical reviews accepted this finite-game construction.
It has not been formalized in Lean or adapted to the native raw menu.

### Public constants before the selected service

A public class with q(v)>=q_min>0 satisfies the theorem whenever

\[
D>\frac{R+(1-q_{\min})c}{q_{\min}}.
\]

There is no upper cap below one. The class includes certain late success
and sequences of builders with q approaching one. For a fixed D,c, the
equivalent useful service requirement is a public q_min satisfying
q_min D-(1-q_min)c>R.

D here is the intrinsic source forfeit. Choosing it describes a funded game
design or a parameterized source class before the builder is selected.
Increasing an already fixed lawful-Withhold source's D is a utility change,
not an automatic compiler-collateral choice. A separate extra enforcement
mechanism would need its own payoff and collection correspondence.

The quantified statement is uniform pointwise outcome existence. Failure
reply policies may depend on the selected kernels. It is not automatically
one complete equilibrium policy for players who know only bounds. For a
finite hidden service type independent of i, with no observations before
the late choice, marginalizing the joint resolution-and-observation kernel
gives the same construction under its specified common prior. In particular,
the failed-send weights use
E[(1-q_theta(v))K_theta,v(o)], not a product of separately averaged
kernels. When 1-E[q_theta(v)] is positive, divide these joint weights by
that probability to obtain the marginal conditional failure channel.
Public per-type lower bounds still imply the displayed Send comparison.

### The information gain is proportional to failure here

This construction proves the relevant bound instead of assuming the desired
success posteriors. For each late send, successful receiver replies produce
the same S_i as the source. Failure base reward is at most R. Its base gain
over protected Open is therefore at most

\[
(1-q)(R-S_i)\le R(1-q).
\]

The failure deduction D(1-q) dominates that gain because D>R; c only adds
another deduction. Never has unit failure probability and base gain at
most R-S_i. Arbitrary mixtures obey the same bound. Thus the base
gain-to-failure ratio is uniformly at most R, with zero gain when failure
probability is zero. The additional high-reliability inequality above is
used to obtain the consistent all-type Send completion; it is not a
uniform lower bound on failure.

## Full observation slack gives another restricted positive

Suppose every permitted opening is broadcast by a physical time T_emit,
every relevant receiver gets every such plaintext packet within Delta,
and its irrevocable decision occurs at or after T_emit+Delta. It then sees
even failed and rejected openings. This follows packet by packet from the
delivery bound and persistent memory, independently of inclusion risk.

For one immutable disclosure phase with finitely many sending opportunities,
no intermediate receiver choices and at most one emission, the
[fully public phase paper theorem](../full-public-disclosure-phase-preservation.md)
constructs a common tremble sequence and source replies at every successful
late opportunity. It allows arbitrary finite value-dependent reliabilities,
including zero and one. The same base-gain bound R times failure probability
then follows for all late policies. This uses that theorem's actual
assessment construction, not just the delivery lemma.

The slack statement excludes neither earlier observation nor temporary
pending ignorance; it specifies when ignorance must end. It is not implied
by a finite source horizon. Additional permitted sends after T_emit,
additional receiver choices before the cutoff, retained private commitments
across phases and arbitrary raw messages are outside this application.

## Changing the binding value is a different one-late game

The fixed immutable value restriction is material. The following complete
finite counterexample is a boundary for arbitrary utilities on private
terminal histories. Its failure reward uses a privately attempted value even
if its commitment was rejected. Such a value need not exist in the native
typed readout. This is not a native whole-program counterexample or a
refutation of a serial theorem restricted to that readout.

**Source.** Nature gives the sender a uniform private label A, B or C. It
chooses an opaque binding to x or y, then chooses Open or lawful Withhold.
Open reveals the value. The receiver then chooses Safe for reward 2/5, or
guesses the label for reward one if correct. Sender Safe rewards are R/2;
any guess pays sender labels A and B R, and label C zero. On failure the
receiver has no decision and receives zero. Sender failure gross reward is
R for label A with value x, R for label B with value y, and zero otherwise;
it also deducts D>R.
The locally selected value persists in the sender's private history.

There is a source SE in which every type binds x, opens, and the receiver
chooses Safe after either revealed value. Equal vanishing y-binding
trembles for all types, equal withholding trembles at every binding, and
full receiver trembles give uniform label posteriors at both successes.
Safe is strictly optimal because 2/5>1/3. Open strictly dominates Withhold,
and both binding choices give R/2 after Open. Its initialized law is value
x, successful Open, and Safe at every type.

**Target.** The sender can bind x or y at the protected opportunity, surely
succeeding, or Defer. After Defer there is one late binding decision: submit
x, submit y, or never submit after locally choosing either value. A submitted
binding succeeds with common probability q in (0,1), independent of the
value and label. On acceptance the sender has the source Open/Withhold
decision; failed submission deducts D+c, with c>=0, and retains its private
attempted value for the specified failure utility. Never and subsequent
Withhold deduct D. Submitted commitment contents are opaque; neither a
failed commitment nor its attempted value need be disclosed. There is no
intermediate receiver action or another channel.

After successful Open, the receiver observes the value and whether its
binding used the protected or late route. That route distinction is
essential: merging a late x history with initialized protected x histories
would invalidate the late-only face argument. Public receipt time can
provide it, but it is explicitly part of this finite model's observation.

**Proposition, paper proof.** For every fixed R>0, D>R and c>=0, every q
strictly between

\[
\max\left\{\frac{R+c}{D+c},
              \frac{D+c+R/2}{D+c+R}\right\}<1
\]

and one has no target SE implementing the selected source law.

**Proof.** After an accepted binding, Open strictly dominates Withhold:
every success reply gives a nonnegative reward, and Withhold gives at most
R-D<0. At the late binding decision, either submission gives at least
-(1-q)(D+c), whereas any Never continuation gives at most R-D. The first
threshold makes every Never choice strictly dominated by a submission.

Let s_x,s_y be the receiver's Safe probabilities at the two late-success
information sets, and set p=qR(s_y-s_x)/2. The difference between submitting
x and submitting y is, for the three labels,

\[
(p+(1-q)R,\quad p-(1-q)R,\quad -p).
\]

Some label strictly chooses x and another strictly chooses y. If p>0,
label A prefers x and C prefers y; if p<0, C prefers x and B prefers y;
if p=0, A prefers x and B prefers y.

Call these labels s and h, respectively. In each fully mixed consistency
witness, let a_i be its late x-submission probability multiplied by its
Open probability at the resulting accepted x node; define b_i analogously
for y. The common acceptance factor q is kept outside these products.
Let d_i be the protected deferral probability. Bayesian
late-success type weights are proportional to pi_i d_i a_i and
pi_i d_i b_i. Hence the exact cross identity is

\[
\mu_x(h)\mu_y(s)a_s b_h
 =\mu_x(s)\mu_y(h)a_h b_s.
\]

These are the actual probabilities, not b_i=1-a_i: Never and later
Withhold still have positive probability in fully mixed witnesses.
In the equilibrium limit a_s=b_h=1 and a_h=b_s=0. Thus
mu_x(h)mu_y(s)=0. At least one late-success posterior excludes a label.
One of its two remaining labels has probability at least 1/2>2/5, so
the receiver strictly chooses a label guess there.

Either sender label A or B can defer and select that value. Its reward is
at least qR-(1-q)(D+c), exceeding R/2 by the second threshold. A target
profile with the selected source law must use protected x and Safe at
every type: any positive deferral probability creates a positive chance
of failure, and protected y changes the value law. The displayed deviation
contradicts its initial sequential rationality.

The witness has base gain at least qR-R/2 and failure risk 1-q. Its
base gain-to-risk ratio is at least R/[2(1-q)]-R, again diverging as q
approaches one. No failed commitment plaintext or intermediate receiver
decision is involved; the value-dependent private failure utility is the
essential extra premise in this example.

This proof also explains the utility boundary. With equal q and a failure
gross reward independent of the attempted value, the (1-q)R and -(1-q)R
terms disappear. The forced opposite value choices and this face argument
then disappear as well. The example does not establish a negative under
that narrower payoff restriction. Two independent mathematical reviews
accepted this counterexample with its route and full-history utility
restrictions. It warns against automatically copying a
source lottery over binding values into a late decision when rare failures
change those values' continuation utilities.

## Bounded propagation alone does not bound the ratio

The [honest-producer finite interface](honest-producer-models.md) gives a
counterexample. It has a mandatory-opening source, a protected opportunity,
two live late opportunities and an intervening receiver observation. Every
plaintext opening reaches every observer within a fixed finite bound.
The earlier pending opening has greater probability of being seen before
the irrevocable reply. A sole late opening succeeds with q approaching one
as independent competing load becomes rare. All these calendars and
delivery bounds can remain fixed while q varies.

In a purported preserving SE of that restricted comparison, the consistency
face argument and receiver optimality force a profitable deferral witness
with expected base reward at least

\[
q\bigl(\lambda R+(1-\lambda)R/2\bigr).
\]

Protected base reward is R/2. The witness emits one opening, whose failure
risk is 1-q. Therefore its base gain-to-risk ratio has lower bound

\[
\frac{g(q)}{1-q}
\ge \frac{\lambda R}{2(1-q)}-\frac{(1+\lambda)R}{2},
\]

which diverges for fixed lambda>0. Its expected failure deductions are only
(D+c)(1-q), with finite D,c. The inspected retry-law generalization gives
the same conclusion for honest one-slot fee selection; the existing
fixed-rate comparison is machine checked. These are restricted interface
results. An embedding of that fee-maximizing producer interface remains
unproved. The separate [native two-late construction](native-late-action-analysis.md)
has a reviewed paper proof including its actual full raw actions, observations
and settled audit; it does not inherit the producer interface or its fee model.

The mathematical reason is subtle. Failed-packet observation influences
different types' strict timing preferences, even when their payoff
differences become arbitrarily small. Their choices then constrain the
posterior at *successful* late histories. Receiver best replies there can
change the successful reward by a fixed amount. A coupling that holds only
while the receiver replays its source reply misses this effect. Bounding
the probability of a failed packet does not by itself bound the rational
receiver's continuation change.

Thus bounded public propagation and ordinary high inclusion reliability do
not imply g(q)<=C(1-q) for a fixed C. The number and order of strategic
decisions and the information released before them matter.

## What the actual runtime already shows, and what remains open

The checked
[accepted late recovery fixture](../../Vegas/Examples/CommittedResolutionRecovery.lean)
has an actual initial-law-supported late canonical opening, accepted outside
its protected inclusion window, permitted by the risk menu when available,
and uncharged by every authentic settlement sampler. Its deterministic
recovery scheduler satisfies the actual asynchronous contract. This rules
out deriving a positive late-failure or late-charge floor merely from that
contract. It is an operational result, not an SE impossibility or a proof of
the one-late phase theorem for the native game.

The new positive suggests a precise next native test: can all raw actions
and remembered observations in a single-disclosure fixture be reduced to
one fixed-value late decision, with no strategically relevant receiver move
before resolution? Its lawful FALSE decision, private preparation, additional
activations, forwarded proofs and rejected packet observations cannot be
discarded without proofs. A constant number of source events does not bound
or normalize those physical decisions.

The [checked two-live-opportunity native test](native-se-obstruction.md)
controls the extra channels, full authentic final audit and common native
Bayesian limits. It fixes one immutable initial opening and allows the entire
bounded raw menu; no late private value is inserted into the utility interface.
For fixed $R>0$, $D>R$, $K_A>R$ and $K_B>1$, with fair partial pending samples,
one admissible builder has arbitrarily small positive canonical omission but
no SE matching the source's exact joint terminal-store and realized-payoff
law. Native SE exist. The sharper $K_A>R/2$ and broader sampling/audit
variants remain [paper results](native-late-action-analysis.md). General
multi-phase preservation with retained correlated private state, and a negative
for the public-result marginal alone, are outside these conclusions.
