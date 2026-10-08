# Sequential equilibrium for a fully public disclosure phase

Analysis by Codex. For a single immutable-value disclosure phase, complete
observation permits a stronger positive result than the particular
`LateLeak` construction. Any fixed finite number of late turns may have
different inclusion probabilities, including zero or one. Arbitrary receiver
preferences after failure do not by themselves destroy preservation.
A common global tremble sequence can keep
the original type posterior at every late transmission site, even when some
types strictly prefer never transmitting at those sites.

The theorem below is a paper proof. It has not been connected to the Lean
sequential-equilibrium definitions or to an actual Vegas source-to-runtime
adapter. It preserves the initialized outcome of every source Nash equilibrium,
and therefore of every source weak PBE or SE. It does not preserve all of a
selected source assessment's off-path responses or beliefs.
The extension below also allows correlated private receiver information
under a full-support joint prior, and slot reliabilities depending on the
publicly disclosed immutable value.

## Source game and runtime comparison

Let $T$ be a nonempty finite type set with full-support prior $\pi$. Nature
draws $i\in T$, known to the sender. Its immutable committed value is
$v(i)$ in a finite public value set. The receiver initially does not know the
type. No other strategic decision precedes this phase.

In the source game the sender chooses either:

- open, which succeeds and publicly reveals $v(i)$;
- withhold, which produces a failed publication without revealing $v(i)$.

After success, the receiver selects a legal answer from a finite nonempty menu
$A_{v(i)}$. After failure, it selects an answer from a finite nonempty menu $B$.
Each player has perfect recall. There are no further decisions after this
answer.

Write $u_i^S(a)$ and $u_i^F(b)$ for the sender's base payoffs, and $r_i^S(a)$
and $r_i^F(b)$ for the receiver's payoffs. Assume, after subtracting a common
constant from all sender payoffs, that

$$
0\le u_i^S(a),u_i^F(b)\le R,
\qquad R\ge0,
\qquad D>R.
$$

Successful disclosure pays the sender its base payoff. Failed publication,
including lawful source withholding, subtracts the failure forfeit $D$.
Receiver failure preferences are otherwise arbitrary: guessing the disclosed
value need not be optimal, and different types may favor different failure
answers. Payoffs depend on the type, publication result and receiver answer,
not on physical transmission timing.

The target comparison game adds two late opportunities. The sender may open
at the protected turn, or defer to the first late turn. At the first late turn
it sends or waits. After waiting it sends or never sends at the second late
turn. Protected opening succeeds surely. Each late send succeeds with the
same probability $q\in(0,1)$, independently of the hidden type. Only one
packet is emitted on each play. The equal-$q$ assumption is removed in the
distinct-reliability construction below, permitting arbitrary
$q_1,q_2\in(0,1)$. An unsuccessful late send also subtracts a
finite charge $c\ge0$, in addition to the failure forfeit.

The receiver observes the transmission turn and whether it succeeded.
Every emitted packet reveals $v(i)$, including both failed late transmissions.
Never sending reveals no value. The receiver's answer menus and base payoffs
are the source ones for the corresponding success or failure result. There
are no aliases, retries, value-changing submissions, extra player decisions
or other signals.

## Preservation statement

Every source Nash equilibrium opens at every sender type. Indeed, any success payoff is
nonnegative, whereas any withholding payoff is at most $R-D<0$.
Each type has positive prior probability, so changing its choice from
withholding to opening gives a strictly profitable ex ante unilateral
deviation whenever withholding has positive probability. After all types
open, every reached receiver success information set has positive probability.
Nash optimality there already requires a best response to the conditional
prior; sequential rationality and source off-path beliefs are unnecessary.
Consequently its initialized outcome is determined by its receiver replies
$\beta^*_v$, each Bayes-optimal for the original conditional type prior
$\pi(\cdot\mid v)$ after success.

For every such collection $\beta^*$, the target comparison game has an SE
whose protected opening and successful receiver reply are exactly those
of the source equilibrium. It therefore preserves the joint law of the type,
publication result, receiver answer and both realized payoffs. No late charge
or failure forfeit is incurred on initialized play. This holds for the
common-$q$ model proved first, for two distinct probabilities, and for the
finite-opportunity extension with $q_j\in[0,1]$ proved below.

The target may choose another reply after never sending. That source failure
branch has probability zero. The statement is outcome preservation of each
source Nash equilibrium, not a requirement that every off-path source assessment component
be copied literally.

## Choosing the off-path continuation

For each observed value $v$, choose any failure reply $\beta^F_v$ that maximizes
the receiver's expected failure payoff under $\pi(\cdot\mid v)$. Define

$$
S_i=u_i^S(\beta^*_{v(i)}),
\qquad F_i=u_i^F(\beta^F_{v(i)}).
$$

For a candidate no-emission reply $b$, set

$$
W_i(b)=u_i^F(b),
\qquad
C_i=q(S_i+D)+(1-q)(F_i-c).
$$

The sender's late-send payoff is $C_i-D$, while its never-send payoff is
$W_i(b)-D$. The subtraction by $D$ is common in this local comparison.

Consider the following auxiliary finite normal-form game. One player selects a
type $i$ and receives $W_i(b)-C_i$. The other selects $b\in B$ and receives
$r_i^F(b)$. A mixed Nash equilibrium exists. Write its strategies as
$(w,\beta^0)$, and put

$$
m_i=W_i(\beta^0)-C_i,
\qquad m=\max_i m_i.
$$

The receiver reply $\beta^0$ is optimal under the type distribution $w$.
Moreover, $w$ assigns positive probability only to types with $m_i=m$.
This is an ordinary finite-game existence step, not an assumption about the
desired runtime posterior.

If $m>0$, define $N=\{i:m_i>0\}$ and $S=T\setminus N$. Then $N$ is nonempty
and $w$ is supported on $N$. Prescribe never sending at both late turns for
types in $N$. For types in $S$, prescribe sending with probability $1/2$ at
the first late turn and surely at the second.

If $m\le0$, prescribe the latter sending behavior for every type. This case
has no never-sending types in the limiting strategy. Nevertheless, the
receiver still needs a consistent optimal reply at the never-send information
set, and $w$ will provide its limiting belief there.

Prescribe protected opening for all types. After every successful opening use
$\beta^*_{v(i)}$. After every emitted failed opening use $\beta^F_{v(i)}$.
After never sending use $\beta^0$.

## A single fully mixed consistency sequence

Let $\varepsilon\downarrow0$, with each term positive and small enough that
$\varepsilon<\min(1/4,\min_i\pi_i/4)$. Put $\delta=\varepsilon^3$.
For each type, write $d_i$ for its protected-turn deferral probability,
$a_i$ for its first-late send probability, and $b_i$ for its second-late send
probability conditional on waiting at the first late turn. The constructions
below give all three probabilities strictly between zero and one.

Both cases enforce the two exact equalities

$$
d_i a_i=\delta,
\qquad
d_i(1-a_i)b_i=\delta.
$$

Thus the unconditional probability of reaching either specified late
transmission, before inclusion is sampled, is exactly $\delta\pi_i$ for each
type. The factor $\pi_i$ comes from Nature; it must not be inserted again in
the conditional emission probabilities.

**When $m>0$.** For $i\in N$, choose

$$
d_i=\varepsilon\frac{w_i}{\pi_i}+\varepsilon^2,
\qquad a_i=\frac{\delta}{d_i},
\qquad b_i=\frac{a_i}{1-a_i}.
$$

Here $d_i\ge\varepsilon^2$, so $a_i\le\varepsilon<1/4$ and
$0<b_i<1$. Both late send probabilities tend to zero, as prescribed.
For $i\in S$, choose

$$
b_i=1-\varepsilon,
\qquad a_i=\frac{b_i}{1+b_i},
\qquad d_i=\delta\frac{1+b_i}{b_i}.
$$

Then $a_i\to1/2$ and $b_i\to1$. Every $d_i\to0$.

For $i\in N$, the unconditional never-send probability is exactly

$$
\pi_i d_i(1-a_i)(1-b_i)
=\pi_i(d_i-2\delta)
=\varepsilon w_i+\varepsilon^2\pi_i-2\varepsilon^3\pi_i.
$$

For $i\in S$, it is

$$
\pi_i\delta\frac{\varepsilon}{1-\varepsilon}
=O(\varepsilon^4).
$$

Since $w$ is supported on $N$ and sums to one, the normalized never-send
posterior tends to $w$. This includes types with $w_i=0$: their probabilities
remain positive along the sequence and vanish at a faster rate.

**When $m\le0$.** For every type, choose

$$
b_i=1-\varepsilon\left(\frac{w_i}{\pi_i}+\varepsilon\right),
\qquad a_i=\frac{b_i}{1+b_i},
\qquad d_i=\delta\frac{1+b_i}{b_i}.
$$

Smallness of $\varepsilon$ ensures $0<b_i<1$. The limit again has first-late
send probability $1/2$, second-late send probability one, and protected-turn
deferral probability zero. The unconditional never-send probability is

$$
\pi_i\delta\frac{1-b_i}{b_i}
=\delta\varepsilon\frac{w_i+\varepsilon\pi_i}{b_i}.
$$

After division by $\delta\varepsilon$, these weights converge to $w_i$.
Their normalized posterior therefore tends to $w$, including when some
$w_i=0$.

At each receiver information set, perturb its prescribed mixed reply by a
vanishing positive mixture with the uniform distribution over its legal
answers. This makes every receiver action probability positive. All sender
choices are already fully mixed. The resulting profiles form one common
fully mixed sequence converging to the prescribed target strategy.

## Its Bayes limits

At protected success, the type weights are $\pi_i(1-d_i)$. Conditional on
the disclosed value they tend to $\pi(\cdot\mid v)$.

At first-late success, the type weights are $q\delta\pi_i$. At first-late
failure they are $(1-q)\delta\pi_i$. The corresponding second-late weights
are exactly the same. Conditional on the disclosed value, all four posteriors
are therefore exactly $\pi(\cdot\mid v)$ at every term of the sequence.
Observing the turn and inclusion result adds no hidden-type likelihood factor.

At never sending, no value was disclosed, and the preceding calculations give
the limiting posterior $w$ over the entire type set.

These are precisely the receiver information sets in this comparison game.
The sender knows its type at each of its decisions. Thus the common sequence
establishes sequential consistency of the whole assessment.

Notice why a proposed negative proof based only on the limiting off-path
sender strategy would fail. A type that never sends in that strategy can still
have positive limiting Bayes weight at *both* emitted-packet information sets.
Its comparatively larger protected-turn deferral tremble compensates its
comparatively smaller subsequent send trembles. Consistency concerns the
common fully mixed sequence, not Bayes conditioning of the limiting strategy
at a zero-probability event.

## Sequential rationality

Receiver success replies $\beta^*_v$ are rational under the transported source
posterior. Emitted-failure replies $\beta^F_v$ are rational by construction.
The no-emission reply $\beta^0$ is rational under $w$ by the auxiliary Nash
equilibrium.

At the second late turn, the difference between never sending and sending is
exactly $m_i$. If $m>0$, never sending is strictly optimal for every type in
$N$, and sending is weakly optimal for every type in $S$. If $m\le0$, sending
is weakly optimal for every type. Types with $m_i=0$ may send without violating
rationality.

At the first late turn, the payoff from sending is the same as the payoff from
sending at the second: both have the common inclusion probability, identical
success and emitted-failure posterior, identical prescribed replies and
identical charge. A type in $S$, or any type in the $m\le0$ case, may therefore
mix with probability $1/2$ between these equally optimal timings. A type in
$N$ gets the strictly better never-send payoff by waiting and then never
sending. Its prescribed first-late wait is optimal.

At the protected turn, opening pays $S_i\ge0$. Any late send pays

$$
qS_i+(1-q)(F_i-D-c)<S_i,
$$

because $F_i\le R<D$ and $c\ge0$. Never sending pays
$W_i(\beta^0)-D\le R-D<0\le S_i$.
Every complete sender continuation after deferring is a mixture of first-late
send, second-late send and never send, so it also pays strictly less than
protected opening. This verifies whole-continuation rationality, not merely
the prescribed immediate action.

The assessment is consequently an SE and has the source equilibrium's
initialized joint outcome and payoff law.

## Distinct inclusion probabilities at the two late turns

The same preservation statement holds for arbitrary
$q_1,q_2\in(0,1)$. Keep the source-success and emitted-failure replies
$\beta^*,\beta^F$ fixed as above. Write

$$
V_{ij}=q_j S_i+(1-q_j)(F_i-D-c),
\qquad m_{ij}(b)=W_i(b)-D-V_{ij}.
$$

The difference between two send payoffs has the sign of their inclusion
probability difference, for every type:

$$
V_{i1}-V_{i2}
=(q_1-q_2)(S_i-F_i+D+c).
$$

The last factor is strictly positive, because $D>R$, $S_i\ge0$, $F_i\le R$
and $c\ge0$. Thus all types rank two sends by reliability. Their comparison
with never sending can still differ.

For every construction in this section, choose positive emission factors
$\delta_1,\delta_2$ tending to zero and a positive conditional never-send
probability $p_i$. Define

$$
d_i=\delta_1+\delta_2+p_i,
\qquad a_i=\frac{\delta_1}{d_i},
\qquad b_i=\frac{\delta_2}{\delta_2+p_i}.
$$

For sufficiently small $\varepsilon$, the choices below make $0<d_i,a_i,b_i<1$.
They give the exact identities

$$
d_i a_i=\delta_1,
\qquad d_i(1-a_i)b_i=\delta_2,
\qquad d_i(1-a_i)(1-b_i)=p_i.
$$

Therefore both success and emitted-failure posteriors equal
$\pi(\cdot\mid v)$ at each turn, despite different inclusion probabilities.
The never-send posterior is obtained by normalizing $\pi_i p_i$.

### The first late turn is more reliable

Suppose $q_1>q_2$. Then $m_{i1}(b)<m_{i2}(b)$ for every type and reply.
We need a reply $\beta^0$ whose consistent no-emission posterior is supported
on the appropriate never-sending types. A sequence of finite auxiliary games
provides it.

For each positive integer $K$, give the selector pure actions
$(i,z_1,z_2)\in T\times\{0,1\}^2$. Its payoff against a receiver answer $b$ is

$$
Kz_1 m_{i1}(b)+z_2 m_{i2}(b).
$$

The receiver payoff is $r_i^F(b)$, independent of the selector's flags. Take
a mixed Nash equilibrium of each finite game and project the selector strategy
to a type distribution $w^K$. Against a receiver lottery $\beta^{0,K}$, its
best achievable payoff for a fixed type is exactly

$$
H_i^K=K\bigl(m_{i1}(\beta^{0,K})\bigr)^+
       +\bigl(m_{i2}(\beta^{0,K})\bigr)^+,
\qquad x^+=\max(x,0).
$$

The flags are essential: this is the positive part of the *expected* payoff,
obtained by maximizing over selector flags. Assigning a positive-part payoff
directly to each pure receiver answer would instead average positive parts,
which is a different game.

Take a convergent subsequence $(w^K,\beta^{0,K})\to(w,\beta^0)$, with
$K\to\infty$. Receiver best-response inequalities pass to the limit, so
$\beta^0$ is optimal under $w$. Put
$m_{ij}=m_{ij}(\beta^0)$ and $M_j=\max_i m_{ij}$.

- If $M_1>0$, then $w$ is supported on $N_1=\{i:m_{i1}>0\}$.
  Any type outside $N_1$ has a strictly smaller first positive-part term than
  a type with $m_{i1}=M_1$. Multiplication by $K$ eventually dominates the
  uniformly bounded second term, so that outside type cannot receive positive
  equilibrium selector probability.
- If $M_1\le0$ and $M_2>0$, then $w$ is supported on
  $N_2=\{i:m_{i2}>0\}$. For a type outside $N_2$,
  $m_{i1}<m_{i2}\le0$, so its first term is eventually zero and its second
  term tends to zero. A type with strictly positive $m_{i2}$ has selector
  payoff bounded away from zero. Again the outside type cannot remain in the
  limiting selector support. This covers the boundary $M_1=0$.
- If $M_2\le0$, every type weakly prefers sending to never sending at the
  second late turn; no support condition on $w$ is needed.

At the second late turn prescribe never sending when $m_{i2}>0$, and sending
when $m_{i2}\le0$. At the first late turn prescribe waiting when $m_{i1}>0$,
and sending when $m_{i1}\le0$. These choices are rational: if $m_{i1}>0$,
never sending beats both sends; otherwise the more reliable first send beats
the second send and weakly beats never sending. Equality at the first turn is
resolved in favor of sending.

The following explicit calibrations implement these limiting choices. All
smallness conditions are uniform because $T$ is finite and $\pi_i>0$.

**If $M_1>0$**, take $\delta_1=\varepsilon^4$ and
$\delta_2=\varepsilon^6$, and set

$$
p_i=\begin{cases}
\varepsilon w_i/\pi_i+\varepsilon^2,&i\in N_1,\\
\varepsilon^5,&i\in N_2\setminus N_1,\\
\varepsilon^7,&i\notin N_2.
\end{cases}
$$

For $N_1$, $p_i\gg\delta_1$, so $a_i,b_i\to0$. For
$N_2\setminus N_1$, $\delta_2\ll p_i\ll\delta_1$, so $a_i\to1$ and
$b_i\to0$. For the remaining types, $p_i\ll\delta_2\ll\delta_1$, so both
send probabilities tend to one. Since $w$ is supported on $N_1$, the
normalized never-send weights tend to $w$.

**If $M_1\le0<M_2$**, take $\delta_1=\varepsilon^3$ and
$\delta_2=\varepsilon^7$, and set

$$
p_i=\begin{cases}
\varepsilon^5 w_i/\pi_i+\varepsilon^6,&i\in N_2,\\
\varepsilon^8,&i\notin N_2.
\end{cases}
$$

All first-send probabilities tend to one. At the second turn they tend to zero
on $N_2$ and one elsewhere. The normalized never-send weights tend to $w$.

**If $M_2\le0$**, take $\delta_1=\varepsilon^3$,
$\delta_2=\varepsilon^5$, and

$$
p_i=\varepsilon^6 w_i/\pi_i+\varepsilon^7.
$$

Both send probabilities tend to one, while the normalized never-send weights
again tend to $w$. Every protected deferral probability tends to zero in all
three cases.

### The second late turn is more reliable

Suppose $q_1<q_2$. Use the original auxiliary normal game with selector payoff
$m_{i2}(b)$ and receiver payoff $r_i^F(b)$. Its equilibrium gives a reply
$\beta^0$, a prior $w$ and $M_2=\max_i m_{i2}(\beta^0)$. If $M_2>0$, $w$
is supported on $N_2=\{i:m_{i2}(\beta^0)>0\}$.

Every type waits at the first late turn: waiting leads either to the strictly
better second send or to an even better never-send payoff. At the second turn,
types in $N_2$ never send; the others send. If $M_2\le0$, all types send at
the second turn.

Take $\delta_1=\varepsilon^6$, $\delta_2=\varepsilon^4$. If $M_2>0$, set

$$
p_i=\begin{cases}
\varepsilon w_i/\pi_i+\varepsilon^2,&i\in N_2,\\
\varepsilon^5,&i\notin N_2.
\end{cases}
$$

If $M_2\le0$, set $p_i=\varepsilon^5 w_i/\pi_i+\varepsilon^6$ for every
type. In both cases $a_i\le\delta_1/\delta_2\to0$. The second-turn
probabilities have the prescribed limits, and the no-emission posterior tends
to $w$.

### Completing the distinct-reliability assessment

Perturb receiver replies to full support as before. The common global sender
calibration keeps the protected posterior asymptotically equal to the source
posterior, both emitted posteriors exactly equal to the source conditional
prior, and the never-send posterior equal to $w$ in the limit. This establishes
consistency with the actual different inclusion laws.

The preceding comparisons prove rationality at both late turns. Protected
opening beats each late-send payoff and the never-send payoff by the same
$D>R$ argument used in the common-$q$ proof. It therefore beats every complete
late continuation, regardless of which turn is more reliable. The initialized
source outcome and payoff law is preserved.

## Any finite number of late opportunities

The strongest single-phase statement allows $n\ge1$ late opportunities, with
conditional inclusion probabilities $q_j\in[0,1]$, independent of the hidden
type at each chosen send. The sender may wait between opportunities, but
emits at most one packet. After that packet resolves there are no additional
sender choices before the receiver answers. A phase with no late opportunities
reduces to the source comparison.

The probabilities need not be monotone. No independence between counterfactual
inclusion outcomes at different slots is required: only one send occurs, so
only the selected slot's conditional kernel is sampled. There are no additional
private signals about that kernel before choosing a slot.

Keep $\beta^*,\beta^F$ as before, and define

$$
V_{ij}=q_jS_i+(1-q_j)(F_i-D-c),
\qquad m_{ij}(b)=W_i(b)-D-V_{ij}.
$$

Every type ranks sends by $q_j$, because
$S_i-F_i+D+c>0$. Keep the suffix-record slots

$$
j_1<\cdots<j_r,
\qquad q_{j_k}>q_\ell\text{ for every }\ell>j_k.
$$

The last slot is always a record, by the vacuous condition on its empty suffix.
The record reliabilities strictly decrease. Every nonrecord slot has a later
record of at least equal reliability. Prescribe waiting at each nonrecord
slot; this is optimal whenever the later record's send or never-send
continuation is optimal. Ties are resolved by waiting for the later slot.

At records, write $m_{ik}=m_{i,j_k}(\beta^0)$. For any receiver lottery
$\beta^0$, these margins strictly increase in $k$. Prescribe sending at a
record when $m_{ik}\le0$, and waiting otherwise. Once a margin is positive,
never sending beats this and every subsequent send. Thus each type has a
single cutoff

$$
\tau_i=\min\{k:m_{ik}>0\},
$$

or $\tau_i=r+1$ when the set is empty. It sends at record decisions before
its cutoff and waits at and after the cutoff. Equality is resolved by sending.

### A receiver reply with the required no-emission posterior

For each positive integer $K$, give the auxiliary selector actions
$(i,z_1,\ldots,z_r)\in T\times\{0,1\}^r$, payoff

$$
\sum_{k=1}^r K^{r-k}z_k m_{i,j_k}(b),
$$

and give the receiver payoff $r_i^F(b)$, independent of the flags. As in the
two-slot construction, finite Nash existence supplies equilibria. Project
their selector strategies to type laws and take a convergent subsequence
$(w^K,\beta^{0,K})\to(w,\beta^0)$. The receiver reply is optimal under $w$.
The selector's best payoff for each type is

$$
H_i^K=\sum_{k=1}^r K^{r-k}
       \bigl(m_{i,j_k}(\beta^{0,K})\bigr)^+.
$$

Let $k_*$ be the first record with $\max_i m_{ik_*}>0$, if one exists.
Then $w$ is supported on $N_{k_*}=\{i:m_{ik_*}>0\}$.
To see this, take a type outside $N_{k_*}$. Its earlier margins are strictly
negative, since they are strictly smaller than $m_{ik_*}\le0$. All
higher-priority terms are therefore exactly zero for sufficiently large $K$.
After division by $K^{r-k_*}$ its $k_*$ term tends to zero and its later
terms vanish. A type with positive $m_{ik_*}$ has normalized selector payoff
bounded away from zero. The outside type cannot retain positive equilibrium
selector weight.

All earlier maxima are nonpositive, so the types in $N_{k_*}$ have precisely
the first strict cutoff $\tau_i=k_*$. This argument also handles earlier
maxima equal to zero: their equality is resolved by sending, and the strict
margin differences eliminate their high-priority terms for an outside type.
If no such $k_*$ exists, every type sends at all record decisions, and no
support restriction on $w$ is needed.

### One global calibration for every slot

Choose a positive sequence $\varepsilon\to0$, sufficiently small uniformly
over the finite type and slot sets. At a record choose
$\delta_{j_k}=\varepsilon^{4k}$. At a nonrecord slot $j$, let $j_k$ be the
next record and choose $\delta_j=\varepsilon^{4k+1}$. This nonrecord emission
factor is negligible compared with that following record's factor.

If $k_*$ exists, choose

$$
p_i=\begin{cases}
\varepsilon^{4k_*-2}(w_i/\pi_i+\varepsilon),&\tau_i=k_*,\\
\varepsilon^{4\tau_i-2},&\tau_i>k_*.
\end{cases}
$$

All cutoffs satisfy $\tau_i\ge k_*$. If no $k_*$ exists, set
$p_i=\varepsilon^{4r+2}(w_i/\pi_i+\varepsilon)$ for every type.

Set the protected-turn deferral probability and each conditional late-send
probability to

$$
d_i=\sum_{j=1}^n\delta_j+p_i,
\qquad
a_{ij}=\frac{\delta_j}{\sum_{\ell=j}^n\delta_\ell+p_i}.
$$

All are strictly between zero and one when $\varepsilon$ is small. The
denominator contains $p_i>0$, even at the last slot. Products of conditional
wait probabilities telescope, giving

$$
d_i\left(\prod_{\ell<j}(1-a_{i\ell})\right)a_{ij}=\delta_j,
\qquad
d_i\prod_{j=1}^n(1-a_{ij})=p_i.
$$

Consequently every actual emitted slot has unconditional type weights
$\delta_j\pi_i$, and never sending has weights $p_i\pi_i$.

At records, $p_i$ lies between the adjacent emission scales defining its
cutoff. Before $\tau_i$, the current record factor dominates the remaining
factors and $p_i$, so $a_{i,j_k}\to1$. At and after $\tau_i$, $p_i$
dominates the record factors, so $a_{i,j_k}\to0$. For a type with no cutoff,
$p_i$ is negligible even at the final record. At every nonrecord, the
denominator contains the larger next-record factor, so $a_{ij}\to0$.
Thus the sequence converges to the rational choices just prescribed.

If $k_*$ exists, normalized never-send weights tend to $w$: the terms
$\varepsilon^{4k_*-2}w_i$ dominate every remaining term. Types with
$\tau_i=k_*$ and $w_i=0$ still have positive probabilities of smaller order.
If no cutoff exists, the same conclusion follows directly from
$p_i\pi_i=\varepsilon^{4r+2}(w_i+\varepsilon\pi_i)$.

### Consistency, endpoints and initialized law

Perturb the receiver lotteries to full support. At protected success the
posterior tends to the original source conditional prior. At any emitted
success or failure of positive probability, its type weights are respectively
$q_j\delta_j\pi_i$ or $(1-q_j)\delta_j\pi_i$, so its posterior is exactly
$\pi(\cdot\mid v)$. At never sending the posterior tends to $w$.
Chance-impossible success sites when $q_j=0$, and chance-impossible emitted
failure sites when $q_j=1$, are absent from the legal history tree; they impose
no Bayes or rationality obligation.

This one fully mixed player sequence therefore proves consistency of the
receiver replies and all sender decisions. Record choices maximize the send
and never-send payoffs. Nonrecord waiting reaches an at least equally reliable
record continuation or the optimal never-send outcome, so it is optimal too.

Each late send pays $V_{ij}\le S_i$; the inequality is strict when $q_j<1$.
At $q_j=1$ it pays exactly $S_i$. Never sending pays less than $S_i$ because
$D>R$. Hence protected opening is optimal against every complete timing
policy, even when some late slot is guaranteed. Choosing protected opening
preserves the source equilibrium's initialized joint outcome and payoff law.

This gives exact SE outcome preservation for the fixed finite disclosure phase,
with any finite number of different type-independent slot reliabilities.

## Correlated private receiver information with full joint support

The finite-opportunity theorem extends when the receiver also has a private
type, provided the joint prior has full support. This section states the
additional hypotheses and supplies the modified auxiliary game and Bayes
calculations. It is a paper theorem, like the preceding general phase result.

Let the sender type be $i\in I$ and the receiver type be $j\in J$, with
nonempty finite type sets and joint prior

$$
\pi_{ij}>0\quad\text{for every }(i,j)\in I\times J.
$$

Nature privately tells the sender $i$ and the receiver $j$. Put
$\pi_i=\sum_j\pi_{ij}$ and $\kappa_{ij}=\pi_{ij}/\pi_i$.
The immutable emitted value is $v(i)$. The receiver's success menu may be
$A_{v,j}$ and its failure menu $B_j$, all finite and nonempty. Sender and
receiver base payoffs are $u^S_{ij}(a),u^F_{ij}(b)$ and
$r^S_{ij}(a),r^F_{ij}(b)$ respectively. Uniformly assume

$$
0\le u^S_{ij}(a),u^F_{ij}(b)\le R,
\qquad D>R,\qquad c\ge0.
$$

Keep all preceding timing and observation hypotheses. In particular, each
slot's conditional inclusion probability $q_t\in[0,1]$ is independent of
**both** private types. The receiver makes no earlier decision or public
announcement, and the sender receives no additional signal about $j$ or
the inclusion kernel while waiting. Thus at every pre-emission sender
information set with type $i$, its belief about $j$ remains
$\kappa_{ij}$. Allowing a slot's reliability to depend on $j$ is not covered
by this extension.

### Source equilibrium and emitted-message replies

Every source Bayesian Nash equilibrium opens at every sender type. A
successful reply gives nonnegative payoff for every $j$, whereas lawful
withholding gives payoff at most $R-D<0$. Each sender type has positive
probability, so any positive withholding probability admits a strictly
profitable contingent unilateral deviation.

Consequently every reached receiver observation $(v,j)$ has posterior

$$
\pi(i\mid v,j)
=\frac{\mathbf 1_{v(i)=v}\pi_{ij}}
       {\sum_{\ell:v(\ell)=v}\pi_{\ell j}}.
$$

Fix the selected source equilibrium's success reply lotteries
$\beta^*_{v,j}$. Bayesian Nash optimality makes each a best response to this
posterior. Independently choose a failure reply $\beta^F_{v,j}$ maximizing
the receiver's failure payoff under the same posterior. Such a reply exists
by finiteness. It is used after an emitted packet fails; full public
observation still reveals $v$ there.

Define the sender's conditional expected success and emitted-failure base
payoffs by

$$
S_i=\sum_j\kappa_{ij}\sum_a\beta^*_{v(i),j}(a)u^S_{ij}(a),
\qquad
F_i=\sum_j\kappa_{ij}\sum_b\beta^F_{v(i),j}(b)u^F_{ij}(b).
$$

For a receiver no-emission reply family $\beta^0=(\beta^0_j)_{j\in J}$,
write

$$
W_i(\beta^0)=\sum_j\kappa_{ij}\sum_b\beta^0_j(b)u^F_{ij}(b).
$$

All three conditional base payoffs lie in $[0,R]$. Therefore

$$
V_{it}=q_tS_i+(1-q_t)(F_i-D-c),
\qquad
m_{it}(\beta^0)=W_i(\beta^0)-D-V_{it}
$$

obey precisely the same reliability ranking, cutoff comparisons and
protected-turn bounds as before. In particular,
$S_i-F_i+D+c\ge D-R+c>0$.

### The auxiliary receiver chooses a complete contingent reply plan

Retain the suffix-record slots $t_1<\cdots<t_r$. For each positive integer
$K$, give the selector actions $(i,z_1,\ldots,z_r)\in I\times\{0,1\}^r$.
The receiver's pure auxiliary actions are complete plans
$b=(b_j)_{j\in J}\in\prod_j B_j$. Define auxiliary payoffs by

$$
U_{\mathrm{selector}}(i,z,b)
=\sum_{k=1}^rK^{r-k}z_k
 \left(\sum_j\kappa_{ij}u^F_{ij}(b_j)-D-V_{i,t_k}\right),
$$

$$
U_{\mathrm{receiver}}(i,z,b)
=\sum_j\kappa_{ij}r^F_{ij}(b_j).
$$

This is an ordinary finite normal-form game. A receiver strategy mixed over
whole plans can correlate its prescriptions at different private types.
Only one private type is realized, so its coordinate marginals
$\beta^{0,K}_j$ give exactly the same expected payoffs against every
selector action. This follows from linearity of the displayed sums; no
independence between those unused coordinates is needed.

The selector optimizes its flags **after** averaging the receiver's
lottery and $j$ conditional on the chosen $i$. Its best payoff for type $i$
is therefore

$$
H_i^K=\sum_{k=1}^rK^{r-k}
             \bigl(m_{i,t_k}(\beta^{0,K})\bigr)^+,
$$

not an average of private-type-specific positive parts. Take auxiliary
Nash equilibria, project the selector strategy to a type law $w^K$, and
pass to a convergent subsequence
$(w^K,\beta^{0,K})\to(w,\beta^0)$.

At any projected law $w$, receiver type $j$ has probability

$$
P_j(w)=\sum_iw_i\kappa_{ij}
       \ge\min_i\kappa_{ij}>0.
$$

Receiver plan optimality thus implies that its reply at every $j$ is
optimal against weights $w_i\kappa_{ij}$. Indeed, replacing just one
coordinate of a plan is an available unilateral deviation, and its
payoff change is $P_j(w)$ times the conditional payoff change. The same
component optimality holds in the compact limit: the finite payoff
inequalities are continuous, and the denominator stays uniformly positive.
Consequently $\beta^0_j$ is a best response to the posterior

$$
\widehat w_i^{\,j}
=\frac{w_i\kappa_{ij}}{\sum_\ell w_\ell\kappa_{\ell j}}
$$

at a no-emission observation of receiver type $j$.

The selector support argument is unchanged. Let $k_*$ be the first record
whose limiting maximum $\max_i m_{i,t_{k_*}}(\beta^0)$ is positive.
Then $w$ is supported on the types with positive margin at that record,
and those types have first cutoff exactly $k_*$. For a type outside this
set, all earlier margins are strictly negative, its normalized
$k_*$-term tends to zero, and later terms vanish. A positive reference
type has normalized selector payoff bounded away from zero. If there is
no positive record maximum, all types send at each record. These are
exactly the support and cutoff facts used in the existing calibration.

### The same sender calibration is one consistent assessment

Use the previously specified emission factors $\delta_t$, residual
no-emission factors $p_i$, protected deferral $d_i$, and conditional send
probabilities $a_{it}$, now using the marginal prior $\pi_i$. The
calibration depends on $i$ only, because the sender does not know $j$.
It gives emission likelihood $\delta_t$ and no-emission likelihood $p_i$
conditional on $i$, with normalized weights $\pi_i p_i$ tending to $w_i$.

For each receiver type $j$, slot $t$ and emitted value $v$, success and
failure have joint type weights respectively

$$
\mathbf 1_{v(i)=v}\,\pi_{ij}\delta_tq_t,
\qquad
\mathbf 1_{v(i)=v}\,\pi_{ij}\delta_t(1-q_t).
$$

Whenever the corresponding chance branch exists, its conditional
posterior is exactly $\pi(i\mid v,j)$. Protected success has weights
$\mathbf 1_{v(i)=v}\pi_{ij}(1-d_i)$, so its posterior tends to the
source posterior. At no emission, conditional weights are $\pi_{ij}p_i$.
Writing these as $(\pi_i p_i)\kappa_{ij}$ shows that their posterior
tends to $\widehat w^{\,j}$. Its denominator is positive by full joint
support. Sender information sets retain exactly $\kappa_{ij}$ throughout
the same sequence, since the sender's own choices depend only on $i$ and
there is no earlier receiver action.

Perturb every receiver reply coordinate at every legal information set to
full support. Together with the calibrated fully mixed sender policy,
this is one global fully mixed sequence. It proves consistency of all
receiver and sender beliefs. At $q_t=0$ or $1$, chance-impossible
success or failure observations are omitted as before.

Receiver success replies are optimal by source Bayesian Nash optimality;
emitted-failure replies by the choice of $\beta^F$; no-emission replies by
the auxiliary plan argument. Sender continuation comparisons use the
conditional averages $S_i,F_i,W_i$ and therefore give the same optimal
record/nonrecord policy. Protected opening is optimal against every
whole timing continuation, since $V_{it}\le S_i$ and $W_i-D<S_i$.
Thus the limit assessment is an SE.

Initialized play always opens at the protected turn. For every type pair
and receiver action its law is

$$
\Pr(i,j,\mathrm{success},a)
=\pi_{ij}\beta^*_{v(i),j}(a),
$$

exactly the selected source Bayesian Nash outcome. It preserves the joint
law of both private types, value, publication result, receiver answer and
both realized payoffs. The target may choose different off-path source
failure replies and beliefs; no assessment embedding is claimed.

Full joint support is a substantive hypothesis of this extension. With
zeros in the prior, a limiting selector law can assign zero probability
to some receiver private types. Its auxiliary best-response conditions
then need not determine replies at those types, while smaller-order
global trembles can still reach their no-emission information sets. The
argument above does not resolve those additional posterior scales and
does not claim preservation for arbitrary correlated priors with zeros.

## Inclusion probability may depend on the disclosed value

The strongest version of the phase theorem allows $q_t(v)\in[0,1]$:
inclusion reliability may depend on the chosen slot and the emitted
immutable value. Conditional on that value it must be independent of the
remaining sender type and of the receiver's private type. Keep the full
joint support and other hypotheses of the private-information extension.
Values have no additional aliases or private representations affecting
inclusion. The value is disclosed on both possible terminal branches of
an actual emission, before the receiver answers.

The following modifies the selector and calibrates different value classes
on different emission scales while aligning their no-emission probabilities.
This is still a paper theorem; it is not a runtime adapter or a checked
general phase-equilibrium declaration.

### Value-specific records and one auxiliary selector

Keep the source replies, conditional averages $S_i,F_i,W_i$ and receiver
response plans from the previous section. Set

$$
V_{it}=q_t(v(i))S_i+(1-q_t(v(i)))(F_i-D-c),
\qquad m_{it}(b)=W_i(b)-D-V_{it}.
$$

For every value $v$ in the image of $v(i)$, form its strict suffix-record
slots

$$
t_{v,1}<\cdots<t_{v,r_v},
\qquad q_{t_{v,k}}(v)>q_\ell(v)
\text{ for every }\ell>t_{v,k}.
$$

The last slot is always a record. Equal reliabilities are handled by
waiting for their last occurrence. A type $i$ ranks transmissions by this
value-specific reliability list, and its record margins strictly increase.
Prescribe waiting at nonrecords, and sending at each record with
$m_{i,t_{v,k}}\le0$. Define its first strict cutoff $\tau_i$ as before,
with $\tau_i=r_v+1$ when no record margin is positive.

For each positive integer $K$, let the selector choose $i$ together with
one binary flag for each record of its value. Give it payoff

$$
\sum_{k=1}^{r_{v(i)}}K^{n-t_{v(i),k}}
  z_km_{i,t_{v(i),k}}(b).
$$

The receiver chooses a complete plan $b=(b_j)$ and gets
$\sum_j\kappa_{ij}r^F_{ij}(b_j)$. This finite game has a Nash equilibrium.
Project the selector strategy to a type law and take a compact subsequence
$(w^K,\beta^{0,K})\to(w,\beta^0)$. Receiver component optimality under
$w_i\kappa_{ij}$ follows exactly as in the preceding extension.

The record powers prioritize actual earlier slots. The selector's best
payoff at each type is

$$
H_i^K=\sum_{k=1}^{r_{v(i)}}K^{n-t_{v(i),k}}
 \bigl(m_{i,t_{v(i),k}}(\beta^{0,K})\bigr)^+.
$$

For each value separately, let $k_v$ be the first record with

$$
\max_{i:v(i)=v}m_{i,t_{v,k_v}}(\beta^0)>0,
$$

if one exists. Then, within that value, $w$ is supported on the types
having positive margin at this record. To prove this, compare an outside
type $i$ with a positive-margin type $i'$ of the **same value**. All earlier
margins of $i$ are strictly negative. After division by
$K^{n-t_{v,k_v}}$, its higher-priority terms are eventually zero, its
current term tends to zero, and its later terms vanish. The corresponding
normalized payoff of $i'$ is bounded away from zero. Hence $i$ eventually
has strictly lower selector payoff than an available action and cannot
retain selector weight.

The comparison is within a value class; it does not assume a single global
earliest positive cutoff across all values. A value class may have no
limiting selector mass at all. When $k_v$ exists, any type with positive
selector mass in that class has cutoff exactly $k_v$, and all its types
have $\tau_i\ge k_v$. When $k_v$ does not exist, every type in that class
has $\tau_i=r_v+1$ and sends at all its records.

### Aligning all no-emission posteriors

Let $M=4n+3$, and choose $\varepsilon\downarrow0$. For a value with an
earliest positive record $k_v$, set

$$
\delta_{t_{v,k}}(v)
=\varepsilon^{M+4(k-k_v)+2}.
$$

At each nonrecord slot, use the exponent of its next record plus one.
For types of that value, set

$$
p_i=\begin{cases}
\varepsilon^M(w_i/\pi_i+\varepsilon),&\tau_i=k_v,\\
\varepsilon^{M+4(\tau_i-k_v)},&\tau_i>k_v.
\end{cases}
$$

For a value with no positive record maximum, use instead

$$
\delta_{t_{v,k}}(v)
=\varepsilon^{M-4r_v-2+4k},
\qquad
p_i=\varepsilon^M(w_i/\pi_i+\varepsilon),
$$

again assigning a nonrecord the exponent of its next record plus one.
All exponents are positive since $r_v\le n$. Define

$$
d_i=\sum_{t=1}^n\delta_t(v(i))+p_i,
\qquad
a_{it}=\frac{\delta_t(v(i))}
 {\sum_{\ell=t}^n\delta_\ell(v(i))+p_i}.
$$

For sufficiently small $\varepsilon$, all probabilities are strictly
between zero and one, and $d_i\to0$. The same telescoping identity gives
conditional emission likelihood $\delta_t(v(i))$ and no-emission
likelihood $p_i$.

The probability orders give the prescribed continuation exactly in the
limit. A type at cutoff $k_v$ has $p_i$ of order $\varepsilon^M$ when
$w_i>0$, or $\varepsilon^{M+1}$ when $w_i=0$. Either dominates its cutoff
record factor $\varepsilon^{M+2}$, and is negligible compared with any
earlier record factor. For a later cutoff, its $p_i$ exponent lies two
units above the preceding record's exponent and two below its cutoff
record's exponent. A no-cutoff type sends at the final record as well.
For a value with no positive record maximum, the final record factor is
$\varepsilon^{M-2}$, which dominates $p_i$. Every nonrecord factor is
negligible relative to its following record, so it waits.

The local selector support property ensures the common global limit

$$
\frac{\pi_i p_i}{\varepsilon^M}\longrightarrow w_i
\quad\text{for every }i.
$$

For later-cutoff types, $w_i=0$ and the exponent of $p_i$ is at least
$M+4$. For earliest-cutoff and no-positive-cutoff types, the displayed
limit follows directly from their formula. Thus the differently scaled
value classes still produce a single no-emission type law $w$.

### Posterior cancellation and outcome preservation

At any emitted slot $t$ with disclosed value $v$ and receiver type $j$,
successful and unsuccessful joint weights are

$$
\mathbf 1_{v(i)=v}\pi_{ij}\delta_t(v)q_t(v),
\qquad
\mathbf 1_{v(i)=v}\pi_{ij}\delta_t(v)(1-q_t(v)).
$$

Within the observation $(v,j)$, both the emission factor and the actual
resolution probability cancel. Every chance-possible emitted posterior
is therefore exactly the original $\pi(i\mid v,j)$. At no emission,

$$
\frac{\pi_{ij}p_i}{\varepsilon^M}
\longrightarrow w_i\kappa_{ij},
$$

so the posterior is the same auxiliary conditional law
$\widehat w^{\,j}$. Full joint support keeps its denominator positive.
Protected posteriors converge to the source posteriors, and sender beliefs
remain $\kappa_{ij}$. Perturbing receiver replies to full support again
gives one common global consistency sequence.

At $q_t(v)=0$, there is no successful emitted history for that value and
slot; at $q_t(v)=1$, there is no failed emitted history. Neither imposes
an artificial belief obligation. Value-specific strict records, including
the last record of an all-zero or all-one reliability list, retain the
same ordering and calibration arguments. The case of no late slots is
the source comparison itself.

Receiver rationality follows from the three posterior calculations.
Sender rationality follows from its value-specific cutoff policy and the
same bounds $V_{it}\le S_i$ and $W_i-D<S_i$. Initialized play has joint
law $\pi_{ij}\beta^*_{v(i),j}(a)$ on protected success, exactly the chosen
source Bayesian Nash outcome, including both private types and realized
payoffs. This proves the payload-dependent reliability extension without
copying the source assessment's off-path failure behavior.

## What this does and does not establish

This is a close model of one immutable-value opening phase with lawful source
withholding and full public observation. It allows arbitrary receiver failure
preferences, finite drop charges and any finite number of late inclusion
probabilities, including zero and one.
The extensions allow correlated private receiver types under full joint
support and reliabilities depending on the disclosed value.
It does not require the direct last-send margin used
by the simpler uniform-tremble construction in
[the actual-runtime late-opening analysis](actual-runtime-late-opening-analysis.md).

It does not establish a general source-language compiler theorem. Strategic
binding-value choices, several interacting phases,
inclusion laws depending on the residual sender type beyond the disclosed
value or on the receiver's private type, extra runtime actions, aliases, retries,
correlated priors outside the full-joint-support extension, and genuinely
intermediate receiver decisions need
additional arguments. In particular, a large common failure forfeit cancels
when comparing two different values within the same late submission; this
proof fixes the immutable value before the phase.

The source comparison permits arbitrary private-type utilities, as ordinary
Bayesian game theory does. A public contract payout depending on a still-secret
type additionally requires an implementable verification or disclosure
mechanism. This theorem does not supply that mechanism.

The operational complete-observation result in
[ReactiveCompleteObservation](../Interaction/ReactiveCompleteObservation.lean)
establishes that every previously submitted foreign packet is visible at an
actual raw decision under complete pending observation. The checked recovery
example in
[CommittedResolutionRecovery](../Vegas/Examples/CommittedResolutionRecovery.lean)
establishes that the asynchronous contract permits accepted, audit-clean late
openings. Neither operational result identifies this finite game's histories,
menus, utilities or assessments with the complete actual Vegas runtime.

No existing asynchronous target, checklist box, semantics or runtime rule is
changed by this analysis.
