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

## What this does and does not establish

This is a close model of one immutable-value opening phase with lawful source
withholding and full public observation. It allows arbitrary receiver failure
preferences, finite drop charges and any finite number of late inclusion
probabilities, including zero and one. It does not require the direct last-send margin used
by the simpler uniform-tremble construction in
[the actual-runtime late-opening analysis](actual-runtime-late-opening-analysis.md).

It does not establish a general source-language compiler theorem. Strategic
binding-value choices, several interacting phases,
hidden-type-dependent inclusion laws, extra runtime actions, aliases, retries, private
receiver information, and genuinely intermediate receiver decisions need
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
