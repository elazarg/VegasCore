# Sequential equilibrium of commit–reveal programs on an asynchronous ledger

Status: mathematics, prepared for external review (2026-10-12). Neither
theorem is mechanized. Earlier drafts of each part had independent
adversarial reviews. This consolidated text had one further review, which
re-checked every arithmetic step; its corrections are incorporated. They
covered:

- unforgeable evidence;
- unopenable bindings of $b$;
- explicit builder parameters;
- bad bindings in Theorem 2;
- emitter-attached charges;
- notation.

## Summary

A *commit–reveal program* lets players commit to hidden values and later
reveal them. Its intended meaning is the **honest game**, in which every
commitment holds a valid value and every reveal opens. Compiling the program
to a ledger adds what the honest game lacks:

- players may stay silent or send late;
- a block builder schedules, includes and omits messages;
- pending messages can be seen by others before inclusion;
- a deposit and an audit punish misbehaviour.

We ask whether every sequential equilibrium (SE) of the honest game has an SE
of the compiled game with the same outcome law and no charges on its paths. The
deposit is fixed **before** the builder, so it cannot be scaled against the
builder's reliability.

- **Theorem 1 (negative).** The standard compiler fails. It charges a forfeit
  for each failed reveal and continues the program, and it charges every
  authentic packet that is never accepted. There is a program with three
  commitments, three reveals, and no setup, guard or randomness, such that the
  following holds for every forfeit and deposit above fixed thresholds and
  every $\varepsilon>0$. Some admissible builder, with late-omission
  probability below $\varepsilon$, has native SEs, and none of them preserves
  the honest SE.
- **Theorem 2 (positive).** A modified compiler succeeds, with two changes.
  - *Exclusion.* A player whose event fails gets a fixed payoff below every
    honest payoff of theirs, and the others continue.
  - *A free first packet.* A player's first well-formed packet for an event is
    never charged, whether or not it is included. Everything else the player
    sends is charged.

  For every program in the class, every forfeit, every deposit above the
  payoff spread and every admissible value-blind builder, every honest SE is
  preserved.

Section 5 explains what the proof of Theorem 2 needs from each change.
Section 6 lists what is open.

## 1. Model

### 1.0 Glossary

| Term | Meaning |
| --- | --- |
| honest game | The program's intended game: every commitment holds a guard-accepted value, every reveal opens (1.1). |
| native game | The finite game played on the ledger under a compiler and a builder (1.2–1.3). |
| gross / net payoff | Payoff before / after audit charges and forfeits. |
| settlement | The end of a run, when the audit's verdicts are computed and charges collected. |
| authentic packet | A packet signed by its emitter; every packet in the model is authentic. |
| handle, slot | A handle $(i,s)$ names slot $s$ of player $i$; a slot holds a value privately chosen by $i$ (openable) or nothing (unopenable). |
| own certificate | Evidence asserting exactly the opening's own (handle, value) pair. |
| Stage S | Events run one at a time in program order. |
| guard reads | The data a guard depends on (1.1). |
| missed binding | Expiry of a commit event without an accepted binding. |
| raw menu | Everything a player may emit at an activation (1.2). |
| late packet | A packet for an event sent after its owner's first activation while that event was ready. |
| protected turn | The owner's first activation while its event is ready. |
| record | In Theorem 1, Bob's information set at his first activation with his commitment ready. |
| real type | A type with positive probability in the honest SE. |

### 1.1 Programs and the honest game

A program is a finite straight-line sequence of events over players
$N=\{1,\dots,n\}$:

- `commit x : X by i`. Player $i$ binds a value in a finite domain $X$. The
  binding may be subject to a **guard**, a predicate on data available to $i$
  at the commit: public data, earlier publications, and $i$'s own commitments.
  The guard is evaluated at the reveal that completes its reads, which is one
  of $i$'s own.
- `reveal x by i`. Player $i$ publishes the value bound to $x$. Its
  *publication result* is $\mathsf{ok}(v)$ or $\mathsf{fail}$.
- `sample y ~ λ`. The runtime draws a public value from a law $\lambda$ that
  may depend on earlier public data.
- `return u`. The utilities $u_i$ are functions of the publication results and
  samples only.

Programs start from the **empty context**: no initial private inputs, no
initial commitments and no prior. Every commitment is revealed.

The **honest game** $\Gamma^H$ is the finite extensive-form game in which:

- each commit is a move of its owner, who chooses a value its guard accepts;
- each reveal publishes;
- samples are chance moves.

A player's information set in $\Gamma^H$ is determined by the public results
and their own commitments. Write
$[\underline u_i,\overline u_i]$ for the range of $u_i$ over terminal
histories of $\Gamma^H$.

### 1.2 The ledger runtime

**Clock and events.** Time is a public clock in **slots**. Events run one at a
time in program order (*Stage S*). An owned event $e$ becomes **ready** at the
clock $r_e$ when its predecessor completes. It completes in one of two ways:

- when the contract accepts a packet for it;
- at **expiry**, as a failure, when the clock reaches $r_e+d_e$.

**Packets.** When the builder activates player $i$, $i$ may emit at most one
packet, or stay silent. A packet has three parts:

1. a *call*: a binding for an event (with a handle of $i$), an opening (a
   handle and a value), or a malformed call;
2. optional *evidence*: a fact "handle $h$ holds value $v$";
3. a *readiness token* for the call's event, which the runtime attaches only
   while that event is ready.

**Evidence is unforgeable.** A player can emit the evidence "$h$ holds $v$"
only if it is true: either $h$ is its own handle and its slot holds $v$, or it
copies evidence from a packet it has seen. Anyone who sees the packet learns
that fact.

Every packet gets a fresh identifier $(i,s)$, where $s$ is the **emitter**
$i$'s next serial. A packet is always its emitter's. If $i$ relays $j$'s
content, the result is $i$'s packet.

Raw menus are finite but otherwise unrestricted. They include silence,
malformed calls, copies, extra identifiers, evidence attachments, and packets
for events that are not ready. They also include **unopenable bindings**: a
binding whose slot holds no value is accepted like any binding, and its reveal
can only fail.

**Contract (independent of the compiler).** An included packet gets a public
receipt marked accepted or rejected. The contract accepts the first included
packet that comes from $e$'s owner, addresses the currently ready event $e$,
and has one of these calls:

- a binding for $e$ with a fresh handle of the owner, which records the
  binding;
- an opening of the bound handle whose value matches the bound value. It
  records $\mathsf{ok}(v)$ if the guards accept $v$ and $\mathsf{fail}$
  otherwise.

An opening whose value does not match is not accepted.

**Mempool and leaks.** An emitted packet is *pending* until it is included.
At each activation of $i$, the builder may *show* $i$ some pending packets of
other players. Showing a packet reveals its identifier, call and evidence.

**Builder.** The builder is a public chance process that chooses activations,
inclusions, leaks, clock advances and expiries. Its law is fixed and known to
the players; its realization is not. Each owned event $e$ has parameters
$\mathit{delay}_e$ and $\mathit{bound}_e$. The following hold on every legal
history, including histories with deviations:

- **Opportunity.** Once the clock exceeds $r_e+\mathit{delay}_e$, the owner has
  been activated since $e$ became ready.
- **Protected inclusion.** Suppose the owner emits a packet for $e$ while $e$
  is ready, at clock $s$, and emits no other identifier for $e$. Then by the
  time the clock exceeds $s+\mathit{bound}_e$, the packet has a receipt,
  unless $e$ has completed. Other emitters' packets do not void this.
- **Timeliness.** $\mathit{delay}_e+\mathit{bound}_e<d_e$.
- **Completion.** Every run ends with every event completed.

Protected inclusion is vacuous for a packet sent at clock $s$ with
$s+\mathit{bound}_e\ge r_e+d_e$, because expiry completes $e$ first. Such
late packets may be omitted.

**Observation.** Player $i$ observes the following:

- the public clock;
- every included packet in full (identifier, call, evidence), with its
  receipt and inclusion clock;
- every completion, publication result, failure and expiry;
- its own activations and emissions;
- at each of its activations, the packets shown to it, with the clock of their
  first sighting. Showing an already known packet again adds nothing.

Players do not observe others' activations or emissions except through leaks
and inclusions.

**Builder properties used below.** The builder is:

- **value-blind** if its laws read only public data, packet identifiers and
  emitters, and the value of the opening being delivered. In particular they
  read no other unopened value, and no evidence that a packet carries about
  one;
- **author-only** if leaks depend only on the observer and on the emitters of
  pending packets, not on their content;
- **blind to late packets in its inclusion law** if the following holds at
  every history holding a pending late packet $x$. The builder's inclusion law
  is a mixture of two components: including $x$, and the inclusion law at the
  corresponding history in which $x$ was never sent.

### 1.3 Compilers

A compiler fixes two things: the payoff consequences of failures, and an
**audit**. The audit runs at settlement and charges player $i$ the deposit
$K_i$, at most once, if any packet *emitted by $i$* is charged. Charges are
burned.

**Compiler $C_0$ (standard).**

- *Forfeit pass.* Each failed reveal or missed binding of player $j$ costs $j$
  a forfeit $D$. The program continues with $\mathsf{fail}$ in place of the
  result. Player $j$ keeps playing, and utilities read the failure results.
- *Settled audit.* A packet that names no event is charged. Otherwise the
  verdict compares it with the settled record:
  - a packet for an event that has not settled is permitted, but by
    Completion every event settles before the verdict;
  - a packet for a settled event is permitted only if the contract accepted it
    with correct content. A binding must carry no evidence and use the
    emitter's next slot (counted from its bindings settled before the event).
    An opening must carry exactly its own certificate, and its guards must
    accept.

  Every other packet is charged. This includes packets never included and
  every copy beyond the accepted one. An unopenable binding on the next slot
  is permitted, so it is not charged. Collection is sure.

**Compiler $C_1$ (exclusion with a free first packet).**

- *Exclusion.* An owned event of $j$ *fails* if it is a missed binding, a
  failed or unopenable opening, a guard rejection, or an expiry. Player $j$ is
  then **excluded**:
  - each later event of $j$ completes as a failure without becoming ready for
    $j$;
  - $j$'s gross payoff is a fixed $a_j<\underline u_j$;
  - every other player $i$ continues and receives $u_i$ on the public results,
    with the excluded players' results failed.

  The forfeit $\underline u_j-a_j>0$ may be arbitrarily small.
- *Count audit.* A packet is **well-formed** for event $e$ if three things
  hold:
  - its emitter owns $e$;
  - it carries a valid token for $e$;
  - its call is correct for $e$. For a reveal, that means the opening of the
    bound value with exactly its own certificate. For a commit, it means a
    binding with a fresh handle of the emitter and no evidence.

  The emitter's **first** packet for $e$ is the one with the lowest serial
  among its packets addressed to $e$. It is free if it is well-formed, whether
  or not it is ever included. Every other packet is charged:
  - every later packet for $e$, even an identical copy, and even if $e$ failed;
  - every packet that is not well-formed, which includes every disclosure of
    an unopened value;
  - every packet whose emitter does not own its event.

  At every history at which a charged packet is emitted, the charge is
  collected with conditional probability at least $\alpha>0$. Collection reads
  no unopened value. The verdict reads only signed content, tokens, serials
  and the final record, never send times.
- *Deposit.* $\alpha K_i>\operatorname{sp}_i$, where $\operatorname{sp}_i$ is
  the spread of $i$'s gross payoff over all compiled terminal histories.

### 1.4 Preservation, sequential equilibrium, quantifier order

A native assessment **preserves** an honest SE if it induces the same joint
law of public results and realized net payoffs, and charges and forfeits
nobody on its paths.

Sequential equilibrium is in the sense of Kreps and Wilson. It requires
sequential rationality at every information set, and **consistency**:
beliefs are limits of Bayes beliefs along one sequence of fully mixed
behaviour profiles. Only the players' strategies are perturbed. Chance moves,
meaning samples and every draw of the builder, keep their fixed laws
throughout.

The quantifier order is **deposit-first**:

1. the program and utilities;
2. the compiler's parameters (forfeits, $\alpha$, deposits);
3. an honest SE;
4. the builder;
5. the native SE, which may depend on everything before it.

### 1.5 Standing assumptions

1. Players interact only through the runtime's packets. There is no
   off-ledger communication.
2. Domains are finite. The native game is finite, with finite menus and a
   horizon of at most $\mathcal T$ moves.
3. Players are finitely many.
4. The audit observes every emitted packet, including packets sent privately
   to the builder, with the collection bounds of 1.3. How dead packets are
   reported (for example, by watchers submitting signed packets) is outside
   the model.

## 2. Theorem 1: the standard compiler does not preserve SE

### 2.1 The program

Players are Alice and Bob. Fix $p\in(0,1)$, $R>0$, $\gamma=1$ and $\beta=1/2$.
Bob's answers are $\mathrm{Safe}$, $\mathrm{Lab}_k$ for $k\in\{0,1,2\}$ (a
label guess), and $\mathrm{Bit}_g$ for $g\in\{0,1\}$ (a Boolean guess).

```text
commit  b : Bool        by Alice
commit  t : (ℓ, h)      by Alice      -- ℓ ∈ {0,1,2}, h ∈ Bool
reveal  b               by Alice
commit  c : Answer      by Bob        -- Safe, Lab0, Lab1, Lab2, Bit0, Bit1
reveal  c               by Bob
reveal  t               by Alice
return  (utilities below)
```

The public outcome is $(o_b,o_c,o_t)$, the three publication results. Gross
utilities, before forfeits:

- If $o_c$ failed, both players get $0$.
- **Success branch**, $o_b=\mathsf{ok}(b)$:

  | Bob's answer | Bob, $o_t=\mathsf{ok}(\ell,h)$ | Bob, $o_t$ failed | Alice, $\ell\in\{0,1\}$ | Alice, $\ell=2$ |
  | --- | --- | --- | --- | --- |
  | Safe | $2/5$ | $2/5$ | $R/2$ | $R/2$ |
  | $\mathrm{Lab}_k$ | $\mathbf 1_{k=\ell}+\gamma\,\mathbf 1_{h\ne b}$ | $1$ | $R$ | $0$ |
  | $\mathrm{Bit}_g$ | $0$ | $0$ | $0$ | $0$ |

  Alice with $\ell\in\{0,1\}$ gets $R$ for **any** label guess, correct or
  not. She only wants Bob to leave Safe.
- **Failure branch**, $o_b$ failed:

  | Bob's answer | Bob, $o_t=\mathsf{ok}(\ell,h)$ | Bob, $o_t$ failed | Alice, $\ell=0$ | Alice, $\ell=1$ | Alice, $\ell=2$ |
  | --- | --- | --- | --- | --- | --- |
  | $\mathrm{Bit}_1$ | $\mathbf 1_{h=1}$ | $\beta$ | $R$ | $0$ | $0$ |
  | $\mathrm{Bit}_0$ | $\mathbf 1_{h=0}$ | $\beta$ | $0$ | $R$ | $0$ |
  | Safe, $\mathrm{Lab}_k$ | $0$ | $0$ | $0$ | $0$ | $0$ |

- Alice's gross is $0$ whenever $o_t$ failed.

Alice's payoff ranges over $[0,R]$ and Bob's over $[0,1+\gamma]$. The
thresholds are
$$
D>\max\{R,\,1+\gamma\},\qquad K_A>R/2,\qquad K_B>1+\gamma .
$$

The role of each piece:

- $\ell$ stands in for a private type. Alice's preferences over Bob's answer
  depend on a value she committed to and Bob has not yet seen.
- $h$ keeps a failed opening of $b$ payoff-relevant. On the honest path
  $h=b$, so an omitted opening of $b$ that Bob saw still predicts $h$.
- The remaining terms close escape routes (2.6).

### 2.2 The honest SE

Alice commits $b$ with $\Pr(b=1)=p$, and independently commits a uniform
$\ell$ with $h=b$. She opens $b$; Bob commits to Safe and opens it; Alice
opens $t$.

- **Bob is optimal.** He sees the published $b$, so his posterior has $\ell$
  uniform and $h=b$. A label guess is worth $1/3<2/5$, and a Boolean guess is
  worth $0$.
- **Alice is optimal.** Every choice earns her $R/2$.
- **Consistency** is trivial, because every information set is reached.

The law to preserve is the following:

- $\Pr(b=1)=p$, with $\ell$ uniform and independent, and $h=b$;
- every publication succeeds, and Bob publishes Safe;
- Alice nets $R/2$ and Bob nets $2/5$.

### 2.3 The builder

**Parameters.** All clocks are slots, and a receipt is due once the clock
*exceeds* the sending clock plus $\mathit{bound}$.

| Event | $\mathit{delay}$ | $\mathit{bound}$ | $d$ |
| --- | --- | --- | --- |
| commit $b$, commit $t$ | $0$ | $0$ | $1$ |
| reveal $b$ (ready at clock $0$) | $0$ | $2$ | $3$ |
| commit $c$ | $1$ | $0$ | $2$ |
| reveal $c$, reveal $t$ | $0$ | $0$ | $1$ |

Timeliness holds for every event. Each event other than the reveal of $b$
gets one owner activation when it becomes ready, and that owner's packet from
the activation is included at once (a *receipt*). So protected inclusion holds
with $\mathit{bound}=0$.

Commit $c$ becomes ready at clock $2$ when the lottery includes the opening of
$b$. Bob is activated at clock $3$, which is why $\mathit{delay}_c=1$.

For the reveal of $b$, the protected packet is sent at clock $0$ and included
at once. A packet sent at clock $1$ or $2$ has $s+2\ge3=r+d$, so protected
inclusion is vacuous for it: it is a *late packet* and may be omitted.

**Schedule.**

| Clock | Operations |
| --- | --- |
| 0 | Alice: activation and receipt (commit $b$); activation and receipt (commit $t$); activation and receipt (reveal $b$, her protected turn). |
| 1 | Alice's first late activation. Her emission is *not* included at clock 1. Then Bob's activation and leak sample, and a receipt for Bob's own emission, if any. |
| 2 | Alice's second late activation, then the inclusion lottery. |
| 3 | Expire the reveal of $b$ if unresolved. Bob: activation and receipt (commit $c$). Bob: activation and receipt (reveal $c$), if his binding completed. Alice: activation and receipt (reveal $t$), if Bob's publication completed. |
| later | Each unresolved event expires at its deadline; when an event becomes ready, one owner activation and receipt; then settlement. |

Bob's only activation between clock 1 and his commitment is at clock 3, in
both the success and the failure branch.

**Leaks.** At each activation, each pending packet of the other player is
shown independently with probability $1/2$. Packets not shown stay pending.

**Lottery.** Let $m$ be the number of pending identifiers at clock 2. Only
Alice's late packets can be pending, since Bob's are included on receipt. Each
pending identifier is included with probability $w/(1+mw)$, and none is
included with probability $1/(1+mw)$. A sole late opening is therefore
included with probability $q=w/(1+w)$. Let $\delta=1-q$.

This builder satisfies every condition of 1.2. It is value-blind and
author-only. It is blind to late packets in its inclusion law: conditioned on
not including a given packet, the lottery is the lottery on the remaining
$m-1$ identifiers. Its leaks are not covered by that property.

**Records.** Fix $b$. Bob's records after Alice sends a **certified** opening
of $b$ (value $b$ with its own certificate) late are:

| Record | Meaning | After a clock-1 send | After a clock-2 send |
| --- | --- | --- | --- |
| $E(b)$ | included; seen at clock 1 | $q/2$ | $0$ |
| $U(b)$ | included; not seen at clock 1 | $q/2$ | $q$ |
| $F_1(b)$ | omitted; seen at clock 1 | $\delta/2$ | $0$ |
| $F_3(b)$ | omitted; first seen at clock 3 | $\delta/4$ | $\delta/2$ |
| $F_u$ | omitted; never seen | $\delta/4$ | $\delta/2$ |

The included opening shows its value and serial but no emission time. $F_u$
does not reveal $b$, so it is one information set for both values. Seeing a
known packet again is not a new observation, so $F_1(b)$ is a single
information set.

An opening call without its own certificate is never accepted under $C_0$ and
is charged. It produces records other than those above.

### 2.4 Statement

**Theorem 1.** Fix the program and utilities of 2.1, any $D,K_A,K_B$ above
the thresholds, and the honest SE of 2.2. For every $\varepsilon>0$, choose
$0<\delta<\varepsilon$ with
$$
\delta\,(D+K_A+R/2)<\min\{D-R,\ K_A-R/2\}
\qquad\text{and}\qquad
\delta<\frac{R}{3R+4(D+K_A)},
\tag{δ}
$$
and set $w=(1-\delta)/\delta$. Under compiler $C_0$ and the builder of 2.3,
the native game is finite with perfect recall, so it has SEs. **None of them
preserves the honest SE.**

Example numbers:

- $R=1$, $D=3$, $K_A=2$, $K_B=3$ and $w=24$, so $\delta=0.04$.
- Both conditions hold: $0.22<1.5$ and $0.04<1/23$.
- The deviation of Step 4 earns at least $0.75\cdot0.96-0.04\cdot5=0.52>0.5$.

The first condition is conservative: Step 1 only needs $D-R/2$ in place of
$D-R$.

### 2.5 Proof

Assume a native SE preserves the honest SE.

*Alice's type* is her pair of bindings. Each of $b$ and $t$ is either openable
or unopenable ($\bot$): $b\in\{0,1,\bot\}$, and $t$ is either some
$(\ell,h)$ or $\bot$. A type is *real* if it has positive honest probability,
that is $b\in\{0,1\}$ and $t=(\ell,b)$. Real types are on the native path.

By unforgeable evidence, only a type with bound value $b$ can emit a
certified opening of $b$. A type with $b=\bot$ has no certified opening and
reaches, among the records of 2.3, only $F_u$.

**Step 0. Late turns are off path.** The preserved law has every publication
succeed and no charges. A late opening is omitted with positive probability,
and any other first message at the protected turn is charged or changes the
record. So every type opens $b$ at clock 0 on path, and every record of 2.3 is
reached with probability zero. Sequential rationality must still hold there,
with consistent beliefs.

**Step 1. Clean late play is one opening.** Take a late history at which
Alice is uncharged, and a type whose $b$ and $t$ are both openable. Compare a
single certified opening with every alternative:

- One opening earns at least $qR/2-\delta(D+K_A)$ for labels $0,1$, and
  $-\delta(D+K_A)$ for label $2$.
- Any continuation with a charged packet earns at most $R-K_A$ (resp.
  $R/2-K_A$). Charged packets include a duplicate, an extra identifier, a
  malformed call, and any evidence other than an opening's own certificate.
  The settled audit never permits an opening of $b$ that carries evidence
  about $t$, nor a binding that carries evidence.
- Permanent silence earns at most $R-D$ (resp. $-D$).

By (δ), one opening is strictly best: either send at clock 1 and stay quiet,
or send at clock 2.

A type with openable $b$ and $t=\bot$ earns gross $0$ in every continuation
and pays $D$ at the reveal of $t$. One opening costs it $\delta(D+K_A)<D$ in
expectation, so it also sends exactly one opening, at a time it is indifferent
about.

The remaining choices are fixed as follows:

- Alice opens an openable $t$ at its reveal.
- Bob never sends charged packets ($K_B$ exceeds his range).
- Bob binds a valid answer and opens it ($D$ and $K_B$ exceed his range).

Pass to a subsequence along which the quantities below and all beliefs
converge. Write:

- $\omega_{\tau,n}$ for the probability that type $\tau$ is drawn and stays
  silent at the protected turn;
- $\theta_{\tau,n}$ for the conditional probability, given that, that Alice's
  first emission afterwards is the certified opening of $b$, sent at clock 1.

For a type $\tau$ with openable $b$ and for each record $r$ other than $F_u$,
$$
\Pr_n(r,\tau)=\omega_{\tau,n}\bigl(\kappa_r(\theta_{\tau,n})+o(1)\bigr),
$$
where $\kappa_r$ is the entry of the table and $o(1)$ is uniform over types.
The reason is that any other history reaching such a record needs an extra
emission:

- an extra emission *before* the opening changes the opening's serial, which
  gives a different record;
- an extra emission *after* it is a tremble against the strict preference
  above.

$F_u$ is also reached by permanent silence (an $o(1)$ term) and by every
$b=\bot$ type with weight of order $\omega_{\tau,n}$. The proof uses $F_u$
only through the fact that it is a single information set, common to both
values of $b$.

**Step 2. Two ties.** Bob's posteriors at $E(b)$, $U(b)$, $F_1(b)$ and
$F_3(b)$ are over types whose bound value is $b$.

*Tie 1: $E(b)$ and $F_1(b)$ carry the same belief, exactly.* Fix any history
up to the lottery in which Bob saw the certified opening at clock 1, including
histories with further traffic.

- Whatever $m$ is, the lottery includes the opening, or nothing, at odds
  $w:1=q:\delta$.
- Including any other packet produces a public receipt, and hence a different
  record. Inclusion removes only the included identifier, so the other pending
  packets meet the same fate in both branches.
- Bob already knows the opening, and he has exactly one activation before his
  commitment in either branch.

So $\Pr_n(E(b),\tau):\Pr_n(F_1(b),\tau)=q:\delta$ for every type and every
$n$, and Bob's posteriors at $E(b)$ and $F_1(b)$ coincide.

*Tie 2: the cross identity.* Let $\mathcal G_u,\mathcal G_v$ be sets of types
with bound value $b$, with $\theta_{\tau,n}\to1$ on $\mathcal G_u$ and
$\theta_{\tau,n}\to0$ on $\mathcal G_v$. Then
$$
\mu_{E(b)}(\mathcal G_v)\,\mu_{U(b)}(\mathcal G_u)\to0 .
$$

*Proof.* Write $W_X=\sum_{\tau\in X}\omega_{\tau,n}$. The table gives
$\kappa_E(\theta)=\theta q/2$ and $\kappa_U(\theta)=(1-\theta/2)q$. So
$$
\frac{\mu_E(\mathcal G_v)}{\mu_E(\mathcal G_u)}\le o(1)\cdot\frac{W_v}{W_u},
\qquad
\frac{\mu_U(\mathcal G_u)}{\mu_U(\mathcal G_v)}\le\Bigl(\tfrac12+o(1)\Bigr)\frac{W_u}{W_v}.
$$
Multiply the two bounds: the weights cancel, and the product of the ratios
tends to zero. Since $\mu_E(\mathcal G_u)$ and $\mu_U(\mathcal G_v)$ are at
most $1$, the claim follows.

**Step 3. Timing preferences.** Fix $b$. Let:

- $\psi_E,\psi_U$ be Bob's probabilities of Safe at $E(b)$ and $U(b)$;
- $y_1$, $y_3$ and $z$ be his probabilities of guessing $1$ at $F_1(b)$,
  $F_3(b)$ and $F_u$.

At success records a Boolean guess is strictly worse than Safe. At failure
records Bob always makes a Boolean guess, which earns at least
$\min\{1/2,\beta\}>0$.

For a type with openable $t$ and label $\ell$, the payoff of sending at
clock 1 minus sending at clock 2 is, for $\ell=0,1,2$,
$$
(\Delta_{\mathrm{succ}}+\Delta_{\mathrm{fail}},\
 \Delta_{\mathrm{succ}}-\Delta_{\mathrm{fail}},\
 -\Delta_{\mathrm{succ}}),
\qquad
\Delta_{\mathrm{succ}}=\frac{qR}{4}(\psi_U-\psi_E),\qquad
\Delta_{\mathrm{fail}}=\frac{\delta R}{4}(2y_1-y_3-z).
$$
If $\Delta_{\mathrm{succ}}\ne0$ or $\Delta_{\mathrm{fail}}\ne0$, then some
label group $\mathcal G_u$ (all openable-$t$ types with that label and this
$b$) has $\theta\to1$, and another group $\mathcal G_v$ has $\theta\to0$.

**Step 4. Contradiction.**

*Case A: for some $b$, Bob plays Safe with probability zero at $E(b)$ or at
$U(b)$.* Let the real type $(b,(0,b))$ deviate: stay silent at clock 0, send
the certified opening at clock 1, then stay quiet.

- On inclusion she reaches $E(b)$ or $U(b)$, each with probability $1/2$. She
  earns $R$ at the record where Bob avoids Safe, and at least $R/2$ at the
  other.
- On omission she pays $D+K_A$ and gets a nonnegative gross payoff.

So she earns at least $3qR/4-\delta(D+K_A)>R/2$ by (δ), which beats her
equilibrium payoff. Contradiction.

*Case B: for both $b$, Safe has positive probability at $E(b)$ and $U(b)$.*
Then Safe is optimal at all four records. At a success record, write:

- $\mu_\bot$ for the mass on $t=\bot$;
- $\nu$ for the mass on $h\ne b$;
- $\mu_k$ for the mass on openable $t$ with $\ell=k$.

A label guess $\mathrm{Lab}_k$ is worth $\mu_\bot+\mu_k+\gamma\nu$, and
Safe-optimality makes this at most $2/5$. Summing over $k$ gives
$2\mu_\bot+3\gamma\nu\le1/5$. Then every label has
$\mu_k\ge1/5+\mu_\bot+2\gamma\nu\ge1/5$.

- At $E(b)$: $\nu\le1/15$ and $\mu_\bot\le1/10$, so the mass on $h=b$ exceeds
  $1/2$. By Tie 1 the same holds at $F_1(b)$. Guessing $b$ there is worth
  $\Pr(h=b)+\beta\mu_\bot$, against $\Pr(h\ne b)+\beta\mu_\bot$ for the other
  guess. So $y_1(b)=b$.
- Then $\Delta_{\mathrm{fail}}(0)=0$ forces $z=0$, and
  $\Delta_{\mathrm{fail}}(1)=0$ forces $z=1$. So
  $\Delta_{\mathrm{fail}}(b)\ne0$ for some $b$, and Step 3 gives groups
  $\mathcal G_u,\mathcal G_v$ for it.
- Tie 2 gives $\mu_{E(b)}(\mathcal G_v)\,\mu_{U(b)}(\mathcal G_u)\to0$. But
  Safe-optimality gives both factors at least $1/5$. Contradiction. $\square$

### 2.6 Why each payoff term is needed

| Term | Escape it closes |
| --- | --- |
| $h$ revealed last, $h=b$ on path | Without it, a failed opening's content reaches no payoff, so $\Delta_{\mathrm{fail}}=0$. |
| $\gamma\,\mathbf 1_{h\ne b}$ | Bob could split his belief at $F_1(b)$ between $h=b$ and $h\ne b$ and be indifferent. Tie 1 moves that split to $E(b)$, where it rules out Safe. |
| A label guess against a failed $t$ pays $1$ | Bob could attribute deviations to $t=\bot$. This payoff caps that mass at $1/10$. |
| $\beta>0$ | Bob always makes a Boolean guess after an omission, so labels $0$ and $1$ mirror each other ($\pm\Delta_{\mathrm{fail}}$). |
| $\ell$ committed and revealed last | Supplies Alice's types without setup. |

## 3. Theorem 2: exclusion with a free first packet preserves SE

**Theorem 2.** Assume the deposit-first order with compiler $C_1$, and fix:

- any program of 1.1;
- any payoffs $a_j<\underline u_j$;
- any $\alpha>0$ and deposits with $\alpha K_i>\operatorname{sp}_i$;
- any honest SE $(\sigma^H,\mu^H)$;
- any value-blind builder of 1.2. Blindness to late packets is not assumed.

Then some native SE preserves $(\sigma^H,\mu^H)$.

### 3.1 Construction

**Regions.** A *charged action* emits a charged packet. Information sets fall
into three regions:

- **forced**: sets containing a history with no charged action and no
  exclusion;
- **excluded**: sets after an exclusion. Failures are public, so these are
  disjoint from the forced sets;
- **free**: all other sets.

**Projection.** A binding is *bad* if it is unopenable, wrongly typed or
rejected by its guard. A history with no exclusion, no charged action and no
bad binding determines an honest history. Let $I$ be a forced set at which
player $i$ has an honest choice (a binding value, or an opening), and suppose
$i$ holds no bad binding. Then $I$ projects to an honest information set
$\Pi(I)$. The set $I$ refines $\Pi(I)$ by operational data: activations,
receipts, serials, handle slots, leaks and timing.

Now suppose $i$ itself holds a bad binding. Project as if each of $i$'s bad
bindings held a fixed honest value. Every uncharged action of $i$ there is
optimal, because its gross payoff is $a_i$ in every continuation of
$\sigma^*$. $\sigma^*$ plays the projected honest action, with the exceptions
listed below.

**The profile $\sigma^*$ on the forced region.**

- *First activation while the event is ready.* The owner sends its free
  packet:
  - for a binding, the value is drawn from $\sigma^H$ at $\Pi(I)$, with a
    fresh handle of the owner, chosen independently of the value, and no
    evidence;
  - for a reveal, the packet is the certified opening of the bound value.
- *Late delivery.* If the owner has sent nothing for an unresolved event, it
  follows a fixed policy $\varphi^*$.
  - At each activation, $\varphi^*$ decides whether to send the free packet
    now, so as to maximize the conditional probability that the event
    succeeds.
  - $\varphi^*$, including its tie-breaking rule, is a function of the public
    data, the owner's operational view, and the value being delivered only.
  - A late binding draws its value from $\sigma^H$ at $\Pi(I)$.
- *Bad bindings.*
  - At the reveal of an unopenable or wrongly typed binding, no well-formed
    packet exists, so the owner stays silent.
  - A guard-violating binding may be opened, since both choices exclude the
    owner.
- *Otherwise*, silence. In particular, nothing further is sent after the free
  packet.

**Trembles.** Take the honest tremble sequence $\sigma^H_n\to\sigma^H$, with
beliefs $\mu^H_n\to\mu^H$. Let $c$ bound the menu sizes, and let $\rho_n$ be
the smallest positive probability that $\sigma^H_n$ or Nature gives to any
action. At each forced set the perturbed profile is built as follows:

- The prescribed component gets mass $1-\eta_n-\eta_n^2-\eta_n^M$, and inside
  it honest choices follow $\sigma^H_n$ at the projection. So an honest action
  $x$ has probability $\sigma^H_n(x)(1-\eta_n-\eta_n^2-\eta_n^M)$, which is the
  same rescaling at every set.
- *Timing deviations* get probability $\eta_n$. That is silence at a first
  activation, or the send time that $\varphi^*$ does not choose; each forced
  set has at most one.
- The other native-only uncharged actions share $\eta_n^2$, uniformly. These
  are values outside the honest set, bad bindings and other handle slots.
  Where a set has no such action, the $\eta_n^2$ goes to the prescribed
  component.
- Charged actions share $\eta_n^M$.

The sequences satisfy $\eta_n=o(\rho_n)$, $M>2\mathcal T$, and
$\eta_n^{M-2\mathcal T}=o\bigl((\rho_n/c)^{\mathcal T}\bigr)$. So a history
with a charged action has weight at most $\eta_n^M$. That is negligible
against any history without one, whose weight is at least
$(\eta_n^2/c)^{\mathcal T}\rho_n^{\mathcal T}$.

All native-only factors that can differ across types are therefore of the
form $1+o(1)$, uniformly.

**Excluded and free regions.** For each $n$, take an equilibrium of the
agent-form game in which forced sets play the perturbed $\sigma^*$, and all
other sets choose freely with minimum probability $\eta_n^M$ on every action.
It exists by Kakutani's theorem. Pass to a convergent subsequence of profiles
and Bayes beliefs.

### 3.2 Proof

**Lemma A (forced beliefs are honest).** Two claims hold.

1. At every forced set, the limit belief puts zero weight on histories with a
   charged action or with another player's bad binding.
2. At a forced set $I$ that projects and at which no reveal is pending, the
   belief over $\Pi(I)$ is $\mu^H(\Pi(I))$.

At forced sets with a pending reveal, only the first claim is asserted;
Lemma B covers them.

*Proof.*

- *Charged actions* are negligible by the choice of $M$.
- *A bad binding* carries a factor of at most $\eta_n^2$, against at least
  $\rho_n$ for the honest binding with the same public record. The two
  operational records have the same law, since well-formed bindings carry no
  evidence and are opaque.
- *Every other history* factors as
  $\Pr_n(h)=\Pr^H_n(\Pi(h))\,N_n(h)\,(1+o(1))$. Here $\Pr^H_n$ is the honest
  probability. $N_n$ collects the builder's draws, the leaks, the collection
  and the timing trembles.
  - By value-blindness and by the construction of the trembles and of
    $\varphi^*$, the law of the operational record given the honest history
    depends only on public data and opened values.
  - No packet in such a history carries evidence about an unopened value:
    well-formed bindings carry none, and every other packet is charged.
  - When no reveal is pending, every opened value is public at $I$.

  Hence $\sum_{h\in I,\Pi(h)=x}N_n(h)$ is the same for every $x\in\Pi(I)$,
  and the posterior equals $\mu^H_n(\Pi(I))(1+o(1))\to\mu^H(\Pi(I))$.
  $\square$

**Lemma B (delivery is one-dimensional).** Fix a forced history at which
player $j$'s event is unresolved and $j$ has sent nothing for it. Consider a
type of $j$ without a bad binding, and a policy $s$ that sends at most the
free packet. Its payoff is
$$
P_s\,V+(1-P_s)\,a_j ,
$$
where $P_s$ is the policy's success probability and $V\ge\underline u_j$ is
$j$'s honest continuation value. So every type ranks these policies by $P_s$
alone.

*Proof.*

- **Failure.** The free packet is never charged. Failure gives exactly $a_j$,
  whatever the route and whatever happens afterwards.
- **Success.** $\sigma^*$ plays the projection of $\sigma^H$, with honest
  beliefs by Lemma A, so the continuation is honest and worth
  $V\ge\underline u_j>a_j$.
- **Success probability.** $P_s$ depends only on the builder and the policy.
  These may read the value being opened. That value is public after success
  and payoff-irrelevant to $j$ after failure. They read no other unopened
  value. So $\arg\max P_s$ is the same set for every type that delivers the
  same value, and the fixed rule $\varphi^*$ picks the same element for all
  of them.
- **Late bindings.** For a late binding, $P_s$ does not depend on the value,
  so the honest value choice stays optimal.
- **Pending reveal.** While a reveal is pending, other players' only uncharged
  action is silence, so their beliefs do not yet matter.
- **Handle slot.** The handle slot is uncharged cheap talk. Its trembles do
  not depend on the value, so by Lemma A observers ignore it. $\square$

**Lemma C (charged one-shot deviations do not pay).** At a forced set of
player $j$, every one-shot deviation to a charged action is strictly worse
than $\sigma^*$, whatever anyone does afterwards.

*Proof.*

- At a forced set, $j$ is uncharged. Charges attach to the emitter, so a
  charge needs $j$'s own charged packet, which $j$ would recall. And the set
  contains a charge-free history.
- The deviation yields at most $\max\text{gross}_j-\alpha K_j$.
- $\sigma^*$ never charges $j$, so it yields at least $\min\text{gross}_j$.
- The difference is at most $\operatorname{sp}_j-\alpha K_j<0$.
- A further packet for an event is charged on every path where it is sent,
  whether the event succeeds or fails, so multi-packet delivery is covered.
  $\square$

The statement is one-shot on purpose. Because the charge is capped once per
player, removing one charged action from a strategy that takes another later
need not save anything.

**Sequential rationality, forced region.** By the one-shot deviation principle
for consistent assessments in finite games (Hendon, Jacobsen and Sloth 1996),
it suffices to check single deviations.

From a forced set, with probability one under the beliefs (Lemma A), play
leaves the forced region in only two ways: the deviator's own charged action,
or the deviator's own exclusion. Nobody can make another player fail.
Protected inclusion holds on every history, and other emitters' packets do not
void it. Nobody can make another player charged either, since charges attach
to the emitter.

- **Honest choice at a first activation.** The beliefs are $\mu^H(\Pi(I))$ by
  Lemma A.
  - The free packet sent at once is included before the deadline, by
    opportunity, protected inclusion and timeliness.
  - It is accepted: a binding has a fresh owned handle, and an opening is the
    certified value. Honest values pass their guards.
  - So the honest continuation follows, and $\sigma^H$ is optimal among honest
    actions.

  The alternatives are no better:
  - late delivery yields $P_sV+(1-P_s)a_j\le V$ (Lemma B);
  - a bad binding leads to exclusion at $a_j<V$;
  - charged actions are worse (Lemma C).
- **Late delivery.** $\varphi^*$ is optimal by Lemma B, and Lemma C rules out
  charged actions.
- **Own bad binding.** Every uncharged action yields $a_j$. Silence is the
  only uncharged action at the reveal of an unopenable or wrongly typed
  binding.
- **After the free packet, and for non-owners.** Every alternative to silence
  is charged, and Lemma C applies.

**Sequential rationality, excluded and free regions.** This follows from the
limit argument for perturbed agent-form equilibria: Selten perfection in agent
form implies sequential optimality. The forced agents are fixed throughout. An
excluded player's gross payoff is constant and its packets are charged, so
silence is optimal for it.

**Consistency.** The assessment is the limit of Bayes beliefs along the fully
mixed profiles of the construction.

**Preservation.** Every owner sends its free packet at its first activation,
and it is accepted before the deadline. So nobody is excluded or charged on
path. Bindings follow $\sigma^H$, samples follow their law, and the builder's
randomness affects no public result. So the joint law of public results and
net payoffs is the honest one. $\square$

## 4. How the two theorems relate

Theorem 1's mechanism has three links:

1. Alice's payoff after a failed reveal depends on Bob's later answer.
2. Bob's answer reads what he saw of the omitted opening.
3. So the timing of a late send is a type-dependent choice. The beliefs this
   forces at the success records make a protected-turn deviation profitable.

Exclusion cuts the first link. $C_0$ also charges a dead first packet. That
makes the cost of a late send depend on the route, which would recreate a
type-dependent choice even after exclusion (Section 5).

## 5. Why the proof needs each change

These are obstructions to the proof of Theorem 2, not counterexamples.
Theorem 1 is a counterexample only for $C_0$ as a whole, which combines the
first two features below.

- **Exclusion with a fixed payoff.** Without it, link 1 of Section 4 holds.
  The failing player's payoff then depends on both the type and the route, and
  Lemma B fails. What the proof needs is narrower than ending the game. After
  failure, the failing player's payoff must depend neither on its type nor on
  the route. Given a fixed payoff:
  - the excluded player's later actions need not be removed, since they affect
    only the excluded region;
  - the other players may continue under any payoff on public results,
    including the program's own failure semantics;
  - ending the game, with constants for everyone, is the special case.
- **The free first packet.** Suppose instead that a dead first packet costs an
  expected $\alpha K(1-q)$. Relative to silence, a late send is then worth
  $$
  q\,(V-a_j)-\alpha K(1-q).
  $$
  The builder is chosen after the deposit, so it can pick $q$ with
  $\alpha K(1-q)/q$ strictly between the continuation values $V_1-a_j$ and
  $V_2-a_j$ of two types. Then the high-value type sends late and the
  low-value type stays silent, and Lemma A fails.

  Charging *further* packets on every path is harmless (Lemma C).
- **Charging every disclosure.** Take Battle of the Sexes, in which both
  players commit and then both reveal. If an evidence-bearing binding were
  free, a player could verifiably commit first, and the other would best
  respond to it. Under $C_0$, the settled audit already forbids such packets;
  $C_1$ keeps that.
- **Deposit $\alpha K_i>\operatorname{sp}_i$.** Lemma C needs it, and it does
  not depend on the builder.
- **Value-blind builder.** Lemma A needs it. The runtime's scheduler view
  contains pending payloads, so this is a real restriction.

## 6. Open questions and limitations

- **Isolating the causes.** $C_0$ has two features: failure branches
  continue, and dead packets are charged. Whether either feature alone already
  breaks preservation is not settled.
- **Keeping the program utility after exclusion.** A plausible but unchecked
  variant gives the excluded player its program utility on public results,
  with its own results failed, minus a forfeit $D_j>\sup u_j-\underline u_j$.
  The supremum is over histories in which $j$'s results failed. A proof would
  combine four ingredients:
  - the excluded player takes no further action, which the contract enforces;
  - with an empty context, unopened values are conditionally independent
    given the public history, so the excluded player's leaked values are
    uninformative and payoff-irrelevant;
  - the continuation lifts an SE of the residual honest game, chosen from
    public results only, by induction on the number of active players;
  - the excluded player's continuation value is then route-independent and
    below $\underline u_j$.
- **Concurrency.** Both theorems are for Stage S, one event at a time.
- **Infinite domains**, for example sealed-bid auctions over $\mathbb N$, are
  outside both theorems.
- **Builder-first order.** If the deposit may depend on the builder's law,
  Theorem 2 applies unchanged. Whether $C_0$ preserves SE in that order is not
  settled.
- **Mechanization.** Neither theorem is machine-checked. The finite games,
  information sets and runtime conditions are taken from a Lean formalization,
  and Appendix A maps the names.

## Appendix A. Correspondence to the Lean development

| Note | Lean |
| --- | --- |
| Opportunity, protected inclusion, completion | `Vegas.EventGraphRuntime.AsyncContract` |
| Timeliness | `Vegas.EventGraphRuntime.AsyncTimely` |
| Packet (call, evidence, token) | `Vegas.EventGraphRuntime.WitnessedPacket` |
| Unforgeable evidence | `Vegas.EventGraphRuntime.EvidenceRequest.resolve` |
| Unopenable binding (prepared slot without a value) | `Vegas.EventGraphRuntime.Submission.candidateAfter` |
| Opening's own certificate | `Vegas.EventGraphRuntime.certifiedOpening` |
| Settled audit of $C_0$ | `Vegas.EventGraphRuntime.SettledRecord.Permits` |
| Per-emitter serials | `Interaction.MessageNetwork.submit` |
| Event address of a packet | `Vegas.EventGraphRuntime.Payload.event?` |

A mechanization must also check the following, beyond the statements above:

- the projection of raw information sets;
- value-blindness of the scheduler, the leak rule and collection;
- that expiry cannot fire before clock $r_e+\mathit{delay}_e+\mathit{bound}_e+1$;
- that failures and expiries are in every player's view;
- that the builder of Theorem 1 satisfies the contract with the parameters of
  2.3, and that its inclusion law is blind to late packets;
- the agent-form fixed point.
