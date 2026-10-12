# Sequential equilibrium of commit–reveal programs on an asynchronous ledger

Status: mathematics, prepared for external review (2026-10-12). Neither
theorem is mechanized. Earlier drafts of each part had independent
adversarial reviews; their corrections are incorporated. This consolidated
text has not itself been reviewed.

## Summary

A *commit–reveal program* lets players commit to hidden values and later
reveal them. Its intended meaning is the **honest game**: every commitment
holds a valid value and every reveal opens. Compiling the program to a ledger
adds what the honest game lacks:

- players may stay silent or send late;
- a block builder schedules, includes and omits messages;
- pending messages can be seen by others before they are included;
- a deposit and an audit punish misbehaviour.

We ask whether every sequential equilibrium (SE) of the honest game has an SE
of the compiled game with the same outcome law, and no charges on its paths.
The deposit is fixed **before** the builder, so it cannot be scaled against
the builder's reliability.

- **Theorem 1 (negative).** The standard compiler fails. That compiler charges
  a forfeit for each failed reveal and continues the program, and it charges
  every authentic packet that is never accepted. There is a program with three
  commitments, three reveals and no setup, guard or randomness such that,
  for every forfeit and deposit above fixed thresholds and every
  $\varepsilon>0$, some admissible builder with late-omission probability
  below $\varepsilon$ has native SEs, but none of them preserves the honest SE.
- **Theorem 2 (positive).** A modified compiler succeeds, with two changes.
  - **Exclusion:** a player whose event fails gets a fixed payoff below every
    honest payoff of theirs, and the others continue.
  - **The free first packet:** a player's first well-formed packet for an
    event is never charged, included or not; everything else the player sends
    is charged.

  For every program in the class, every forfeit, every deposit above the
  payoff spread, and every admissible value-blind builder, every honest SE is
  preserved.

Section 5 shows why each change is needed, and Section 6 lists what is open.

## 1. Model

### 1.1 Programs and the honest game

A program is a finite straight-line sequence of events over players
$N=\{1,\dots,n\}$:

- `commit x : T by i`: player $i$ binds a value of the finite type $T$,
  optionally subject to a **guard**, a predicate on data available to $i$ at
  the commit. That data is the public data, the earlier publications, and $i$'s
  own commitments. The guard is evaluated at the reveal that completes its
  reads, which is one of $i$'s own reveals.
- `reveal x by i`: player $i$ publishes the value bound to $x$. Its
  *publication result* is either $\mathsf{ok}(v)$ or $\mathsf{fail}$.
- `sample y ~ λ`: the runtime draws a public value from a fixed law $\lambda$,
  which may depend on earlier public data.
- `return u`: the utilities $u_i$, which are functions of the publication
  results and samples only.

Programs start from the **empty context**: no initial private inputs, no
initial commitments and no prior. Every commitment is revealed.

The **honest game** $G^H$ is the finite extensive-form game in which each
commit is a move of its owner, who chooses a value its guard accepts; each
reveal publishes; and samples are chance moves. A player knows the public
results and their own commitments. Write $[L_i,U_i]$ for the range of $u_i$
over terminal histories of $G^H$.

### 1.2 The ledger runtime

Time is a public clock in **slots**. Events run one at a time in program order
(*Stage S*). An owned event $e$ becomes **ready** when its predecessor
completes. It completes when the contract accepts a packet for it, or at
**expiry**, $d_e$ slots after readiness, as a failure.

- **Packets.** When the builder activates player $i$, $i$ may emit at most one
  packet, or stay silent. A packet has three parts:
  - a *call*: a binding for an event (with a handle naming a slot of $i$), an
    opening (a handle and a value), or a malformed call;
  - optional *evidence*: a checkable fact "handle $h$ holds value $v$";
  - a *readiness token* for the call's event, which the runtime attaches only
    while that event is ready.

  Every packet gets a fresh identifier $(i,s)$, where $s$ is $i$'s next
  serial. Raw menus are finite but otherwise unrestricted: silence, malformed
  calls, copies, extra identifiers, evidence attachments, packets for events
  that are not ready, and **unopenable bindings**. An unopenable binding is a
  binding whose handle holds no openable value. It is accepted like any
  binding, and its reveal can only fail.
- **Contract.** An included packet gets a public receipt. The contract
  *accepts* the first included packet that is well-formed for the currently
  ready event and authored by its owner:
  - acceptance of a binding records the binding;
  - acceptance of an opening records $\mathsf{ok}(v)$ if $v$ matches the binding
    and passes the guards, and $\mathsf{fail}$ if the guard rejects it.
- **Mempool and leaks.** An emitted packet is *pending* until it is included.
  At each activation of $i$, the builder may show $i$ some pending packets of
  other players. Player $i$ remembers what it was shown.
- **Builder.** A public chance process that chooses activations, inclusions,
  leaks, clock advances and expiries. Its law is fixed and known to the
  players; its realization is not. It satisfies the following on every legal
  history, including histories with deviations:
  - **Opportunity:** the owner of a ready event $e$ is activated within
    $\mathit{delay}_e$ slots.
  - **Protected inclusion:** suppose the owner emits a packet for $e$ while
    $e$ is ready at clock $s$, and emits no other identifier for $e$. Then that
    packet is included by clock $s+\mathit{bound}_e$, unless $e$ has completed.
    Other authors' packets do not void this.
  - **Timeliness:** $\mathit{delay}_e+\mathit{bound}_e<d_e$.
  - **Completion:** every run ends with every event completed.

  A packet sent later than its owner's first activation (a *late* packet) has
  no such guarantee if it is sent within $\mathit{bound}_e$ of the deadline.
  It may then be omitted.
- **Observation.** Player $i$ observes the ledger (included packets, receipts,
  publication results and failures, the clock), its own activations and
  emissions, and its leaks.
- **Builder properties used below.** The builder is:
  - **value-blind** if its laws read public data, packet identifiers and
    authors, and the value of the opening being delivered, but no other
    unopened value and no evidence a packet carries about one;
  - **author-only** if leaks depend on the observer and on the authors of
    pending packets, not on their content;
  - **blind to late packets** (mixture form) if, at any history holding a
    pending late packet, its law is a mixture of including that packet and
    its law in the world where the packet was never sent.

### 1.3 Compilers

A compiler fixes the payoff consequences of failures and an **audit**. The
audit sees every emitted packet, included or not, and at settlement charges a
player $K_i$ (at most once) if any of their packets is *charged*. Charges are
burned.

**Compiler $C_0$ (standard).**
- *Forfeit pass.* Each failed reveal or missed binding of player $j$ costs $j$
  a forfeit $D$. The program continues with $\mathsf{fail}$ in place of the
  result, $j$ keeps playing, and utilities read the failure results.
- *Settled audit.* A packet for an event is permitted only if the contract
  accepted it with correct content:
  - a binding carries no evidence and uses the author's next handle;
  - an opening carries exactly its own certificate, and its guards accept.

  Every other authentic packet is charged, including a packet that is never
  included and every copy beyond the accepted one. Collection is sure.

**Compiler $C_1$ (exclusion with a free first packet).**
- *Exclusion.* If an owned event of $j$ fails (a missed binding, a failed or
  unopenable opening, a guard rejection, or expiry), $j$ is **excluded**:
  - each later event of $j$ completes as a failure without becoming ready for
    $j$;
  - $j$'s gross payoff is a fixed $a_j<L_j$;
  - every other player $i$ continues, and receives $u_i$ on the public
    results, with the excluded players' results failed.

  The forfeit $L_j-a_j>0$ may be arbitrarily small.
- *Count audit.* A packet is **well-formed** for event $e$ if:
  - its author owns $e$;
  - it carries a valid token for $e$;
  - its call is correct for $e$: for a reveal, the opening of the bound value
    with exactly its own certificate; for a commit, a binding with a fresh
    handle the author owns and no evidence.

  The author's **first** packet for $e$ (lowest serial among its packets
  addressed to $e$) is free if well-formed, whether or not it is ever
  included. Every other authentic packet is charged:
  - every later packet for $e$, even an identical copy, and even if $e$
    failed;
  - every packet that is not well-formed, which includes every disclosure of
    an unopened value;
  - every packet of a non-owner.

  At every history at which a charged packet is emitted, the charge is
  collected with conditional probability at least $\alpha>0$. Collection reads
  no unopened value.

  The verdict reads only signed content, tokens, serials and the final record,
  never send times.
- *Deposit.* $\alpha K_i>\Delta_i$, where $\Delta_i$ is the spread of $i$'s
  gross payoff over all compiled terminal histories.

### 1.4 Preservation and quantifier order

A native assessment **preserves** an honest SE if two things hold:
- it induces the same joint law of public results and realized net payoffs;
- it charges and forfeits nobody on its paths.

Sequential equilibrium is in the sense of Kreps and Wilson: sequential
rationality at every information set, and beliefs that are limits of Bayes
beliefs along one sequence of fully mixed profiles, with Nature and the
builder fixed.

The quantifier order is **deposit-first**:
1. the program and utilities;
2. the compiler's parameters (forfeits, $\alpha$, deposits);
3. an honest SE;
4. the builder;
5. the native SE, which may depend on everything before it.

### 1.5 Standing assumptions

1. Players interact only through the runtime's packets. There is no
   off-ledger communication.
2. Payload types are finite, and the native game is finite: finite menus and
   a finite horizon $T$.
3. Players are finitely many.

## 2. Theorem 1: the standard compiler does not preserve SE

### 2.1 The program

There are two players, Alice and Bob. Fix $p\in(0,1)$, $R>0$, $\gamma=1$ and
$\beta=1/2$.

```text
commit  b : Bool        by Alice
commit  t : (ℓ, h)      by Alice      -- ℓ ∈ {0,1,2}, h ∈ Bool
reveal  b               by Alice
commit  c : Answer      by Bob        -- Safe, L0, L1, L2, G0, G1
reveal  c               by Bob
reveal  t               by Alice
return  (utilities below)
```

The public outcome is $(p_b,p_c,p_t)$. Gross utilities, before forfeits:

- If $p_c$ failed: both players get $0$.
- **Success branch**, $p_b=\mathsf{ok}(b)$:

  | Bob's answer | Bob, $p_t=\mathsf{ok}(\ell,h)$ | Bob, $p_t$ failed | Alice, $\ell\in\{0,1\}$ | Alice, $\ell=2$ |
  | --- | --- | --- | --- | --- |
  | Safe | $2/5$ | $2/5$ | $R/2$ | $R/2$ |
  | $L_k$ | $\mathbf 1_{k=\ell}+\gamma\,\mathbf 1_{h\ne b}$ | $1$ | $R$ | $0$ |
  | $G_g$ | $0$ | $0$ | $0$ | $0$ |

- **Failure branch**, $p_b$ failed:

  | Bob's answer | Bob, $p_t=\mathsf{ok}(\ell,h)$ | Bob, $p_t$ failed | Alice, $\ell=0$ | Alice, $\ell=1$ | Alice, $\ell=2$ |
  | --- | --- | --- | --- | --- | --- |
  | $G_1$ | $\mathbf 1_{h=1}$ | $\beta$ | $R$ | $0$ | $0$ |
  | $G_0$ | $\mathbf 1_{h=0}$ | $\beta$ | $0$ | $R$ | $0$ |
  | Safe, $L_k$ | $0$ | $0$ | $0$ | $0$ | $0$ |

- Alice's gross is $0$ whenever $p_t$ failed.

Alice's payoff ranges over $[0,R]$ and Bob's over $[0,1+\gamma]$. The
thresholds are
$$
D>\max\{R,\,1+\gamma\},\qquad K_A>R/2,\qquad K_B>1+\gamma .
$$

The role of each piece:
- $\ell$ stands in for a private type: Alice's preferences over Bob's answer
  depend on a value she committed to and Bob has not yet seen.
- $h$ keeps a failed opening of $b$ payoff-relevant: on the honest path
  $h=b$, so an omitted opening of $b$ that Bob saw still predicts $h$.
- The remaining terms close escape routes (Section 2.6).

### 2.2 The honest SE

Alice commits $b\sim\mathrm{Bernoulli}(p)$ and, independently, $\ell$ uniform
with $h=b$. She opens $b$. Bob commits to Safe and opens it. Alice opens $t$.

- **Bob is optimal.** His information is the published $b$, and his
  posterior has $\ell$ uniform and $h=b$. A label guess is worth $1/3<2/5$, and
  a Boolean guess $0$.
- **Alice is optimal.** Every choice of hers earns $R/2$.
- **Consistency** is trivial, since every information set is reached.

The law to preserve:
- $b\sim\mathrm{Bernoulli}(p)$, with $\ell$ uniform and independent, and
  $h=b$;
- every publication succeeds, and Bob publishes Safe;
- Alice nets $R/2$ and Bob nets $2/5$.

### 2.3 The builder

**Schedule.** For each event, the owner is activated when it becomes ready,
and its latest message is included immediately (a *receipt*). The exception is
the opening of $b$, which uses the late-turn schedule below.

| Clock | Operations |
| --- | --- |
| 0 | Alice: activation and receipt (commit $b$), activation and receipt (commit $t$), activation and receipt (reveal $b$; her *protected* turn). |
| 1 | Alice's first late activation; Bob activation, leak sample, receipt. |
| 2 | Alice's second late activation; inclusion lottery. |
| 3 | Expire the opening of $b$ if unresolved; Bob activation and receipt (commit $c$); Bob activation and receipt (reveal $c$) if his binding completed; Alice activation and receipt (reveal $t$) if Bob's publication completed. |
| later | Expiry of each unresolved event at its deadline, with one owner activation and receipt when an event becomes ready; settle. |

Bob's only activation between clock 1 and his commitment is at clock 3, in the
success and failure branches alike.

The other components of the builder:
- **Leaks.** At each activation, each pending packet of the other player is
  shown independently with probability $1/2$. Omitted packets stay pending.
- **Lottery.** With $m$ pending identifiers, each is included with probability
  $w/(1+mw)$, and none with probability $1/(1+mw)$. A sole late opening is
  included with probability $q=w/(1+w)$. Let $\delta=1-q$.
- **Records.** An included late opening shows its value and serial, but no
  emission time. Receipts and failures are public.

This builder satisfies every condition of Section 1.2. It is value-blind,
author-only, and blind to late packets in the mixture form.

**Timing channel.** If Alice skips her protected turn and sends at clock 1,
Bob sees the opening at clock 1 with probability $1/2$. A clock-2 send cannot
be seen before the lottery. An omitted opening is seen at clock 3 with
probability $1/2$. For a fixed $b$, Bob's records after a single late opening
are:

| Record | Meaning | After a clock-1 send | After a clock-2 send |
| --- | --- | --- | --- |
| $E(b)$ | included, seen at clock 1 | $q/2$ | $0$ |
| $U(b)$ | included, not seen at clock 1 | $q/2$ | $q$ |
| $F_1(b)$ | omitted, seen at clock 1 | $\delta/2$ | $0$ |
| $F_3(b)$ | omitted, first seen at clock 3 | $\delta/4$ | $\delta/2$ |
| $F_u$ | omitted, never seen | $\delta/4$ | $\delta/2$ |

$F_u$ does not reveal $b$, so it is one information set for both values.
Seeing a known packet again is not a new observation, so $F_1(b)$ is a single
information set.

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
- $R=1$, $D=3$, $K_A=2$, $K_B=3$ and $w=24$, so $\delta=0.04$;
- both conditions hold: $0.22<1.5$ and $0.04<1/23$;
- the deviation of Step 4 earns at least $0.75\cdot0.96-0.04\cdot5=0.52>0.5$.

### 2.5 Proof

Assume a native SE preserves the honest SE.
- *Alice's type* means her two bindings: $b$, and $t$, which is either an
  openable $(\ell,h)$ or unopenable ($\bot$).
- A type is *real* if it has positive honest probability, that is
  $t=(\ell,b)$. Real types are on the native path.

**Step 0. Late turns are off path.** The preserved law has every publication
succeed and no charges. A late opening is omitted with positive probability.
Any other first message at the protected turn is charged or changes the
record. So every type opens $b$ at clock 0 on path, and every record of 2.3 is
reached with probability zero. Sequential rationality must still hold there,
with consistent beliefs.

**Step 1. Clean late play is one opening.** Take a late history at which
Alice has not been charged. Compare one proper opening with every alternative,
for a type whose $t$ is openable:
- one opening earns at least $qR/2-\delta(D+K_A)$ (labels $0,1$), or
  $-\delta(D+K_A)$ (label $2$);
- any continuation with a charged packet earns at most $R-K_A$ (resp.
  $R/2-K_A$). Charged packets include a duplicate, an extra identifier, a
  malformed call, and any evidence other than an opening's own certificate.
  Under the settled audit, an opening of $b$ carrying evidence about $t$, or a
  binding carrying evidence, is never permitted;
- permanent silence earns at most $R-D$ (resp. $-D$).

By (δ), one opening is strictly best: either send at clock 1 and stay quiet,
or send at clock 2.

A $\bot$ type earns gross $0$ in every continuation and pays $D$ at the reveal
of $t$. One opening costs it $\delta(D+K_A)<D$ in expectation, so it too sends
exactly one opening, at a time it is indifferent about.

The remaining choices:
- Alice opens an openable $t$ at its reveal.
- Bob never sends charged packets, since $K_B$ exceeds his range.
- Bob binds a valid answer and opens it, since $D$ and $K_B$ exceed his range.

So records arise from one opening sent at clock 1 or clock 2. In the common
tremble sequence, write:
- $\omega_{\tau,n}$ for the probability that type $\tau$ is drawn and stays
  silent at the protected turn;
- $a_{\tau,n}$ for the probability that her first late emission is the
  opening, sent at clock 1. This is a total over all identifiers, with or
  without further traffic afterwards.

Any other history reaching a record of 2.3 needs an extra emission. If it
comes before the opening, it changes the opening's serial, which gives a
different record. If it comes after, it is a tremble against a strict
preference. Hence, for each record $r$,
$$
\Pr_n(r,\tau)=\omega_{\tau,n}\bigl(\kappa_r(a_{\tau,n})+o(1)\bigr),
$$
where $\kappa_r$ is the entry of the table and $o(1)$ is uniform over types.

**Step 2. Two ties.**

*Tie 1: $E(b)$ and $F_1(b)$ carry the same belief, exactly.*
- Fix any history up to the lottery in which Bob saw the opening at clock 1,
  including histories with further traffic.
- Whatever the number $m$ of pending identifiers, the lottery includes the
  opening, or nothing, at odds $w:1=q:\delta$.
- Including any other packet produces a public receipt, and hence a different
  record. Inclusion removes only the included identifier, so the other
  pending packets meet the same fate in both branches.
- Bob already knows the opening, and he has exactly one activation before his
  commitment in both branches.

So $\Pr_n(E(b),\tau):\Pr_n(F_1(b),\tau)=q:\delta$ for every type and every
$n$, and Bob's posteriors at the two records coincide.

*Tie 2: the cross identity.* Let $G_u,G_v$ be sets of types with the same $b$,
with $a_{\tau,n}\to1$ on $G_u$ and $a_{\tau,n}\to0$ on $G_v$. Then
$$
\mu_{E(b)}(G_v)\,\mu_{U(b)}(G_u)\to0 .
$$
Write $W_X=\sum_{\tau\in X}\omega_{\tau,n}$. We have $\kappa_E(a)=aq/2$ and
$\kappa_U(a)=(1-a/2)q$, so
$$
\frac{\mu_E(G_v)}{\mu_E(G_u)}\le o(1)\cdot\frac{W_v}{W_u}
\qquad\text{and}\qquad
\frac{\mu_U(G_u)}{\mu_U(G_v)}\le\Bigl(\tfrac12+o(1)\Bigr)\frac{W_u}{W_v}.
$$
Multiplying, the weights cancel and the product tends to zero. The bound
follows because $\mu_E(G_u),\mu_U(G_v)\le1$.

**Step 3. Timing preferences.** Fix $b$. Let:
- $\sigma_E,\sigma_U$ be Bob's probabilities of Safe at $E(b)$ and $U(b)$;
- $y_1,y_3,x$ be his probabilities of guessing $1$ at $F_1(b)$, $F_3(b)$ and
  $F_u$.

At success records a Boolean guess is strictly worse than Safe. At failure
records Bob always makes a Boolean guess, which earns at least
$\min\{1/2,\beta\}>0$.

For a type with openable $t$ and label $\ell$, the payoff of sending at
clock 1 minus clock 2 is, for $\ell=0,1,2$,
$$
(S+F,\ S-F,\ -S),\qquad
S=\frac{qR}{4}(\sigma_U-\sigma_E),\qquad
F=\frac{\delta R}{4}(2y_1-y_3-x).
$$
If $S\ne0$ or $F\ne0$, some label group $G_u$ has $a\to1$ and another group
$G_v$ has $a\to0$.

**Step 4. Contradiction.**

*Case A: for some $b$, Bob plays Safe with probability zero at $E(b)$ or at
$U(b)$.* Let the real type $(b,(0,b))$ deviate: stay silent at clock 0, send
at clock 1, then stay quiet.
- On inclusion she reaches $E(b)$ or $U(b)$, with probability $1/2$ each. She
  earns $R$ at the record without Safe, and at least $R/2$ at the other.
- On omission she pays $D+K_A$ and gets a nonnegative gross payoff.

So she earns at least $3qR/4-\delta(D+K_A)>R/2$ by (δ). That beats her
equilibrium payoff, a contradiction.

*Case B: for both $b$, Safe has positive probability at $E(b)$ and $U(b)$.*
Then Safe is optimal at all four records. At a success record, write:
- $\mu_\bot$ for the mass on unopenable $t$;
- $m$ for the mass on $h\ne b$;
- $\mu_k$ for the mass on openable $t$ with $\ell=k$.

A label guess $L_k$ is worth $\mu_\bot+\mu_k+\gamma m\le2/5$. Summing over $k$
gives $2\mu_\bot+3\gamma m\le1/5$, and then $\mu_k\ge1/5$ for every label.

- At $E(b)$: $m\le1/15$ and $\mu_\bot\le1/10$, so the mass on $h=b$ exceeds
  $1/2$. By Tie 1 the same holds at $F_1(b)$, so Bob strictly guesses $b$
  there: $y_1(b)=b$.
- Then $F(0)=0$ forces $x=0$, and $F(1)=0$ forces $x=1$. So $F(b)\ne0$ for
  some $b$, and by Step 3 there are groups $G_u$ and $G_v$ as above.
- Tie 2 gives $\mu_{E(b)}(G_v)\,\mu_{U(b)}(G_u)\to0$. But Safe-optimality gives
  both factors at least $1/5$. Contradiction. $\square$

### 2.6 Why each payoff term is needed

| Term | Escape it closes |
| --- | --- |
| $h$ revealed last, $h=b$ on path | Without it, a failed opening's content reaches no payoff, so $F=0$. |
| $\gamma\,\mathbf 1_{h\ne b}$ | Bob could split his belief at $F_1(b)$ between $h=b$ and $h\ne b$, and be indifferent. Tie 1 moves that split to $E(b)$, where it rules out Safe. |
| A label guess against a failed $t$ pays $1$ | Bob could attribute deviations to unopenable $t$. The payoff caps that mass at $1/10$. |
| $\beta>0$ | Bob always makes a Boolean guess after an omission, so labels $0$ and $1$ mirror each other ($\pm F$). |
| $\ell$ committed and revealed last | Supplies Alice's types without any setup. |

## 3. Theorem 2: exclusion with a free first packet preserves SE

**Theorem 2.** Take the deposit-first order, with compiler $C_1$:
- any program of 1.1;
- any payoffs $a_j<L_j$;
- any $\alpha>0$ and deposits with $\alpha K_i>\Delta_i$;
- any honest SE $(\sigma^H,\mu^H)$;
- any builder of 1.2 that is value-blind. Blindness to late packets is not
  assumed.

Then there is a native SE that preserves $(\sigma^H,\mu^H)$.

### 3.1 Construction

**Regions.** A *charged action* emits a charged packet. Information sets fall
into three regions:
- **forced:** sets that contain a history with no charged action and no
  exclusion;
- **excluded:** sets after an exclusion. Failures are public, so these are
  disjoint from the forced sets;
- **free:** all the rest.

**Projection.** A binding is *bad* if it is unopenable, wrongly typed or
rejected by its guard. A history with no exclusion, no charged action and no
bad binding determines an honest history. Let $I$ be a forced set at which
player $i$ has an honest choice (a binding value, or opening). It projects to
an honest information set $\pi(I)$, which $I$ refines by operational data:
activations, receipts, serials, handle slots, leaks and timing.

**The profile $\sigma^*$ on the forced region.**

- *First activation while the event is ready.* The owner sends its free
  packet:
  - a binding with value drawn from $\sigma^H$ at $\pi(I)$, a fresh owned
    handle chosen independently of the value, and no evidence;
  - or the opening of its bound value.
- *Late delivery.* If the owner has sent nothing for an unresolved event, it
  follows a fixed policy $\pi^*$. At each activation, $\pi^*$ decides whether
  to send the free packet now, so as to maximize the conditional probability
  that the event succeeds. A late binding draws its value from $\sigma^H$ at
  $\pi(I)$.
- *Bad bindings.*
  - At the reveal of an unopenable or wrongly typed binding, no well-formed
    packet exists, so the owner stays silent.
  - A guard-violating binding may be opened: both choices lead to exclusion.
- *Otherwise* silence. In particular, the owner sends nothing further after
  its free packet.

**Trembles.** Take the honest tremble sequence $\sigma^H_n\to\sigma^H$, with
beliefs $\mu^H_n\to\mu^H$. Forced actions tremble in three tiers:
- **honest choices** follow $\sigma^H_n$ at the projection;
- **native-only uncharged actions** get probability $\eta_n$, the same at every
  information set. These are:
  - silence at the first activation;
  - a send time that $\pi^*$ does not choose;
  - a binding outside the honest values, or a bad binding;
  - a handle slot other than the prescribed one;
- **charged actions** get probability $\eta_n^M$.

Let $\rho_n$ be the smallest positive probability that $\sigma^H_n$ or Nature
gives to any action. Require $\eta_n=o(\rho_n)$, $M>T$ and
$\eta_n^{M-T}=o(\rho_n^T)$. Then any history with a charged action, of weight
at most $\eta_n^M$, is negligible against any history without one, of weight
at least $\eta_n^T\rho_n^T$.

**Excluded and free regions.** For each $n$, take an equilibrium of the
agent-form game in which forced sets play the perturbed $\sigma^*$, and all
other sets choose freely with minimum probability $\eta_n^M$ on every action.
It exists by Kakutani's theorem. Pass to a convergent subsequence of profiles
and Bayes beliefs.

### 3.2 Proof

**Lemma A (forced beliefs are honest).** At every forced set, the limit
belief puts zero weight on histories that have a charged action or another
player's bad binding. At a projecting forced set $I$, the belief over
$\pi(I)$ is $\mu^H(\pi(I))$.

*Proof.* We bound each kind of history in turn.
- *Charged actions* are negligible by the choice of $M$.
- *A bad binding* carries an extra factor $\eta_n$ compared with the honest
  binding that has the same public record, whose operational record has the
  same law (well-formed bindings are opaque).
- *Every other history* factors as $\Pr_n(h)=\Pr^H_n(\pi(h))\,N_n(h)$.
  - $\Pr^H_n$ is the honest probability.
  - $N_n$ collects the builder's draws, the leaks, the collection and the
    native-only choices.
  - By value-blindness and the construction of the trembles and of $\pi^*$,
    the law of the operational record given the honest history depends only on
    public data and opened values.
  - No packet in such a history carries evidence about an unopened value:
    well-formed bindings carry none, and every other packet is charged.
  - The opened values are public at $I$.

  So $\sum_{h\in I,\pi(h)=x}N_n(h)$ does not depend on $x\in\pi(I)$, and the
  posterior equals $\mu^H_n(\pi(I))\to\mu^H(\pi(I))$. $\square$

**Lemma B (delivery is one-dimensional).** Fix a forced history at which
player $j$'s event is unresolved and $j$ has sent nothing for it. For every
type of $j$ without a bad binding, a policy $s$ that sends at most the free
packet yields
$$
q_s\,V+(1-q_s)\,a_j ,
$$
where $q_s$ is its success probability and $V\ge L_j$ is $j$'s honest
continuation value. So every type ranks such policies by $q_s$ alone.

*Proof.*
- **After failure.** The free packet is never charged, and failure gives
  exactly $a_j$ whatever the route and whatever happens afterwards.
- **After success.** $\sigma^*$ plays the projection of $\sigma^H$, with
  honest beliefs by Lemma A, so the continuation is honest and worth
  $V\ge L_j>a_j$.
- **The success probability.** $q_s$ depends only on the builder and the
  policy. They may read the value being opened, which is public after success
  and payoff-irrelevant to $j$ after failure, but no other unopened value.
  So $\arg\max q_s$ is the same for every type that delivers the same value.
- **A late binding.** $q_s$ does not depend on the bound value, so the honest
  value choice remains optimal.
- **While the reveal is pending.** Other players' only uncharged action is
  silence, so their beliefs do not yet matter.
- **The handle slot.** It is uncharged cheap talk, and its trembles are
  value-independent, so observers ignore it by Lemma A. $\square$

**Lemma C (charged one-shot deviations do not pay).** At a forced set of
player $j$, every one-shot deviation to a charged action is strictly worse than
$\sigma^*$, whatever any player does afterwards.

*Proof.*
- $j$ is uncharged at a forced set: a charge needs $j$'s own charged packet,
  which $j$ would recall, and the set contains a charge-free history.
- The deviation yields at most $\max\text{gross}_j-\alpha K_j$.
- $\sigma^*$ never charges $j$, so it yields at least $\min\text{gross}_j$.
- The difference is at most $\Delta_j-\alpha K_j<0$.
- A further packet for an event is charged on every path where it is sent,
  whether the event succeeds or fails, so multi-packet delivery is covered
  too. $\square$

The lemma is one-shot on purpose. Because the charge is capped once per
player, removing one charged action from a strategy that takes another later
need not save anything.

**Sequential rationality, forced region.** By the one-shot deviation principle
for consistent assessments in finite games (Hendon, Jacobsen and Sloth 1996),
it suffices to check single deviations. From a forced history with no charged
action, play leaves the forced region only through the deviator's own charged
action or the deviator's own exclusion. No one else can make another player
fail: protected inclusion holds on every history, and other authors' packets
do not void it.

- **An honest choice at the first activation.** The beliefs are $\mu^H(\pi(I))$
  by Lemma A.
  - The free packet sent at once is included before the deadline, by
    opportunity, protected inclusion and timeliness, since expiry counts from
    readiness.
  - It is accepted: the binding has a fresh owned handle, or the opening is
    the certified value, and honest values pass their guards.
  - So the honest continuation follows, and $\sigma^H$ is optimal among honest
    actions.

  The alternatives are no better:
  - late delivery yields $q_sV+(1-q_s)a_j\le V$ (Lemma B);
  - a bad binding leads to exclusion at $a_j<V$;
  - charged actions are worse (Lemma C).
- **Late delivery.** $\pi^*$ is optimal by Lemma B, and Lemma C rules out
  charged actions.
- **After the free packet, and for non-owners.** Every alternative to silence
  is charged (Lemma C).

**Sequential rationality, excluded and free regions.** These follow from the
limit argument for perturbed agent-form equilibria: Selten perfection in agent
form implies sequential optimality. The forced agents are fixed throughout. An
excluded player's gross payoff is constant, and its packets are charged, so
silence is optimal for it.

**Consistency.** The assessment is the limit of Bayes beliefs along the fully
mixed profiles of the construction.

**Preservation.**
- Every owner sends its free packet at its first activation, and it is
  accepted before the deadline.
- So nobody is excluded or charged on path.
- Bindings follow $\sigma^H$, and samples follow their law.
- The builder's randomness affects no public result.

So the joint law of public results and net payoffs is the honest one.
$\square$

## 4. How the two theorems relate

Theorem 1's mechanism has three links:
1. Alice's payoff after a failed reveal depends on Bob's later answer.
2. Bob's answer reads what he saw of the omitted opening.
3. So the timing of a late send is a type-dependent choice. The equilibrium
   beliefs that this forces at the success records make a protected-turn
   deviation profitable.

Exclusion cuts the first link. A dead first packet is also charged in $C_0$,
which makes the cost of a late send depend on the route. That would recreate a
type-dependent choice even after exclusion (Section 5).

## 5. Why each change in $C_1$ is needed

- **Exclusion with a fixed payoff.** It breaks Theorem 1's mechanism (link 1
  of Section 4).
  - What the proof needs is narrower: after failure, the failing player's
    payoff depends neither on its type nor on the route.
  - Given a fixed payoff, the excluded player's later actions need not be
    removed. They affect only the excluded region.
  - The other players may continue under any payoff on public results,
    including the program's own failure semantics. Ending the game
    (constants for everyone) is the special case.
- **The free first packet.** Suppose a dead first packet costs an expected
  $\alpha K(1-q)$. Then, compared with silence, a late send is worth
  $$
  q\,(V-a_j)-\alpha K(1-q).
  $$
  - The builder is chosen after the deposit, so it can pick $q$ with
    $\alpha K(1-q)/q$ strictly between $L_j-a_j$ and $U_j-a_j$.
  - Then high-value types send late and low-value types stay silent, and
    Lemma A fails.
  - Charging *further* packets on every path is harmless (Lemma C).
- **Charging every disclosure.** Take Battle of the Sexes: both players
  commit, then both reveal. If an evidence-bearing binding were free, a player
  could verifiably commit first, and the other would best respond to it.
  Under $C_0$ the settled audit already forbids such packets. $C_1$ keeps that.
- **Deposit $\alpha K_i>\Delta_i$.** Lemma C needs it, and it does not depend
  on the builder.
- **Value-blind builder.** Lemma A needs it. The scheduler's view of the
  runtime contains pending payloads, so this is a real restriction on the
  builder.

## 6. Open questions and limitations

- **Isolating the causes.** Theorem 1 uses $C_0$, which has both continued
  failure branches and charged dead packets. Whether either one alone already
  breaks preservation is not settled.
- **Keeping the program utility after exclusion.** A plausible but unchecked
  variant gives the excluded player its program utility on public results,
  with its own results failed, minus a forfeit
  $D_j>\sup u_j-L_j$ (the supremum over histories in which $j$'s results
  failed). Its proof sketch has four ingredients:
  - the excluded player takes no further action, which the contract enforces;
  - with an empty context, players' unopened values are conditionally
    independent given the public history, so leaked values of the excluded
    player are uninformative and payoff-irrelevant;
  - the continuation lifts an SE of the residual honest game, chosen from
    public results only, by induction on the number of active players;
  - the excluded player's continuation value is then route-independent and
    below $L_j$.
- **Concurrency.** Both theorems are for Stage S, one event at a time. With
  concurrent events, a player can see another's pending opening before
  choosing, which is a channel exclusion does not address.
- **Infinite payload types** (for example sealed-bid auctions over $\mathbb N$)
  are outside both theorems.
- **Builder-first order.** If the deposit may depend on the builder's law,
  Theorem 2 applies unchanged. Whether the standard compiler $C_0$ preserves
  SE in that order is not settled here.
- **Mechanization.** Neither theorem is machine-checked. The finite games,
  information sets and runtime conditions are taken from a Lean
  formalization; Appendix A maps the names.

## Appendix A. Correspondence to the Lean development

| Note | Lean |
| --- | --- |
| Opportunity, protected inclusion, completion | `Vegas.EventGraphRuntime.AsyncContract` |
| Timeliness | `Vegas.EventGraphRuntime.AsyncTimely` |
| Packet (call, evidence, token) | `Vegas.EventGraphRuntime.WitnessedPacket` |
| Opening's own certificate | `Vegas.EventGraphRuntime.certifiedOpening` |
| Settled audit of $C_0$ | `Vegas.EventGraphRuntime.SettledRecord.Permits` |
| Per-author serials | `Interaction.MessageNetwork.submit` |
| Event address of a packet | `Vegas.EventGraphRuntime.Payload.event?` |

Items a mechanization must check beyond the statements above:
- the projection of raw information sets;
- value-blindness of the scheduler, the leak rule and collection;
- that expiry cannot fire before clock
  $\text{entered}+\mathit{delay}+\mathit{bound}+1$;
- that failures and expiries are in every player's view;
- that the five-event builder of Theorem 1 satisfies the contract and is blind
  to late packets;
- the agent-form fixed point.
