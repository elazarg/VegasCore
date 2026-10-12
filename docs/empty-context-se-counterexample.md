# SE preservation for empty-context programs: a counterexample

Status: mathematics only, written 2026-10-12. Not mechanized. One
adversarial review against the runtime definitions found no fatal error; its
corrections (an exact proof of Tie 1, a pinned schedule detail, the form of
blindness, the deposit thresholds) are incorporated. Section 8 lists every
point that a mechanization must check against the actual runtime
definitions.

## 1. Question, assumptions and quantifier order

The question is whether a concrete compiler can preserve sequential
equilibrium (SE) for actual Vegas programs, without setup assumptions. The
checked native obstruction in
[native-se-obstruction](commit-reveal-research/native-se-obstruction.md) does
not answer it: its program starts from an initialized context (an initial
commitment to a Boolean and a private label input, drawn from a prior), which
a surface program cannot write. This note answers it for the primary target
below.

### Assumptions

1. **Programs.** Straight-line programs over commit (optionally guarded),
   reveal, sample and return, starting from the **empty context**: no setup,
   no private inputs, no initial commitments, no initial law. The example below
   uses only commit, reveal and return. It uses no guard and no sample.
2. **Utilities.** Each player's utility is a function of the public outcome
   only: publication results of every reveal (a value or failure). There is no
   type reading of an initial state, so no private valuation.
3. **Source game.** The *honest game*: every commitment holds a value accepted
   by its guard, and every reveal opens. Its strategic choices are the
   committed values.
4. **Forfeit.** The forfeit pass charges a player $D$ for each of their own
   failed publications, with $D$ strictly above every player's payoff range.
5. **Runtime.** The bounded raw signed-message runtime, Stage S (one event at
   a time in program order). Raw menus include silence, malformed calls,
   duplicates, extra identifiers, messages at forbidden times and unopenable
   bindings (a binding whose candidate is the failure result; it is uncharged
   and has the public effect of a value that is later withheld).
6. **Builder.** A public chance process satisfying `AsyncContract`, blind to
   late packets in the mixture form used by the checked obstruction (at any
   input holding a pending late packet, the builder's law is a mixture of
   including that packet and its law in the world where the packet was never
   sent), with an
   author-only mempool observation rule (leaks depend on the observer and the
   authors of pending messages, not on their content). Both are approved
   optional hypotheses in the [checklist](se-async-checklist.md); the
   counterexample satisfies them, which only strengthens it. Players know its law, not its
   realization.
7. **Audit.** The full authentic audit with one capped deposit per player:
   $K_A$ for Alice and $K_B$ for Bob, charged for forbidden traffic, for
   authentic messages that are never included, and for public binding
   omissions.
8. **Preservation.** A native SE preserves an honest SE when it induces the
   same joint law of public results and realized net payoffs, and charges and
   forfeits nobody on its paths. With an empty context there are no initial
   parameters to include.

### Quantifier orders

- **Deposit-first (primary).** Fix the program and utilities, then the forfeit
  $D$ and deposits $K_A,K_B$, then an honest SE, then the builder; the native
  SE may depend on everything before it. The deposit cannot depend on the
  builder at all.
- **Builder-first (secondary).** The deposit may depend on the builder's
  *law* (for instance on a lower bound on its late-omission probability),
  never on its realized events.

### Result

- **Deposit-first: refuted.** There is a program in the class above, using
  only three commitments, three reveals and a return (no guard, no sample),
  such that for every $D,K_A,K_B$ above the thresholds of Section 2 and every
  $\varepsilon>0$ some
  builder with late-omission probability in $(0,\varepsilon)$ admits native
  SEs, none of which preserves the chosen honest SE.
- **Builder-first: open.** The example's profitable deviation costs
  $\delta(D+K_A)$, so a deposit $K_A$ of order $R/\delta$ removes it. Whether
  preservation then holds is not settled here.

## 2. The program

Players Alice and Bob. Write $p\in(0,1)$ for a fixed probability, $R>0$ for
Alice's reward scale, and fix Bob's parameters $\gamma=1$ and $\beta=1/2$.

```text
commit  b : Bool        by Alice
commit  t : (ℓ, h)      by Alice      -- ℓ ∈ {0,1,2}, h ∈ Bool; one value of six
reveal  b               by Alice
commit  c : Answer      by Bob        -- Safe, L0, L1, L2, G0, G1
reveal  c               by Bob
reveal  t               by Alice
return  (utilities below)
```

The public outcome is $(p_b, p_c, p_t)$, each either a value or failure.
Gross utilities, before forfeits:

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

Every entry reads only public results. Alice's payoff ranges over $[0,R]$ and
Bob's over $[0,1+\gamma]$. Fix
$$
D>\max\{R,\,1+\gamma\},\qquad K_A>R/2,\qquad K_B>1+\gamma .
$$

What each piece is for:

- $\ell$, revealed last, replaces a private type: Alice's preferences over
  Bob's answer depend on a value she committed to and Bob has not yet seen.
- $h$, revealed last, keeps a *failed* opening of $b$ payoff-relevant. On path
  $h=b$, so an omitted opening of $b$ that Bob saw still predicts $h$. Without
  it, an omitted opening's content would never reach any payoff.
- The $\gamma$ term, the payoff $1$ for a label guess against a failed $t$,
  and $\beta>0$ close escape routes of the native SE (Section 7).

## 3. The honest SE

Alice commits $b\sim\mathrm{Bernoulli}(p)$ and, independently,
$\ell$ uniform with $h=b$. She opens $b$; Bob commits to Safe and opens it;
Alice opens $t$.

- **Bob.** His only information set is the published $b$. His posterior has
  $\ell$ uniform and $h=b$, so a label guess is worth $1/3<2/5$ and a Boolean
  guess $0$. Safe is optimal.
- **Alice.** Bob plays Safe whatever she commits, so every choice of
  $(b,\ell,h)$ earns $R/2$. Her mixed commitment is optimal.
- **Consistency.** Every information set of the honest game is reached.

The law to preserve: $b\sim\mathrm{Bernoulli}(p)$, $\ell$ uniform and
independent, $h=b$, all publications succeed, Bob publishes Safe, Alice nets
$R/2$ and Bob nets $2/5$.

## 4. The native configuration

**Schedule.** Events run in program order. The builder activates the owner
of each event when it becomes ready and includes the owner's latest message
immediately (a *receipt*; the contract may reject it as invalid), except for
the opening of $b$, which uses the late-turn schedule of the existing
obstruction:

| Clock | Operations |
| --- | --- |
| 0 | Alice activation and receipt (commit $b$); Alice activation and receipt (commit $t$); Alice activation and receipt (reveal $b$, her *protected* turn). |
| 1 | Alice's first late activation; Bob activation, mempool sample, receipt. |
| 2 | Alice's second late activation; inclusion lottery. |
| 3 | Expire the opening of $b$ if unresolved; Bob activation and receipt (commit $c$); Bob activation and receipt (reveal $c$) if his binding completed; Alice activation and receipt (reveal $t$) if Bob's publication completed. |
| later | Expiry of each unresolved event at its deadline, with one owner activation and receipt when an event becomes ready; settle. |

**Mempool.** At each activation, each pending message of the other player is
revealed independently with probability $1/2$ and remembered. Omitted
messages stay pending.

**Lottery.** With $m$ pending identifiers, each is included with probability
$w/(1+mw)$ and none with probability $1/(1+mw)$. A sole late opening is
included with probability $q=w/(1+w)$; let $\delta=1-q$.

**Records.** Each emitted message has a fresh per-author serial. An included
late opening shows its value and serial, with no emission time. Receipts and
binding omissions are public.

**Timing channel.** If Alice skips her protected turn and sends at clock 1,
Bob sees the opening at clock 1 with probability $1/2$; a clock-2 send cannot
be seen before the lottery. An omitted opening is seen again at clock 3 with
probability $1/2$. For a fixed $b$, Bob's records after a late opening are:

| Record | Meaning | Probability after a clock-1 send | After a clock-2 send |
| --- | --- | --- | --- |
| $E(b)$ | included, seen at clock 1 | $q/2$ | $0$ |
| $U(b)$ | included, not seen at clock 1 | $q/2$ | $q$ |
| $F_1(b)$ | omitted, seen at clock 1 | $\delta/2$ | $0$ |
| $F_3(b)$ | omitted, first seen at clock 3 | $\delta/4$ | $\delta/2$ |
| $F_u$ | omitted, never seen | $\delta/4$ | $\delta/2$ |

$F_u$ does not reveal $b$, so it is one information set for both values.
A packet Bob already knows produces no new observation when sampled again,
so $F_1(b)$ is a single information set.

The schedule is fixed in one respect the proof uses: Bob's only activation
between clock 1 and his commitment is at clock 3, in the success and failure
branches alike, even though his commitment is ready at clock 2 after a
successful lottery.

## 5. Theorem

For the program and utilities of Section 2, fix any $D,K_A,K_B$ satisfying the
bounds there and the honest SE of Section 3. For every $\varepsilon>0$ choose
$0<\delta<\varepsilon$ with
$$
\delta\,(D+K_A+R/2)<\min\{D-R,\ K_A-R/2\}
\qquad\text{and}\qquad
\delta<\frac{R}{3R+4(D+K_A)},
\tag{δ}
$$
and set $w=(1-\delta)/\delta$. The native game is finite with perfect recall,
so it has SEs. **No native SE preserves the honest SE.**

Order of choices: program and utilities; honest SE (independent of $D,K$);
forfeit and deposits; $\varepsilon$; builder; native SEs.

Example numbers: $R=1$, $D=3$, $K_A=2$, $K_B=3$, $w=24$ ($\delta=0.04$). Both
conditions hold ($0.22<1.5$ and $0.04<1/23$), and the deviation of Step 4
earns at least $0.75\cdot0.96-0.04\cdot5=0.52>0.5$.

## 6. Proof

Assume a native SE preserves the honest SE. "Alice's type" means her two
bindings: $b$ (openable, for every record above), and $t$, which is either an
openable value $(\ell,h)$ or unopenable, written $\bot$. A type is *real* if
it has positive probability in the honest law, that is $t=(\ell,b)$; real
types are on the native path because the law is preserved.

**Step 0. Late turns are off path.** The preserved law has every publication
succeed and no charge. A late opening is omitted with positive probability,
and any other first message at the protected turn is charged or changes the
record. So every type opens $b$ at clock 0 on path, and every record of
Section 4 is reached with probability zero. SE still requires sequential
rationality there, with beliefs consistent along one common fully mixed
sequence (Nature and the builder fixed).

**Step 1. Clean late play is one opening.** At a late history with no
unavoidable charge, an openable-$t$ type comparing one proper opening with its
alternatives gets: at least $qR/2-\delta(D+K_A)$ (labels $0,1$) or
$-\delta(D+K_A)$ (label $2$) from one opening; at most $R-K_A$ (resp.
$R/2-K_A$) from any continuation with a duplicate, extra identifier or
malformed message; at most $R-D$ (resp. $-D$) from permanent silence. By
(δ) one opening is strictly best: send at clock 1 and stay quiet, or send at
clock 2. A $\bot$ type earns gross $0$ in every continuation and pays $D$ at
the reveal of $t$; one opening costs it $\delta(D+K_A)<D$ in expectation, so
it also sends exactly one opening, at a time it is indifferent about.
Alice opens an openable $t$ at its reveal: withholding forfeits $D$ and
cannot raise her gross. Bob never sends forbidden traffic ($K_B$ exceeds his
range), binds a valid answer and opens it ($D$ and $K_B$ exceed his range).
These are derived incentives over the full raw menu.

So, for every type, records arise from one opening sent at clock 1 or
clock 2. In the common tremble sequence, write $\omega_{\tau,n}$ for the
probability that type $\tau$ is drawn and stays silent at the protected turn,
and $a_{\tau,n}$ for the total probability (over all aliases, with or without
extra traffic afterwards) that her first late emission is the opening, sent at
clock 1. By Step 3 below its limit $a_\tau$ is $0$ or $1$ wherever timing
preferences are strict. Every other history reaching a record of
Section 4 needs an extra emission: before the opening it changes the
opening's serial (a different record); after it, it is a tremble against the
strict preference of Step 1. Hence, for each record $r$,
$$
\Pr_n(r,\tau)=\omega_{\tau,n}\,\bigl(\kappa_r(a_{\tau,n})+o(1)\bigr),
$$
with $\kappa_r$ the probability in the table of Section 4 and $o(1)$ uniform
over the finitely many types. Bob's posteriors at $E(b),U(b),F_1(b),F_3(b)$
are over the types with that $b$.

**Step 2. The two ties.**

*Tie 1: $E(b)$ and $F_1(b)$ carry the same belief, exactly.* Fix any
history up to the lottery in which Bob saw the opening at clock 1, including
histories where Alice also emitted extra traffic after it. Whatever the
number $m$ of pending identifiers, the lottery includes the opening with
probability $w/(1+mw)$ and nothing with probability $1/(1+mw)$, a ratio
$w:1=q:\delta$. Including any *other* pending packet produces a public
receipt and hence a different record. Inclusion removes only the included
identifier, so Alice's other pending packets meet the same fate in both
branches. Bob already knows the opening, so seeing it again at clock 3 gives
him no new observation. And Bob has exactly one activation, hence one
mempool sample, between the lottery and his commitment, at clock 3, in both
branches (Section 4). So for every type and every $n$,
$\Pr_n(E(b),\tau):\Pr_n(F_1(b),\tau)=q:\delta$, with no assumption on the
rates of $a_{\tau,n}$ or of the extra-traffic trembles, and Bob's posteriors
at $E(b)$ and $F_1(b)$ coincide along the sequence and in the limit.

*Tie 2: the cross identity.* For two sets of types $G_u,G_v$ (with the same
$b$) such that $a_{\tau,n}\to1$ on $G_u$ and $a_{\tau,n}\to0$ on $G_v$,
$$
\mu_{E(b)}(G_v)\,\mu_{U(b)}(G_u)\to0 .
$$
Proof: with $W_X=\sum_{\tau\in X}\omega_{\tau,n}$,
$\mu_E(G_v)/\mu_E(G_u)\le o(1)\cdot W_v/W_u$ and
$\mu_U(G_u)/\mu_U(G_v)\le(1/2+o(1))\cdot W_u/W_v$, since
$\kappa_E(a)=aq/2$ and $\kappa_U(a)=(1-a/2)q$. The product of the two ratios
tends to zero and the unknown weights cancel; $\mu_E(G_u),\mu_U(G_v)\le1$.
No assumption on the relative rates of the $\omega_{\tau,n}$ is used.

**Step 3. Timing preferences.** Fix $b$. Let $\sigma_E,\sigma_U$ be Bob's
probabilities of Safe at $E(b),U(b)$, and $y_1,y_3,x$ his probabilities of
guessing $1$ at $F_1(b),F_3(b),F_u$. At success records a Boolean guess is
strictly worse than Safe, so Bob's alternative to Safe is a label guess. At
failure records he always makes a Boolean guess: the best guess earns at
least $\min\{1/2,\beta\}>0$ and the other answers earn $0$.

For an openable-$t$ type with label $\ell$ (any $h$), Alice's payoff from
sending at clock 1 minus clock 2 is, for $\ell=0,1,2$,
$$
(S+F,\ S-F,\ -S),\qquad
S=\frac{qR}{4}(\sigma_U-\sigma_E),\qquad
F=\frac{\delta R}{4}\,(2y_1-y_3-x).
$$
$S$: labels $0,1$ earn $R-\tfrac R2\sigma$ after success and label $2$ earns
$\tfrac R2\sigma$; a clock-1 send reaches $E$ or $U$ with probability $1/2$
each and a clock-2 send reaches $U$. $F$: given omission, a clock-1 send
reaches $F_1,F_3,F_u$ with probabilities $1/2,1/4,1/4$ and a clock-2 send
reaches $F_3,F_u$ with $1/2,1/2$; label $0$ is paid $R$ for a guess of $1$
and label $1$ for a guess of $0$. Alice's payoffs do not read $h$, so the
timing preference depends on $\ell$ only. If $S\ne0$ or $F\ne0$, the vector has
a strictly positive and a strictly negative entry, so some label group $G_u$
(all openable types with that label and this $b$) has $a\to1$ and another
group $G_v$ has $a\to0$.

**Step 4. The contradiction.** Two cases exhaust Bob's play at success
records.

*Case A: for some $b$, Bob plays Safe with probability zero at one of the
records $E(b)$, $U(b)$.* At that record he guesses a label. Let the real type $(b,(0,b))$ deviate: stay silent at
clock 0, send at clock 1, stay quiet. On inclusion she reaches $E(b)$ and
$U(b)$ with probability $1/2$ each; she earns $R$ at the record without Safe
and at least $R/2$ at the other (Bob never makes a Boolean guess there). On
omission her gross is nonnegative and she pays $D+K_A$. So she earns at least
$3qR/4-\delta(D+K_A)>R/2$ by (δ), more than her equilibrium payoff $R/2$. Her
type is on path, contradicting sequential rationality at her protected turn.

*Case B: for both $b$, Safe has positive probability at $E(b)$ and $U(b)$.*
Then Safe is optimal at all four records. At a success record write
$\mu_\bot$ for the mass on unopenable $t$, $m$ for the mass on $h\ne b$, and
$\mu_k$ for the mass on openable $t$ with $\ell=k$. A label guess $L_k$ is
worth $\mu_\bot+\mu_k+\gamma m$, so Safe-optimality gives
$\mu_\bot+\mu_k+\gamma m\le2/5$ for every $k$. Summing over $k$,
$2\mu_\bot+3\gamma m\le1/5$, and every label has
$\mu_k\ge1-\mu_\bot-2(2/5-\mu_\bot-\gamma m)\ge1/5$.

- At $E(b)$, $m\le1/15$ and $\mu_\bot\le1/10$, so the mass on $h=b$ exceeds
  $1/2$. By Tie 1 the same holds at $F_1(b)$, where guessing $b$ is worth
  $\Pr(h=b)+\beta\mu_\bot$ against $\Pr(h\ne b)+\beta\mu_\bot$ for the other
  guess. So Bob strictly guesses $b$: $y_1(b)=b$.
- Then $F(0)=0$ forces $y_3(0)=x=0$, and $F(1)=0$ forces $y_3(1)=x=1$. So
  $F(b)\ne0$ for some $b$; fix it.
- By Step 3 some label group $G_u$ has $a\to1$ and another $G_v$ has $a\to0$.
  By Tie 2, $\mu_{E(b)}(G_v)\,\mu_{U(b)}(G_u)\to0$. But Safe-optimality at
  both records gives $\mu_{E(b)}(G_v),\mu_{U(b)}(G_u)\ge1/5$, so the product
  is at least $1/25$. Contradiction.

So Case A holds, and Case A contradicts the assumption. $\square$

## 7. Why each payoff term is needed

Each term closes a way in which a native SE could neutralize the leak with
off-path beliefs. Removing a term reopens that route; this is how the
example was found, and it is the map for any positive result.

| Term | Escape it closes |
| --- | --- |
| $h$ revealed last, $h=b$ on path | Without it a failed opening's content is never payoff-relevant (utilities read public results only, and a failed reveal is final), so Bob's guess after a seen omission cannot depend on it, and $F=0$. |
| $\gamma\,\mathbf 1_{h\ne b}$ for label guesses | Bob could believe the types at $F_1(b)$ are split evenly between $h=b$ and $h\ne b$, be indifferent, and guess as at $F_u$, making $F=0$. Tie 1 puts the same split at $E(b)$, where the $\gamma$ term then rules out Safe. |
| Label guess against failed $t$ pays $1$ | Bob could believe the deviators' $t$ is unopenable; with a zero payoff his label guesses would be worthless and Safe trivially optimal at $E,U$ whatever the label masses. The payoff $1$ caps that mass at $1/10$. |
| $\beta>0$ | Bob always makes a Boolean guess after an omission, so labels $0$ and $1$ are exact mirror images ($\pm F$). |
| Commitment to $\ell$ revealed last | Supplies Alice's "types" without setup: her preferences over Bob's answer depend on her own hidden commitment. |

Tie 1 is the new ingredient compared with the setup-based obstruction: Bob's
belief after seeing an opening early cannot depend on whether the opening was
later included, so whatever neutralizes the failure branch also contaminates
the success branch.

A guard could replace the $\gamma$ term: guard $h$ by "$h=b$", which reads
Alice's own commitment. On the failure branch the guard is vacuous for the
failed input (an obligation accepts when its *successful* results are
compatible), so the mismatched types still exist there; on the success branch
the guard rejects them at the reveal of $t$. That variant needs the
rejection's public effect, which is not worked out here.

## 8. Scope and what a mechanization must check

- **Builder contract.** The schedule of Section 4 extends the checked
  late-opening service to five events. A mechanization must prove
  `AsyncContract` (reaction opportunity, protected inclusion, completion,
  timeliness) and blindness to late packets for it, with explicit deadlines,
  reaction delays and inclusion bounds. The claim here is by analogy with the
  checked service, not a proof.
- **Records.** The proof assumes: per-author serials are allocated at
  emission and shown on included and observed messages; receipts and binding
  omissions are public; an observed opening's validity is checkable. These
  match the existing native runtime but must be confirmed.
- **Audit.** Step 1 needs duplicates and extra identifiers to be charged. If
  box S9 makes a censored late opening permitted, an omission costs $D$ only
  (the deviation improves), but duplicates must remain charged; otherwise a
  "send twice" option changes Step 1.
- **Blindness.** The lottery's probability of including nothing depends on how
  many late packets are pending, so it violates a literal "commands other
  than including the packet do not depend on it" reading. It satisfies the
  mixture form named in Section 1, which is the form the checked obstruction
  proves.
- **Deposit thresholds.** The refutation covers every $D>\max\{R,1+\gamma\}$,
  $K_A>R/2$ and $K_B>1+\gamma$. The checklist's "deposit strictly above the
  deterrence bound" is not defined there per player; if that bound can be
  lower than these thresholds, the deposits in between are not covered.
  Scaling a player's utilities scales that player's threshold with them, so
  the meaningful form is relative: the forfeit above every payoff range,
  $K_A$ above half of Alice's range, and $K_B$ above Bob's range.
- **Evidence attachments.** Raw packets can carry checkable opening evidence
  (`WitnessedPacket.evidence`). Step 1 treats a late opening with extra
  evidence, for example about $t$, as a different emission that leads to a
  different record. A mechanization must check that the audit charges such
  attachments, or extend Step 1 to show they are not strictly preferred.
  The [exclusion note](empty-context-fail-stop-preservation.md) sketches, for
  Battle of the Sexes, how an uncharged evidence channel breaks preservation.
- **Unopenable bindings.** The proof allows them (they only enlarge the set
  of types) and handles them in Case B.
- **Honest SE.** It relies on Alice's indifference among her commitments.
  That is a valid SE of the honest game; the target quantifies over every
  honest SE.
- **Builder-first order.** Open, see Section 1.
- **Private valuations.** Secondary; the setup-based obstruction already
  covers a program with an initial private input.
- **Concurrent stage.** Not considered; Stage S already fails.
