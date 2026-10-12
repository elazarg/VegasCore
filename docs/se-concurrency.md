# Concurrency and SE preservation: findings

Status: mathematics, written 2026-10-12, not reviewed and not mechanized.

This note extends Theorem 2 of [the consolidated note](se-preservation-commit-reveal.md)
from Stage S, where events run one at a time, to concurrent execution, and
finds a new obstruction. Notation and the compiler $C_1$ (exclusion with a
free first packet) are as defined there.

## 1. Which events may run concurrently

Concurrency must respect the information dependence of the source semantics.
Guards read only values known to their owner. Under these two constraints,
the concurrent groups of a program are of two kinds.

- **Commitment phases.** These are maximal runs of commitments between public
  barriers. In the source, no commitment in a phase observes another's value:
  commitments are hidden.
- **Reveal phases.** These are sets of reveals that no guard or later decision
  orders. In the honest game a reveal is not a decision: it always opens.

Every event that reads a publication waits for it at a barrier.

## 2. What carries over from Stage S

**Commitment phases.**
- A well-formed binding is opaque, since it carries no evidence, and the
  builder is value-blind. So seeing another player's binding, whether pending
  or included, reveals only its timing.
- Seeing a binding first therefore gives no information the honest game
  withholds.
- Lemma A's factorization holds unchanged.

**Reveal phases.**
- A player who sees another's opening before sending its own learns a value
  that is public anyway on the honest path. Its own choice there is only
  whether, and when, to send an immutable opening.
- Withholding leads to exclusion at $a_j<\underline u_j\le V$. It is dominated even after
  learning others' values, so front-running a reveal gains nothing.

**Single deviations.**
- On the honest path every owner sends at its first activation, and
  protected inclusion holds whatever others send.
- So a player who goes late cannot change whether anyone else's on-time
  packet is included.

## 3. What breaks: coupled inclusion of concurrent late packets

At Stage S at most one event is unresolved at a time. With concurrency,
several players can be late at once. A builder admitted by the contract may
then **couple** their fates: whether one player's late packet is included can
depend on another player's traffic. Lemma B needs each player's delivery
choice to affect only its own success, so it fails.

The danger is not only in regions with two independent deviations. Suppose
one player's silence at its protected turn makes it rational for others,
having seen that silence, to go late too. Then a single deviation leads into
the coupled region, and the deviator can profit there.

### Counterexample to Theorem 2 under concurrency

This adapts the finite game of
[the concurrent-disclosure note](concurrent-disclosure-se-boundary.md) to
compiler $C_1$.

**Program.** There are three players. Each commits a value of a one-element
type, and then the three reveals form one reveal phase. Utilities:
$$
u_p=W\cdot\mathbf 1\{\text{some other player's reveal failed}\},\qquad W>0.
$$
On the honest game every payoff is $0$, so $\underline u_p=\overline u_p=0$. Under $C_1$, player
$p$'s exclusion payoff is a fixed $a_p<0$, and the others continue with $u$.

**Builder.**
- All three reveals become ready at clock $0$. Each has deadline $2$, delay
  $0$ and bound $1$.
- At clock $0$, players $1,2,3$ are activated in that public order, and each
  sees every earlier pending emission (leak probability $1$).
- At clock $1$, every player who has not sent is activated once.
- **Inclusion.** If any opening was sent at clock $0$, every opening sent at
  clock $1$ is included. If none was, and all three send at clock $1$, then
  exactly one of the three late openings, chosen uniformly, is omitted. Every
  other late opening is included.
- At clock $2$, unresolved reveals expire.

**The builder is admissible.**
- A clock-$0$ send is protected: $0+1<2$.
- A clock-$1$ send is unprotected, because expiry completes the event first.
- There are no values, so the builder is value-blind.
- The leak rule is author-only.
- Whether a late packet is included depends on other events' traffic, which
  the contract allows.

**Every SE has a failure on its path when $a_p>-2W$.**

We reason by backward induction. Every information set is a singleton up to
charged packets, which are dominated by the deposit (Lemma C).
- *Clock 1.* A player who has not sent should send: on success its payoff is
  at least $0>a_p$.
- *Player 3 at clock 0, having seen 1 and 2 silent.*
  - Sending makes every late opening included, so 3 gets $0$.
  - Waiting leads to the lottery. Player 3 is omitted with probability $1/3$
    (payoff $a_3$); otherwise someone else fails and 3 gets $W$. That totals
    $\tfrac23W+\tfrac13a_3>0$.

  So 3 strictly waits.
- *Player 2 at clock 0, having seen 1 silent.*
  - Sending gives $0$.
  - Waiting makes 3 wait, which gives $\tfrac23W+\tfrac13a_2>0$.

  So 2 strictly waits.
- *Player 1 at clock 0.*
  - Sending makes everyone succeed, so 1 gets $0$.
  - Silence makes 2 and 3 wait, which gives $\tfrac23W+\tfrac13a_1>0$.

So in every SE player 1 is silent, and some reveal fails with probability one.
The honest law (every reveal succeeds) is not preserved. $\square$

With $n$ players and "exactly one late opening omitted, uniformly", the same
argument works whenever $a_p>-(n-1)W$. The forfeit $\underline u_p-a_p$ must therefore
exceed $(n-1)$ times the gain from another player's failure. In particular,
Theorem 2's "the forfeit may be arbitrarily small" is false under concurrency.

The game has complete information, so this obstruction is about
*incentives to induce others' failure*. Beliefs play no role.

## 4. Routes to a positive result

1. **Success-separable builders (conjectured sufficient).**

   The proof does not need other events' traffic to be ignored altogether. It
   needs only that no player can change whether *another* event succeeds.

   Call a builder *success-separable* if, for each owned event $e$ and each
   delivery policy of $e$'s owner, the probability that $e$ succeeds does not
   depend on other events' packets or traffic. A delivery policy says when the
   owner sends its free packet, as a function of the owner's activations and
   observations. This probability includes the effect of the owner's later
   activations.

   Everything else may depend on other events' traffic:
   - *when* $e$'s packets are included, and in what order relative to other
     packets;
   - the activation order;
   - leaks.

   In particular, a stable priority order on packets is allowed, for example
   one induced by fees. Such an order may delay a packet behind
   higher-priority traffic, provided it never turns a success into a failure.
   This is the natural extension of protected inclusion, which already
   guarantees an on-time packet's success whatever others send. Late packets
   may still fail, but for reasons unrelated to other events' traffic.

   Under such a builder no player can change another's success without a
   charged action. The proof of Theorem 2 then appears to carry over:
   - Lemma B holds at every uncharged, unexcluded history, including when
     several players are late at once. A player's policy changes only its own
     success probability, and the timing of others' records.
   - The forced region needs no overlap exception.
   - Others' pending traffic and inclusion order give only timing
     information, which Lemma A neutralizes as before.

   *Not covered:* congestion that drops low-priority packets so that they miss
   their deadlines. There, one event's traffic changes another's success. The
   three-player counterexample is of this kind, and with unrestricted coupling
   it breaks preservation.

2. **A forfeit scaled with the number of players (open).** The counterexample
   needs $\underline u_p-a_p<(n-1)W$. Two questions are open:
   - whether a forfeit above $(n-1)$ times each player's spread suffices
     against every coupled builder;
   - whether coupled late regions can carry a belief channel like
     Theorem 1's.

   The forfeit would still depend only on payoffs, so the deposit-first order
   is kept.
3. **No reward for others' failure (open).** Fail-stop with constants
   $c_i^{(j)}\le\underline u_i$ removes every incentive to induce another player's
   failure, and it kills the counterexample above. A coupled builder can
   still make $i$'s timing affect $j$'s success, and so trade $i$'s own risk
   against $j$'s success, which $i$ prefers. That trade depends on $i$'s
   continuation value, hence on $i$'s type. Whether this yields a preservation
   failure is open.

## 5. Summary

- Information-respecting concurrency adds no information leak beyond timing.
  Opaque bindings and immutable openings see to that.
- What it adds is **cross-event coupling** of late inclusion. Under $C_1$ with
  a small forfeit this breaks preservation, as the three-player counterexample
  shows.
- With a success-separable builder, Theorem 2 is conjectured to extend
  unchanged.
- With coupled builders, a forfeit scaled by $n-1$, or fail-stop payoffs
  capped at $\underline u_i$, are candidate fixes. Both are open.
