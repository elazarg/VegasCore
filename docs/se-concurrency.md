# Concurrency and SE preservation

Status: mathematics, written 2026-10-12, not mechanized.

Review history:
- An adversarial review of the first version found a counterexample: a
  concurrent commit phase let a player choose its value knowing that another
  player was late. That is now Example 3.
- The same review found a gap in how play after an exclusion was chosen.
- Both are fixed here:
  - commit phases **reset** on failure (§1);
  - play after an exclusion is a lift of a *residual* honest game, built by
    induction (§3).
- A re-review of that revision found nothing fatal and five fixable gaps.
  All are fixed here:
  - the induction carries prior *sequences*;
  - bad-binding types are covered in the residual;
  - the regions are redefined;
  - phases are maximal same-kind runs;
  - the builder after a barrier may differ.

This note extends Theorem 2 of
[the consolidated note](se-preservation-commit-reveal.md) from Stage S (one
event at a time) to concurrent execution that respects the source's
information dependence. Notation, the runtime and compiler $C_1$ are as
defined there.

Results:
- **Theorem 3 (positive).** Concurrent execution preserves every honest SE
  under three conditions:
  - concurrent commit phases reset on failure;
  - the builder is *success-separable*: whether an event succeeds depends only
    on its owner's delivery and on randomness private to that event, while the
    timing and order of inclusion are left free, subject to value-blindness,
    so a stable fee priority is allowed;
  - the exclusion payoff lies below every payoff the player can receive while
    not excluded.
- **Examples 1–3** show that each condition is needed:
  - Example 1: a builder that couples late inclusion across events;
  - Example 2: an exclusion payoff that is only below the honest range;
  - Example 3: a concurrent commit phase without a reset.

## 1. Concurrent execution

An **execution order** is a partial order $\prec$ on the program's events. An
owned event becomes **ready** once all its $\prec$-predecessors have completed.
The order is **information-respecting** if two conditions hold.

1. **Mixed kinds keep program order.** If a commit and a reveal, or a sample
   and any other event, appear in some order in the program, then $\prec$
   orders them the same way. So a commit sees exactly the publications that
   precede it in the program. A reveal that follows a commit in the program
   cannot be sent or leaked before that commit completes.
2. **Same owner keeps program order.** Two events of one owner are ordered as
   in the program. So every owner has at most one ready event, which matters
   because one activation emits at most one packet.

Guards read only values their owner knows at the commit, by assumption of the
source language, so they impose nothing further.

Consequences:
- Two concurrently ready events are of the same kind, with distinct owners.
- A **phase** is a maximal run, in program order, of events of one kind. It
  may contain several events of one owner, ordered among themselves, while
  other owners' events run alongside them.
- Execution alternates **commit phases** and **reveal phases**, with a barrier
  between consecutive phases.
- Stage S is the special case where $\prec$ is the program order.

**Phase reset (part of the compiler).** Suppose a binding of a commit phase
fails, through a missed binding or expiry. Then:
1. its owner is excluded, as in $C_1$;
2. at the end of the phase, every other binding of that phase is **voided**;
3. the remaining owners of the phase commit again, in a fresh commit phase
   with fresh deadlines and fresh events.

A voided binding is never revealed and reaches no payoff. Its free first
packet stays uncharged. Any later packet for the voided event is charged,
like any further packet. Reveal phases need
no reset, because a reveal is not a decision in the honest game. A program
whose commit phases are singletons (commits in program order) never resets.

## 2. Builder and compiler conditions

**Success separability.** For each owned event $e$ with owner $j$, the
builder's randomness splits into a component $\xi_e$ private to $e$, and a
remainder.

- **(S1) Success is private.** Whether $e$ succeeds is a function of $\xi_e$
  and of the clocks at which $j$ emits packets for $e$, counted from $e$'s
  readiness clock $r_e$. $j$'s activations while $e$ is ready are determined
  by $\xi_e$. The packets shown to $j$ at those activations (leaks) come from
  the remainder.
- **(S2) Independence.** The family $(\xi_e)_e$ is independent across events,
  and independent of the remainder of the builder's randomness, of every
  player's choices, and of every $r_f$. An event re-run after a reset is a new
  event, with a fresh independent $\xi$.

The following may depend on the public history and on the packets,
**per-event value-blind**: the law concerning event $e$ may read the value of
$e$'s own opening, but no other unopened value.
- *when* an included packet is included, and in what order relative to
  others (for example a stable priority induced by fees, which are not
  modelled);
- activations other than the owner's own while its event is ready;
- leaks, which are also author-only.

(S1–S2) are an assumption separate from protected inclusion. They say that a
late packet may fail, but neither its failure nor its success is correlated
with anything another player can influence.

The marginal version is not enough, that is, requiring only that each event's
success *probability* be unaffected by others' traffic. If successes can be
correlated through timing, a player who gains from another's failure prefers
anticorrelated timing, and how much it prefers it depends on its continuation
value. (S2) excludes this.

**Exclusion payoff.** Let $m_j$ be the minimum of $j$'s gross payoff over all
compiled terminal histories in which $j$ is not excluded. That includes
histories in which others were excluded and $u_j$ reads their failures.
Require $a_j<m_j$.

This bound depends only on the payoffs, so the order stays deposit-first. At
Stage S, $a_j<\underline u_j$ suffices. Example 2 shows that it does not under
concurrency.

## 3. Theorem 3

The induction below passes through programs that start from a nonempty
state. Call an **initialized program** a program together with:
- an initial public state (publications so far and the set of excluded
  players);
- for each active player, a set of existing hidden commitments, drawn from a
  prior that is a **product across players**;
- a **sequence of product priors** $\pi_n\to\pi$, with full support on each
  player's hidden commitments, including bad bindings. The honest SE must be
  consistent along it: its beliefs are limits of Bayes beliefs under
  $\pi_n$ and fully mixed profiles.

The sequence matters because a residual game starts from the native
posterior *along the tremble sequence*, not from its limit. Types with zero
limit mass, which arise only through trembles, still determine beliefs at
off-path sets. An honest SE consistent along a given prior sequence exists:
take a limit of perturbed equilibria with prior $\pi_n$.

An active player holding a bad binding in the prior is handled as in Theorem
2. It is projected as if it held a fixed honest value, and its weight
vanishes against every honest type.

An empty-context program is the special case with nothing initialized.
Product priors are preserved by honest play: each player's honest choice reads
only public data and its own commitments, so given the public history the
players' hidden commitments are independent.

**Theorem 3.** Take the deposit-first order, with compiler $C_1$ plus phase
reset, and fix:
- an initialized program with an information-respecting order;
- payoffs $a_j<m_j$;
- $\alpha>0$ and deposits with $\alpha K_i>\operatorname{sp}_i$;
- an honest SE $(\sigma^H,\mu^H)$;
- a per-event value-blind, author-only, success-separable builder satisfying
  the contract of the consolidated note's §1.2 (opportunity, protected
  inclusion, timeliness, completion) for every event.

Then some native SE preserves $(\sigma^H,\mu^H)$. Its beliefs are consistent
along $\pi_n$ together with the native trembles. This holds for every builder
continuation: after a barrier the builder's law may depend on earlier data,
and each such continuation is again a builder of the stated class.

The assessment it constructs has one further property:

**(P) Past-blindness.** On the forced and post-barrier regions (defined in
§3.1), from each barrier on, the prescribed play is a function of the public
results, the exclusion set, each player's own commitments, and data recorded
after the barrier. It does not read operational data (timing, serials, leaks)
recorded before the barrier. Play on the free region may read anything, but
the free region has vanishing weight at every set outside it.

### 3.1 Construction

The construction is by induction on the number $k$ of active players. For
$k=0$ there is nothing to show. Assume the theorem, with (P), for fewer than
$k$ active players.

**Regions.** These replace the regions of Theorem 2.
- The **forced** region: sets containing a history with no charged action
  whose last barrier was preceded by no exclusion. This includes the rest of a
  phase after an exclusion inside it.
- The **post-barrier** region: sets after a barrier that was preceded by an
  exclusion, reached without charged actions.
- The **free** region: sets reached only through a charged action.

Excluded players' own sets carry a constant gross payoff, and their only
uncharged action is silence.

**Within a phase (forced region).** Play follows $\sigma^*$ of the
consolidated note's §3.1, including between an exclusion and the next barrier.
There are two changes:
- **Delivery policy.** $\varphi^*$ is chosen among *own-service* policies,
  whose send times depend only on the owner's activations and on the clock
  relative to $r_e$, and, for a reveal, on the value being opened. A binding's
  delivery policy reads no value. $\varphi^*$ maximizes the event's success
  probability.

  By (S1–S2), conditioning on anything else cannot raise that probability:
  leaks and others' receipts come from the remainder, which is independent of
  $\xi_e$. So $\varphi^*$ is optimal among all delivery policies.
- **Honest values in a commit phase** are drawn from $\sigma^H$ at the
  projection $\Pi(I)$, whatever the native order of the phase's bindings.

**After a barrier preceded by an exclusion (post-barrier region).** The
public results and the exclusion set define an initialized **residual
program**:
- the excluded players' later events are failed;
- under phase reset, the voided bindings are removed, and the phase's
  remaining owners commit again.

Its prior is defined as follows. The native public history contains failures,
so it is not an honest history. Remove the excluded players' failed events and
everything they would have done later; what remains projects to an honest
public history $h^\circ$. The prior *sequence* is the posterior at $h^\circ$
of the active players' hidden commitments (bad ones included), along the
native tremble sequence: $\pi_n=\mu^H_n(h^\circ)(1+o(1))$, which tends to
$\pi=\mu^H(h^\circ)$. Each $\pi_n$ is a product prior:
- given the public history, the likelihood factors by player;
- no public result depends on another player's hidden value;
- bindings are opaque;
- every leaked opening belongs to a player who is excluded or already
  published.

Consistency makes every observer's marginal about player $i$ the same.

Take an honest SE $(\sigma^R,\mu^R)$ of the residual game, consistent along
$\pi_n$. By induction, the compiled residual game has a past-blind native SE
preserving it, for every builder continuation. Play from the barrier onward
follows that SE.

**Excluded players** stay silent, as before.

**Trembles and the free region.** Trembles are as in the consolidated note,
with these differences:
- the residual SEs carry their own tremble sequences, built along the prior
  sequence $\pi_n$ that the outer sequence induces at the barrier. So the two
  sequences are indexed together by construction, rather than merely
  multiplied;
- information sets reached only through a charged action form the free
  region, filled by perturbed agent-form equilibria as before.

### 3.2 Proof

**Lemma A″ (beliefs within a phase).** At every forced set, the limit belief
puts zero weight on histories with a charged action or with another player's
bad binding. If, in addition, the set is in a commit phase and its owner has
an honest choice, then the owner's belief about the honest values already
chosen is $\mu^H(\Pi(I))$, and the owner predicts the not-yet-chosen values of
the phase by $\sigma^H$.

*Proof.* The weights work as in Lemma A. The new operational data within a
phase are the order and timing of others' inclusions. Their law reads no
unopened binding value: bindings are opaque, the builder is per-event
value-blind, and binding policies read no value. So the factor $N_n$ does not
depend on the values.

The phase's not-yet-chosen values of other owners are chosen at information
sets that contain no other owner's value from the phase. An owner's own
earlier values in the phase are in its own information, as in the honest game.
$\square$

**Lemma D (value choice under reset).** Take a forced set in a commit phase
at which owner $j$ chooses a value $v$, together with any own-service delivery
policy. Then $j$'s expected payoff is
$$
\Pr(\text{no failure in the phase})\cdot V^H(v)\;+\;\text{terms independent of }v .
$$
Here $V^H(v)$ is $j$'s honest continuation value of $v$, at belief
$\mu^H(\Pi(I))$. So the honest choice $\sigma^H$ is optimal.

*Proof.* There are three cases.
- *$j$'s own binding fails.* Then $j$ gets $a_j$.
- *Some other binding of the phase fails, while $j$'s succeeds.* The reset
  voids $v$. The continuation is the residual SE, which by (P) depends on
  public results and on commitments that do not include $v$.
- *No binding fails.* Every value stands, and play continues by $\sigma^H$.
  Conditional on this event, the other values of the phase are still
  distributed by $\sigma^H$, because success is independent of values by
  (S1–S2) and value-blindness. So the conditional continuation value is
  $V^H(v)$ by Lemma A″.

The probability of each case does not depend on $v$. A binding's delivery
reads no value, and by (S2) others' successes do not depend on $j$'s
choices. $\square$

Without the reset, the second case would keep $v$, and $j$ would optimize
against a mixture that includes another player's failure. That is Example 3.

**Lemma B″ (delivery is one-dimensional).** Take a forced history at which
$j$'s event $e$ is unresolved and $j$ has sent nothing for it. Others in the
phase may be late, or may already be excluded. For every type of $j$ without a
bad binding, every policy $s$ that sends at most the free packet yields
$$
P_s\,V+(1-P_s)\,a_j ,
$$
where $V$ does not depend on $s$ and $V\ge m_j>a_j$. So every type ranks these
policies by $P_s$ alone.

*Proof.*
- *Failure* gives $a_j$.
- *Success.* Two things determine the continuation:
  - The outcomes of the phase's other events depend only on their own $\xi_f$
    and their owners' own-service policies or trembles, so they do not depend
    on $s$ (S1–S2).
  - After the barrier, play is either $\sigma^H$ (if no one failed) or the
    residual SE. Both depend only on public results, exclusions and
    commitments, by (P).

  Within the phase, the only things $s$ changes are inclusion timing and
  leaks. These are information that nobody's prescribed play reads: under
  $\sigma^*$, a binding's value choice reads no timing (Lemma A″), and the
  continuation after the barrier is past-blind.

  So $V$ is an expectation of $j$'s non-excluded gross payoff, which is at
  least $m_j$, and it does not depend on $s$. For a reveal, $P_s$ may depend
  on the value being opened, which is public after success, and $\varphi^*$
  reads only that value. $\square$

**Lemma C** (charged one-shot deviations do not pay) holds verbatim.

**Sequential rationality.** Single deviations suffice. No player can make
another fail without a charged action: another's emissions do not enter
$\xi_e$ (S1). The cases:

- **Honest value choice in a commit phase.** It is optimal among honest values
  by Lemma D. Sending at once succeeds surely, by protected inclusion. The
  alternatives are no better:
  - late delivery gives $P_sV+(1-P_s)a_j\le V$ (Lemma B″);
  - a bad binding gives $a_j$;
  - charged actions are worse (Lemma C).
- **Reveal at a first activation.** Sending succeeds surely and is worth at
  least $m_j>a_j$, whatever others do in the phase. Withholding gives $a_j$.
  Delaying cannot help, because nothing later reads the timing (P).
- **Late delivery.** $\varphi^*$ is optimal (Lemma B″).
- **After the free packet, non-owners, own bad bindings, excluded players.**
  As in Theorem 2.
- **From a barrier after an exclusion onward.** Sequential rationality holds
  by induction, provided the residual SE is an SE in the native continuation.

  It is: by (P), and by Lemma A″ applied to the pre-barrier operational data,
  that data is independent of every hidden value given the public history.

  The only values that leaked and were never published belong to excluded
  players. They are:
  - uninformative about the active players' values, by the product prior;
  - payoff-irrelevant, since the excluded players' results are failed;
  - read by no active player's prescribed strategy, by (P).

  So, along the sequence, conditioning on the pre-barrier data leaves every
  active player's belief equal to the residual prior $\pi_n$. The residual
  assessment's beliefs and rationality therefore carry over.

**Consistency.** The outer and residual tremble sequences share the index
$n$. The residual sequence is built along the prior sequence $\pi_n$ that the
outer sequence induces at the barrier. Within a residual continuation, the
remaining entry weights are value-independent common factors (Lemma A″). So
the native Bayes beliefs equal the residual ones along the sequence, including
at the residual's off-path sets.

**Preservation.** On the path every owner sends its free packet at its first
activation, which succeeds surely. So no exclusion or reset occurs, and play
follows $\sigma^H$. The joint law of public results and net payoffs is the
honest one. $\square$

## 4. Examples showing the conditions are needed

Each example has complete information, so every claimed choice is strict and
every SE makes it.

### Example 1: coupled late inclusion violates (S1–S2)

This adapts the finite game of
[the concurrent-disclosure note](concurrent-disclosure-se-boundary.md) to $C_1$.

**Program.** Three players each commit a value of a one-element type. Then
their three reveals form one reveal phase. Utilities are
$$
u_p=W\cdot\mathbf 1\{\text{some other player's reveal failed}\},\qquad W>0.
$$
Every honest payoff is $0$, and $m_p=0$.

**Builder.**
- All three reveals become ready at clock $0$, with delay $0$, bound $1$ and
  deadline $2$.
- At clock $0$, players $1,2,3$ are activated in that public order. Each sees
  every earlier pending emission.
- At clock $1$, everyone who has not sent is activated once.
- All inclusions happen during clock $1$:
  - if anyone sent at clock $0$, every packet is included;
  - if all three send at clock $1$, exactly one of the three, chosen
    uniformly, is omitted;
  - otherwise every packet is included.
- Unresolved reveals expire at clock $2$.

**Analysis.** For $a_p>-2W$:
- At clock $1$, a player who has not sent strictly sends.
- After two silences, player 3 strictly waits: $\tfrac23W+\tfrac13a_3>0$.
- Then player 2 strictly waits after one silence.
- Then player 1 strictly prefers silence.

So every SE has a failure. With $n$ players the same argument works for
$a_p>-(n-1)W$.

### Example 2: the bound $a_j<\underline u_j$ is too weak

**Program.** Alice commits $x$ and Bob commits $y$, both of one-element types.
Then the reveals of $x$ and $y$ form one reveal phase.

**Utilities.** Honest payoffs are $0$. If Bob's reveal fails while Alice's
succeeds, Alice gets $-X$, with $X>0$. If Alice's fails while Bob's succeeds,
Bob gets $W>0$.

Take $a_A\in(-X,0)$, which satisfies $a_A<\underline u_A$ but not $a_A<m_A=-X$.
Take $a_B<0$.

**Builder** (success-separable). Both reveals have delay $0$, bound $1$ and
deadline $2$.
- At clock $0$, Bob is activated first. A clock-$0$ packet of his is included
  immediately, before Alice's activation, so Alice knows whether Bob sent.
- Alice's packets sent after clock $0$ always fail.
- Bob's clock-$1$ packet succeeds with probability $q$, independently of
  everything else.

**Analysis.** If Bob is silent at clock $0$, he sends at clock $1$. Alice then
compares:
- sending, which gives $-(1-q)X$;
- withholding, which gives $a_A$.

Waiting is equivalent to withholding, since her late packets fail. She
withholds if $a_A>-(1-q)X$. Bob's silence then earns $qW+(1-q)a_B$, which is
positive if $qW>(1-q)|a_B|$.

Both conditions hold for some $q$ whenever
$\frac{|a_A|}{X}\bigl(1+\frac{|a_B|}{W}\bigr)<1$. For example, $a_A=-X/4$,
$a_B=-W/2$ and $q\in(1/3,3/4)$. Then every SE has a failure.

### Example 3: a concurrent commit phase without reset

**Program.** `commit a : {0,1} by A` and `commit b : {*} by B` form one commit
phase, followed by `reveal a` and `reveal b`. No guards.

**Utilities.**
- $u_A=-\varepsilon a$ if $b$ is published, and $u_A=Ha$ if $b$ failed.
- $u_B=W\cdot\mathbf 1\{a\text{ published}=1\}$.
- Take $\varepsilon=0.1$, $H=1$ and $W=4$.

The unique honest SE has $a=0$, with payoffs $(0,0)$. The minima are
$m_A=-\varepsilon$ and $m_B=0$. Take $a_A=a_B=-1$, so $a_j<m_j$ holds.

**Builder** (success-separable, value-blind). Both commits have delay $0$,
bound $1$ and deadline $2$.
- At clock $0$, B is activated first. B's clock-$0$ packet is included
  immediately.
- At clock $1$, B's late packet succeeds with probability $q=1/2$,
  independently of everything else. A's late packets fail.

**Analysis without reset.** Suppose A sees B silent at clock $0$.
- Binding $a=0$ gives $0$.
- Binding $a=1$ gives $-q\varepsilon+(1-q)H=0.45$.

So A binds $1$. Then B compares:
- binding on time, after which A binds $0$, giving $0$;
- silence, giving $qW+(1-q)a_B=1.5$.

So every SE has a failure.

**With reset.** If B fails, A's binding is voided and A commits again, so A's
first value matters only when B succeeds. A then binds $0$, and B's silence
gives $(1-q)a_B<0$.

The same counterexample works with different deadlines instead of a
leak-revealing schedule: a late A could observe B's expiry before choosing.
The reset covers that too.

## 5. What the compiler implements

Exclusion, the phase reset and post-barrier residual play are a **recovery
protocol** that the compiler adds. They are not a compilation of the program's
own failure branches:
- the honest game has no failures, so on its paths none of these rules ever
  fires;
- the preservation target constrains only the honest outcome law and the
  absence of charges on path. Off-path rules are the compiler's to choose, as
  the forfeit and the deposit are.

Under the program's *full* semantics, where failures are results and
utilities read them, a reset would change the meaning: there, another
player's failure leaves a commitment standing. So these compilers are correct
for programs whose intended meaning is the honest game. Programs in which
failure is meaningful source behaviour, such as deliberate withholding with
specified consequences, need a different compiler.

The recovery rules are part of the public contract, known to all players.

## 6. Remaining questions

- **Coupled builders.** Can a forfeit scaled by $n-1$, or capped fail-stop
  payoffs, restore preservation when (S2) fails? Example 1 bounds what a
  forfeit must exceed.
- **Correlated shocks.** (S2) excludes common outages that make all late
  packets fail together. A version allowing shocks no player can influence may
  suffice.
- **Realism of the reset.** It voids opaque commitments of the players who did
  not fail. This is standard practice (abort and restart a commit round). It
  lets a player delay the phase at the price of its own exclusion, which costs
  more than any non-excluded payoff.
- **Mechanization.** Several definitions need checking:
  - information-respecting orders as the runtime's dependency modes;
  - the phase reset in the contract;
  - success separability as a predicate on schedulers;
  - the induction over initialized programs (which needs Theorem 2's
    construction for product priors).
