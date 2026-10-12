# Concurrency and SE preservation

Status: mathematics, written 2026-10-12, not reviewed and not mechanized.

This note extends Theorem 2 of
[the consolidated note](se-preservation-commit-reveal.md) from Stage S (one
event at a time) to concurrent execution that respects the source's
information dependence. Notation, the runtime and compiler $C_1$ are as
defined there.

Results:
- **Theorem 3 (positive).** Preservation holds for concurrent execution under
  two added conditions:
  - the builder is *success-separable*: whether an event succeeds depends only
    on its owner's delivery and on randomness private to that event, while the
    *timing and order* of inclusion may depend on anything, including a stable
    fee priority;
  - the exclusion payoff lies below every payoff the player can receive while
    not excluded.
- **Example 1.** A builder that is not success-separable defeats $C_1$ for
  every forfeit below a bound proportional to the number of players.
- **Example 2.** Under concurrency, even a success-separable builder needs the
  stronger exclusion payoff.

## 1. Concurrent execution

An **execution order** is a partial order $\prec$ on the program's events. An
owned event becomes **ready** once all its $\prec$-predecessors have
completed. The order is **information-respecting** if it satisfies three
conditions.

1. **Mixed kinds keep program order.** If a commit and a reveal, or a sample
   and any other event, appear in some order in the program, then $\prec$
   orders them the same way.
   - A commit therefore sees exactly the publications that precede it in
     the program.
   - No reveal that follows a commit in the program can be sent, or leaked,
     before that commit completes.
2. **Same owner keeps program order.** Two events of the same owner are
   ordered as in the program. Every owner therefore has at most one ready
   event. This matters because one activation lets a player emit only one
   packet.
3. **Guards.** A guard reads only values known to its owner at the commit
   (assumption of the source language). So it never needs an unordered event.

Consequences:
- Any two concurrently ready events are of the same kind and have distinct
  owners.
- Execution therefore alternates *commit phases* and *reveal phases*,
  separated by barriers.
- Stage S is the special case where $\prec$ is the program order.
- In the honest game a reveal is not a decision. All honest choices happen in
  commit phases, at moments when no reveal is pending.

## 2. Builder and compiler conditions

**Success separability.** For each owned event $e$, with owner $j$, the
builder's randomness splits into a component $\xi_e$ private to $e$ and a
remainder, such that:

- **(S1) Success is private.** Whether $e$ succeeds is a function of $\xi_e$
  and of the clocks at which $j$ emits packets for $e$. That includes $j$'s
  activations while $e$ is ready, which are part of $\xi_e$.
- **(S2) Independence.** The family $(\xi_e)_e$ is independent across events,
  and independent of the remainder of the builder's randomness and of every
  player's choices.

Everything else may depend on the whole public history and on all packets:
- *when* an included packet is included, and in what order relative to
  other packets (for example a stable priority induced by fees, which are not
  modelled);
- activations other than the owner's own while $e$ is ready;
- leaks, provided the builder stays value-blind and author-only.

Protected inclusion is the special case in which, for an on-time packet,
success is sure. (S1–S2) extend this to late packets. A late packet may fail,
but neither its failure nor its success is correlated with anything another
player can influence.

The marginal version is not enough, that is, requiring only that each event's
success *probability* be unaffected by others' traffic. If two events' successes
can be correlated through a choice of timing, a player who benefits from
another's failure prefers timing anticorrelated with that player's success, and
that preference depends on the player's continuation value. (S2) excludes this.

**Exclusion payoff below every non-excluded payoff.** Let $m_j$ be the
minimum of $j$'s gross payoff over all compiled terminal histories in which
$j$ is not excluded. That includes histories in which *others* were excluded
and $u_j$ reads their failures. Require
$$
a_j<m_j .
$$
At Stage S, $a_j<\underline u_j$ suffices. Under concurrency, another player in
the same phase may already be late when $j$ decides, so $j$'s continuation
after its own success can include others' failures. Example 2 shows that the
weaker bound fails. $m_j$ depends only on the payoffs, so the order stays
deposit-first.

## 3. Theorem 3

**Theorem 3.** Take the deposit-first order, with compiler $C_1$, and fix:
- a program of the consolidated note's §1.1;
- an information-respecting execution order;
- payoffs $a_j<m_j$;
- $\alpha>0$ and deposits with $\alpha K_i>\operatorname{sp}_i$;
- an honest SE $(\sigma^H,\mu^H)$;
- any value-blind, author-only, success-separable builder satisfying the
  contract of §1.2 (opportunity, protected inclusion, timeliness, completion)
  for every event.

Then some native SE preserves $(\sigma^H,\mu^H)$.

### 3.1 Construction

The construction is the one of §3.1 of the consolidated note, with one
changed definition and one new remark.

- **The delivery policy $\varphi^*$** is chosen among *own-service* policies:
  policies whose send times depend only on the owner's activations and the
  clock while its event is ready, and on the value being delivered. Among
  these, $\varphi^*$ maximizes the success probability of the event. Under
  (S1–S2), conditioning on anything else, such as leaks or others' receipts,
  cannot raise that probability, because the remainder is independent of
  $\xi_e$. So $\varphi^*$ is optimal among all delivery policies.
- **Honest choices in a commit phase** follow $\sigma^H$ at the projection
  $\Pi(I)$, whatever order the phase's bindings take natively. Within a phase,
  no owner's honest information depends on another's binding of that phase.
  So the native order of bindings does not change any owner's information in
  the honest game.

Regions, trembles, and the agent-form equilibria on the excluded and free
regions are unchanged.

### 3.2 Proof

**Lemma A′ (beliefs).** At every forced set, the limit belief puts zero weight
on histories with a charged action or with another player's bad binding.

Let $I$ be a forced set in a commit phase at which the owner has an honest
choice. Then the owner's limit belief about the *already-chosen* honest values
of others is $\mu^H(\Pi(I))$. Its prediction of the *not-yet-chosen* values in
the same phase is $\sigma^H$ at those owners' honest information sets.

*Proof.* The first claim, and the factorization over already-chosen values,
are as in Lemma A. The only new kind of operational datum is the order and
timing in which other bindings of the same phase are included. These depend
only on activations, emitters and timing trembles, none of which reads a
value, so they leave the factor $N_n$ value-independent.

For the not-yet-chosen values: their owners will choose them at information
sets that contain no value from the current phase. Their law is therefore
$\sigma^H$ at those sets, whatever $I$ shows.

In the honest game the same owner, at $\Pi(I)$, faces exactly this
combination: the already-chosen values with belief $\mu^H$, and the later
values of the phase drawn independently from $\sigma^H$. So every action has
the same expected continuation natively as in $\Gamma^H$. $\square$

**Lemma B′ (delivery is one-dimensional under concurrency).** Fix a forced
history at which $j$'s event $e$ is unresolved, and $j$ has sent nothing for
it. Other events of the same phase may be unresolved, and their owners may be
late. For every type of $j$ without a bad binding, every policy $s$ that sends
at most the free packet yields
$$
P_s\,V+(1-P_s)\,a_j .
$$
Here $P_s$ is $e$'s success probability under $s$, and $V$ is $j$'s expected
continuation value given that $e$ succeeds. $V$ does not depend on $s$, and
$V>a_j$.

*Proof.*

- **Failure** gives exactly $a_j$, as before.
- **Success.**
  - By (S1–S2), whether the other events of the phase succeed is a function of
    their own $\xi_f$ and their owners' emissions. Those owners' policies are
    own-service policies (on the path of $\sigma^*$) or trembles that do not
    depend on $j$'s choices. So the joint law of the other events' outcomes is
    independent of $s$, and independent of whether $e$ succeeds.
  - What $s$ can change is only the *timing* of inclusions and the leaks.
    Under $\sigma^*$ both are information only, and Lemma A′ neutralizes them.
  - So $V$ is the expectation, over the others' outcomes and the later honest
    play, of $j$'s gross payoff with $j$ not excluded. It does not depend on
    $s$, and it is at least $m_j>a_j$.

Hence the payoff increases strictly in $P_s$. By the choice of $\varphi^*$ and
(S1–S2), $\arg\max P_s$ depends only on $\xi_e$'s law, the clock and the value
being delivered. It is the same for every type of $j$ that delivers the same
value. $\square$

**Lemma C** (charged one-shot deviations do not pay) holds verbatim. Its proof
uses only the deposit and that charges attach to the emitter.

**Sequential rationality, forced region.** Single deviations suffice, as
before. The claim that "nobody can make another player fail" now follows from
(S1–S2) rather than from Stage S: another player's emissions do not enter
$\xi_e$, and only the owner's own emissions enter (S1).

The cases are:

- **Honest choice at a first activation.** This happens in a commit phase.
  - The free packet sent at once succeeds surely, by protected inclusion. It is
    accepted, because the handle is fresh and owned.
  - By Lemma A′, every action's expected continuation equals its honest
    continuation. So $\sigma^H$ is optimal among honest actions.
  - The alternatives are no better:
    - late delivery gives $P_sV+(1-P_s)a_j\le V$ (Lemma B′);
    - a bad binding gives exclusion at $a_j<m_j\le$ every non-excluded payoff;
    - charged actions are worse (Lemma C).
- **Reveal at a first activation.** Sending succeeds surely, and the
  continuation, whatever others' late events do, is worth at least $m_j>a_j$.
  Withholding gives $a_j$. So sending is optimal, even after $j$ has seen other
  openings or other owners' silence.
- **Late delivery.** $\varphi^*$ is optimal (Lemma B′).
- **Own bad binding, after the free packet, non-owners.** Every alternative is
  charged or yields $a_j$, as before.

**Excluded and free regions, consistency, preservation.** As in Theorem 2. On
the path every owner sends its free packet at its first activation, which
succeeds surely. The phase order changes the order of inclusions but not the
public results. The joint law of public results and net payoffs is therefore
the honest one. $\square$

## 4. Examples showing the conditions are needed

### Example 1: coupled late inclusion

This adapts the finite game of
[the concurrent-disclosure note](concurrent-disclosure-se-boundary.md) to $C_1$.
The builder couples late inclusion across events, violating (S1–S2).

**Program.** Three players each commit a value of a one-element type. Then
their three reveals form one reveal phase. Utilities are
$$
u_p=W\cdot\mathbf 1\{\text{some other player's reveal failed}\},\qquad W>0.
$$
Every honest payoff is $0$.

**Builder.**
- All three reveals become ready at clock $0$, with deadline $2$, delay $0$
  and bound $1$.
- At clock $0$, players $1,2,3$ are activated in that public order. Each sees
  every earlier pending emission.
- At clock $1$, everyone who has not yet sent is activated.
- **Inclusion.** If anyone sent at clock $0$, every late opening is
  included. Otherwise, if all three send late, exactly one late opening,
  chosen uniformly, is omitted.

**Analysis.** Backward induction gives, for $a_p>-2W$:
- after two silences, player 3 strictly waits: $\tfrac23W+\tfrac13a_3>0$;
- after one silence, player 2 strictly waits;
- player 1 strictly prefers silence.

So every SE has a failure. With $n$ players the same argument works for
$a_p>-(n-1)W$.

The game has complete information, so the obstruction is the *incentive to
induce others' failure*, which coupling makes available. Under (S1–S2) no
player can change another's success.

### Example 2: the bound $a_j<\underline u_j$ is too weak under concurrency

**Program.** Alice commits $x$ and Bob commits $y$, both of one-element types.
Then the reveals of $x$ and $y$ form one reveal phase.

**Utilities.** The honest payoffs are $0$ for both. If Bob's reveal fails while
Alice's succeeds, Alice gets $-X$ with $X>0$. If Alice's fails while Bob's
succeeds, Bob gets $W>0$.

Under $C_1$, take $a_A\in(-X,0)$, which satisfies $a_A<\underline u_A=0$ but not
$a_A<m_A=-X$, and take $a_B<0$.

**Builder (success-separable).**
- Both reveals become ready at clock $0$.
- Bob is activated first, and Alice sees his pending emission.
- At clock $1$, the late owners are activated again.
- Bob's late opening succeeds with probability $q$, independently of
  everything else.

**Analysis.** Suppose Bob is silent at clock $0$. He will send at clock $1$,
since any success beats $a_B$. Alice then compares:
- sending, which gives $-(1-q)X$;
- withholding, which gives $a_A$.

She withholds if $a_A>-(1-q)X$. Bob's silence then earns
$$
qW+(1-q)a_B ,
$$
which beats his honest $0$ when $qW>(1-q)|a_B|$.

Both inequalities hold together whenever
$$
\frac{|a_A|}{X}\Bigl(1+\frac{|a_B|}{W}\Bigr)<1 ,
$$
by choosing $q$ in between. Fix such $a_A,a_B$ (for example $a_A=-X/4$ and
$a_B=-W/2$). Then some success-separable builder makes every SE have a failure.

With $a_A<m_A=-X$, Alice never withholds, and Theorem 3 applies.

## 5. Remaining questions

- **Coupled builders.** Can a forfeit scaled by $n-1$, or fail-stop payoffs
  capped at $\underline u_i$, restore preservation when (S2) fails? Example 1
  bounds what a forfeit must exceed. Whether coupled late regions can also
  carry a belief channel like Theorem 1's is open.
- **Realism of (S2).** Independent per-event service excludes correlated
  outages that make all late packets fail together. A version that allows
  common shocks the players cannot influence may suffice, but is not worked
  out.
- **Mechanization.** Two points need checking: information-respecting orders
  as the runtime's dependency modes, and success separability as a predicate
  on schedulers.
