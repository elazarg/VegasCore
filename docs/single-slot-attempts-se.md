# Single-slot attempts and sequential-equilibrium preservation

This note asks whether a contract rule that makes every submission valid for
one named block, so that each attempt's fate is settled before its owner's
next opportunity, gives sequential-equilibrium (SE) preservation from the
intended game, compiled through the forfeit pass, to the asynchronous audited
runtime. The rule must work for every builder satisfying `AsyncContract` and
`BlindToLatePackets`, every finitely branching observation rule, a finite
audit deposit, and concurrency wherever the graph allows it.

The analysis is on paper. Its finite counterexamples were checked by an exact
rational script, described in the last section. Nothing here is Lean-checked
beyond the existing theorems it cites.

## Verdict

The rule does not by itself give SE preservation for that class. Its useful
effect is narrower than "informed retries fix the late leak".

1. **When the deposit may be chosen after the builder, the rule is not
   needed.** Suppose every authored envelope that ends without an accepting
   receipt is collected with probability at least $\alpha>0$, and every late
   attempt fails with probability at least $\delta>0$. Then a deposit
   $E\ge(U-L)/(\alpha\delta)$ makes every late send a deterred departure. In
   that case the checked deposit-extension theorem composes with the paper
   public-scheduling theorem, with or without single-slot attempts. The
   late-leak game `G*` is not a counterexample in this reading: for each fixed
   inclusion probability, a large enough charge removes its premise.
2. **When dead attempts are lawful (uncharged), which is the setting the
   rule is designed for, informed retry aligns the sender's types only if
   the visibility of a dead attempt does not depend on its slot.** A blind
   builder that publishes rejected slot-1 attempts and buries slot-2 attempts
   gives an exact finite game with no preserving SE, for every deposit and
   every forfeit $D>R$, with an empty pending-observation rule.
3. **When dead attempts are charged and the deposit is fixed relative to the
   payoff margins** (the reading under which `G*` refutes the
   arbitrary-builder target), the rule does not rescue the target. A builder
   whose two late slots have slightly different reliabilities near one
   produces a split, and so no preserving SE, at `G*`'s own margins. This
   holds with selective publication of dead attempts and also with complete
   publication. Retries decouple the benefit of an extra attempt from its
   charge, and the builder can tune one against the other.
4. **Concurrency adds an obstruction the rule does not touch.** The
   [concurrent-disclosure comparison](concurrent-disclosure-se-boundary.md)
   is compatible with single-slot attempts. With lawful dead attempts no
   deposit repairs it.
5. **Positive result for the rule (paper sketch).** Assume dead attempts are
   lawful, every dead attempt is either visible to every later decision maker
   before its decision or sealed until after all of them, and late inclusion
   is not coupled across owners. Then informed retry aligns all types on
   attempting at every late slot, and the intended outcome is an SE outcome.
   Each of these hypotheses is necessary in the sense that dropping it admits
   one of the counterexamples above.

## 1. The rule and what the contract can check

**The rule.** Every opening (and every binding) envelope carries a signed
target slot $\sigma$. The contract accepts the envelope only in the block of
height $\sigma$, and only if the event is ready and unfinished and the content
is canonical. An envelope included at any other height is rejected. Once
block $\sigma$ is final without accepting it, the envelope is **dead**: it
can never be accepted. The owner may author a fresh envelope for a later slot
(a **retry**), until the deadline.

**What the contract can check.** It can check the block height against
$\sigma$, check that $\sigma$ lies between the event's readiness and its
deadline, and check that the signature covers $\sigma$. A dead envelope that
is later included can be recognized from the record as rejected and dead.

**What the contract cannot check:**

- The send time. A stale envelope naming a past slot is indistinguishable
  from a censored one.
- Whether the builder saw an envelope. A dead envelope that is never included
  leaves no trace in the record.
- Owner activations.
- Which dead envelopes the builder publishes, or which pending envelopes the
  observation rule shows.

**Builder obligations the rule needs but cannot enforce:**

- **Slot-targeted protected inclusion.** An envelope sent at clock $t$ that
  names a slot $\sigma$ with $t+b\le\sigma<$ deadline, where $b$ is the
  inclusion bound, is included at $\sigma$. A send is *late* when no such
  slot remains, so late attempts live in the final stretch of $b$ slots. Two
  informed late attempts therefore need $b\ge2$.
- **Inter-slot opportunity.** After each late slot, the owner of an
  unfinished event has an activation before the next slot closes. Without
  it, retries are pipelined: blind sends naming several future slots.

**The audit choice.** A dead attempt can be declared **lawful** (no charge),
since the record shows that its named slot passed without acceptance.
Alternatively it can stay **forbidden** (charged once per owner, like any
envelope without an accepting receipt). Lawful dead attempts make every
stale envelope lawful too, because send time is invisible. This choice
decides which of the regimes below applies.

## 2. What the rule changes in the semantics

- No envelope is accepted after its slot. A dead envelope may still sit in
  the pending pool forever, and the network has no discard. It may be shown
  by the observation rule, or included later as a rejected ledger entry. Its
  fate is public, but its existence is public only if it is published or
  leaked.
- Each attempt is a fresh envelope with its own identifier. Sole-identifier
  protection applies per attempt, and the one-charge cap applies per owner.
  After a first dead attempt is charged, retries are free.
- Fate is settled before the next opportunity, so an informed retry replaces
  the blind double send that a late-settling builder allows.
- The slot field makes slot-selective treatment expressible without state.
  An observation rule that shows only openings naming slot 1, or a blind
  builder that includes (as rejected) only slot-1 dead attempts, depends only
  on the pool and the payload. This removes the objection that `G*`'s leak is
  not a stateless `MessageNetwork.ObservationRule`: under the rule, two
  attempts at different slots are different messages.
- Blindness constrains copies. If one envelope is included with probability
  $q$, then $k$ fresh copies in one slot are included with probability
  $kq/(1+(k-1)q)$ (the Luce law that `BlindToLatePackets` forces). The only
  exceptions are $q=0$ and $q=1$.
- Coupling across owners, where the inclusion law of one owner's late
  attempts depends on another owner's public traffic, is untouched.

## 3. The comparison and the alignment identity

The test family keeps the types, prior, payoffs and listener of `G*`. Types
are $t=(v,s)$ with $P(v=1)=9/20$ and $s\in\{A,B,C\}$ uniform. After a success,
the listener plays the safe answer $m$ (worth $2/5$ to it) or guesses $s$. The
sender then gets $R/2$ under $m$; under any guess, types $A$ and $B$ get $R$
and type $C$ gets $0$. After a failure, the listener answers $f_1$ or $f_0$,
worth $[a=v]$ to it. The sender gets $(R,0,0)$ under $f_1$ and $(0,R,0)$
under $f_0$, over $(A,B,C)$. A failed reveal costs the forfeit $D$, and an
owner with a forbidden envelope is charged $c$ in expectation, once. Here $c$
is the collection rate times the deposit, and $c=0$ when dead attempts are
lawful. The intended game has the unique SE in which the sender opens and the
listener plays $m$.

The sender opens at the protected turn, or defers to two late single-slot
attempts accepted with probabilities $q_1$ and $q_2$. It has an activation
before each late slot, so its retry is informed. The plans after deferring:

| Plan | Behaviour |
| --- | --- |
| X | Attempt slot 1; if it dies, retry at slot 2. |
| Xn | Attempt slot 1, no retry. |
| Y | Hold at slot 1, attempt slot 2. |
| Z | Never attempt. |

Write $F_X$ for the sender's failure value after X's two dead attempts and
$F_Y$ after Y's dead attempt. Suppose every success site uses the same reply,
worth $S$ to the type. Then

$$
V_X-V_Y=(1-q_2)\bigl[q_1(S+D)+(1-q_1)F_X-F_Y\bigr]+(q_1-q_2)c.
$$

Listener replies at success sites add a term $s\cdot(1,1,-1)$ with one
coefficient $s$ common to the three types of a value class. This is the
single reward direction of `G*`.

Three readings of the identity organize everything below.

- **Uniform visibility, lawful dead attempts.** Suppose dead attempts are all
  visible before the answer, or all sealed. Then $F_X=F_Y$, and with $c=0$
  the difference is $(1-q_2)q_1(S+D-F)>0$ because $D>R$. Every type prefers
  the earlier attempt.
- **Selective visibility.** Suppose a dead slot-1 attempt is seen and a dead
  slot-2 attempt is not. Then $F_X=F_k$ (value known) and $F_Y=F_0$ (value
  unknown). The type-dependent term $(1-q_1)F_k-F_0$, of size up to $R$, is
  set against $q_1(S+D)$. A first slot of low reliability makes the leak
  term dominate.
- **Charged retries.** The extra attempt's benefit $(1-q_2)q_1(S+D-F)$
  depends on the type through $S-F$. Its extra charge $(q_2-q_1)c$ does not.
  With a single emission per play, as in the
  [disclosure-phase theorem](full-public-disclosure-phase-preservation.md),
  sending at slot 1 rather than slot 2 changes payoff by
  $(q_1-q_2)(S+D-F+c)$, whose sign does not depend on the type. Retries break
  this common factor.

For the `G*` payoffs the split test can be solved exactly. For every listener
behaviour (every success-site mixture and every failure answer), some value
class has two types with opposite strict preferences between X and Y if and
only if

$$
q_1-\tfrac12<\frac{2K}{(1-q_2)R}<\tfrac12,
\qquad
K=(1-q_2)q_1\Bigl(D+\frac R2\Bigr)-(q_2-q_1)c,
$$

in the selective-visibility model. The script compares this closed form with
an exact piecewise check at 580 parameter points.

**Recovering the known informed-retry result.** With $q_1=q_2=q$ the window
needs $q(2D+R)/R<1/2$, so it is empty for `G*`'s margins at every $q$ above
$R/(2(2D+R))$. This agrees with the
[runtime-features probe](runtime-features-vs-late-leak.md), where the informed
retry restores a preserving SE at equal reliabilities.

## 4. Counterexample: an unreliable first slot, lawful dead attempts

**Configuration.** The types, prior, payoffs and listener are those of
`G*`, with any $R>0$ and any forfeit $D>R$. Dead attempts are lawful, so no
plan below carries a charge, whatever the deposit. The pending-observation
rule is empty. The builder is the following, in order:

1. It includes the protected opening at slot 0.
2. If the event completed, it activates the listener at once.
3. Otherwise it activates the sender (L1).
4. Slot 1: it includes no late opening ($q_1=0$).
5. It publishes, as a rejected ledger entry, the lowest-serial pending
   opening that names slot 1, one per owner.
6. It activates the sender (L2).
7. Slot 2: it includes a pending opening that names slot 2 with probability
   $q_2$, under the Luce law for copies.
8. Expiry, then the listener's answer.

The builder never includes anything else and never includes a non-owner
packet for an owned event.

**Contract conditions.**

- **`AsyncContract`.** The protected opportunity and protected inclusion hold
  at slot 0. The late sends carry no obligation, and every event finishes by
  expiry.
- **`BlindToLatePackets`.** At every input, each pending late packet either
  is included or gets weight 0. With weight 0, the builder acts exactly as it
  would if that packet were erased. The publication step gives weight 1 to
  one packet and 0 to the others, which is consistent with each erasure. Its
  choices depend on public state and on the payloads, which blindness allows.
- **Single-slot rule.** Nothing is accepted outside its named slot.

**What the listener can tell apart.** The listener sees only the ledger. A
success at slot 2 after a published dead slot-1 attempt (site S2E) differs
from a slot-2 success with nothing published (site S2N). A failure after a
published attempt reveals $v$. A failure with nothing published (site FN)
pools Y's dead attempt with never attempting.

**Raw options.** Extra raw options are equivalent to a core plan or
irrelevant to the outcome:

- A slot-1 envelope sent at the protected turn is X.
- A slot-2 envelope pipelined at L1 is Y, or X when sent together with a
  slot-1 envelope.
- Stale envelopes and raw signals are never published or observed, and they
  are lawful or uncollected.
- Copies change nothing at $q_1=0$.
- A post-failure activation reaches no one.

**Verdict.** Take any $q_2$ with

$$
q_2>\frac{D+R/2}{D+R}.
$$

Then no SE of this game has the intended outcome law. The argument is that of
`G*`, applied to sites S2E and S2N:

1. Every success reply acts along $(1,1,-1)$ with one coefficient per class.
2. With $q_1=0$ and $c=0$,
   $V_X-V_Y=(1-q_2)(F_k-F_0)+s\cdot(1,1,-1)$. Here $F_0=(yR,(1-y)R,0)$,
   where $y$ is the probability of $f_1$ at FN. For $y<1$, class $v=1$ has
   $f_A>0>f_B$ and $f_C=0$; for $y>0$, class $v=0$ has $f_B>0>f_A$ and
   $f_C=0$. Whatever the sign of $s$, such a class contains one type that
   strictly prefers X and another that strictly prefers Y. Each
   plan's continuation is strict: retry beats no retry by
   $q_2(S+D-F_k)>0$, and Y beats Z by $q_2(S+D-F_0)>0$.
3. Let $t_1$ attempt at L1 with probability $x_{t_1}\to1$, let $t_0$ have
   $x_{t_0}\to0$, and let the follow-up probabilities tend to one. The ratio
   of $t_1$ to $t_0$ at S2N, divided by that ratio at S2E, is
   $$
   \frac{(1-x_{t_1})\,x_{t_0}}{(1-x_{t_0})\,x_{t_1}}\cdot(\text{factors}\to1)\to0
   $$
   along every fully mixed sequence, whatever the deferral tilts. So one of
   the two sites has a limit belief on a face of the simplex.
4. On a face the largest belief is at least $1/2>2/5$, so the listener
   guesses.
5. The type $(v,A)$ or $(v,B)$ that reaches the face site by X or by Y then
   earns at least $q_2R-(1-q_2)D>R/2$, against $R/2$ for opening at the
   protected turn.

At $R=2$, $D=6$, $q_2=99/100$ the deferral gain is exactly $47/50$ at either
site. With $q_1=1/20$ the same holds. The window value is $7/20<1/2$, and the
gain at S2E is $893/1000$. In that case copies would raise the first slot's
reliability, which is why $q_1=0$ is the robust instance.

The forfeit, not the deposit, is the only deterrent here, and the builder is
chosen after $D$. The publication policy, not pending visibility, carries the
information. The obstruction is the
[honest-disclosure mechanism](honest-disclosure-preservation-boundary.md) in
a deviation subtree. A dead attempt that becomes public is a verifiable
disclosure of $v$ that a failed source reveal does not make. It splits the
types, and consistency then pushes a success belief to a face.

**What changes if the protected opening shares a slot with a late
attempt.** Under slot-targeted protection with $b=2$, the protected opening
can land at the same slot as Y's attempt. A slot-2 success is then
indistinguishable from the on-path success, since send time is not on chain.
S2N then keeps the prior belief and the reply $m$. Step 3 puts the face at
S2E, and step 5 goes through with X.

## 5. Counterexamples with charged dead attempts and margin-fixed deposits

Now dead attempts are charged $c>0$ once, and every unpublished stale envelope
or signal is charged too. Visible extra envelopes are then dominated whenever
$c>R/2+(1-q_2)R/q_2$. A pipelined slot-2 envelope costs $q_1c$ and gains
nothing over the informed retry. Copies at slot 1 cost a sure charge and gain
at most $q_1(1-q_1)/(1+q_1)$ times a bounded value.

**Selective publication, tuned reliabilities.** Take `G*`'s margins: $R=2$,
$D=6$, $c=3$. Let $q_2=999/1000$ and $q_1=5994/6013$, with the builder of
section 4 otherwise unchanged. The window value is $0.49842$, inside
$(q_1-1/2,\,1/2)=(0.49684,\,0.5)$, so a split holds for every listener
behaviour. The face argument uses S1 against S2N. The deferral gains are
$0.98734$ through X at S1 and $0.991$ through Y at S2N. Every premise of the
`G*` chain holds, so no SE has the intended outcome.

**Complete publication, tuned reliabilities.** Now let every dead attempt be
published before the answer. Then $F_X=F_Y=F_k$, the failure answer drops out
of the comparison, and in both classes

$$
V_X-V_Y=(1-q_2)q_1\Bigl(\frac R2+D-F_k\Bigr)+(q_1-q_2)c+s\cdot(1,1,-1).
$$

This splits $A$ from $B$ exactly when

$$
q_1(1-q_2)D<(q_2-q_1)c<q_1(1-q_2)\Bigl(D+\frac R2\Bigr).
$$

At $c=3$, $q_2=999/1000$ and $q_1=24975/25054$ the inequality holds, and so
does every other premise. The deferral gains are $0.98737$ at S1 and $0.991$
at S2N. As a control, with lawful dead attempts every type strictly prefers X
under complete publication.

**Why these need the margin-fixed reading.** For a fixed builder, raising $c$
pushes $K$ far below the window. Every type then strictly prefers Y, and
deferral costs at least $(1-q_2)c$. The script confirms that the split fails
for the same builder at $c=30$. These two games therefore refute only a
deposit bound fixed before the builder, the same reading under which `G*`
refutes the arbitrary-builder target. For any $c$ and $D$ they can be
rebuilt: choose $q_2$ close to one, then $q_1$ in the window.

## 6. The other mechanisms

**The `G*` mechanism.** The leak splits the types through the failure
answer. Informed retry neutralizes it only when the per-slot term
$q_j(S+D)$ dominates the visibility asymmetry. A sufficient condition, for
lawful dead attempts, is $q_jD>R$ at every late slot whose dead attempts are
treated differently from later ones. The script checks that this aligns
every type on attempting. The builder can always offer a slot below it.

**Blind and informed retry.** With lawful dead attempts, pipelining is free
and equivalent to an informed retry, so the inter-slot opportunity matters
only for charged attempts. With charged attempts and no inter-slot
opportunity, the blind double send of the
[runtime-features probe](runtime-features-vs-late-leak.md) keeps its
obstruction above its threshold.

**Leaks used before the fate is known.** In a serial program no decision is
ready between a send and its slot. Pending activations there have only
excluded raw actions, which a collectable charge deters and which an empty
rule makes uninformed. A decision that uses the leak before the fate needs
concurrency. Under the barrier order with the forfeit pass, the only
concurrently ready decisions are other reveals. Their open-or-withhold choice
is dominated by $D>R$, but their timing is not. That is the coupling channel.

**Value-selective builders.** Inclusion and publication may depend on the
disclosed value under `BlindToLatePackets`. The counterexamples need no
value selection. The positive sketch below needs its conditions for each
value: per-value visibility must be uniform across slots, since publication
that depends on the value is itself a signal at failure sites.

**Concurrency.** The concurrent-disclosure family uses one late slot per
owner, which already settles before expiry, and a builder whose late
inclusion depends on whether any owner opened early. It satisfies the
single-slot rule. With lawful dead attempts every SE is all-late for every
deposit. With charged attempts and complete collection, $E>W(2-\varepsilon)-D$
repairs that family; this bound is below $2W-D$ whatever the late risk. No general
liability-to-externality bound follows from the contract.

**Bindings.** A dead binding attempt carries an opaque handle, so it
discloses existence and timing but no value. The counterexamples above need a
dead attempt that discloses the value. Binding timing under the rule was not
analyzed.

## 7. Positive statements

### With a builder-dependent deposit (no single-slot rule needed)

**Hypotheses:**

- finitely many players and a bounded raw runtime;
- base payoffs in $[0,R]$ and forfeit $D>R$, through the forfeit pass;
- one protected opportunity per event: every send after the first protected
  activation is late;
- every late attempt is unaccepted with probability at least $\delta>0$ at
  every input (with $N$ inclusion steps per envelope, $\delta\ge(1-q^*)^N$,
  where $q^*<1$ is the largest late inclusion weight);
- every authored envelope that ends without an accepting receipt, and every
  forbidden envelope, is collected with probability at least $\alpha>0$
  under every continuation;
- retained play is a public scheduling of the source: scheduler inputs and
  every decision-visible field are recoverable from the source view at the
  next decision, and under concurrency only reveals are ready while an
  opening can be pending.

**Claim.** With $E\ge(U-L)/(\alpha\delta)$, where $U$ is the largest raw base
utility (forfeits included) and $L$ the smallest retained source utility,
every intended-game SE is preserved. The source-withholding wait is a
retained action; the excluded actions are late sends and forbidden envelopes.
The composition is:

- the checked intended-game step `Vegas.Paper.intended_sequential_equilibrium`;
- the paper [public-scheduling theorem](public-scheduling-se-preservation.md)
  for the retained runtime;
- the checked `exists_deposits_preserving_sequential_equilibria`, with
  detection $\alpha\delta$.

The single-phase sharper bound $q(D-R)\le(1-q)c$ from the
[late-turn note](open-problem-late-turn-equilibria.md) is an instance.

**Checked:** the public-scheduling theorem, for the abstract bounded public
scheduler of the [public-scheduling note](public-scheduling-se-preservation.md)
(section "The checked expansion"):
`GameTheory.Protocol.PublicScheduler.expanded_sequentialEquilibrium`, pinned as
`Vegas.Paper.public_scheduling_sequential_equilibrium` with standard axioms.
Its hypotheses are the source model's decision recall, nonterminal decision
fibers, recoverability of the public projection and of the actors from every
player's information at its decisions, and finitely supported draws. Each
player sees its own view of every draw, so a leak shown to one observer is
covered when its law reads only public data. Nonterminal decision fibers hold
for the source model (`Vegas.SourceProgram.Setup.decision_allNonterminal`).
The late-failure floor is `Vegas.EventGraphRuntime.LateSendsFailAtLeast`:
every packet an owner sends for its event after an earlier activation at which
the event was already ready ends without an accepting receipt with conditional
probability at least $\delta$, under every behavioral continuation. With it,
a late send is collected with probability at least $\alpha\delta$ under every
continuation (`Vegas.EventGraphRuntime.lateSend_collection_continuation`, from
the general `Vegas.EventGraphRuntime.deadPacket_collection_continuation`:
coverage at rate $\alpha$ of every packet forbidden by the final record, times
the probability that the packet stays dead).

**Unproved:**

- the realization: that the first-opportunity retained runtime (every owner
  submits once, at its first activation with the event ready, and is silent
  afterwards) is the expansion of the source model by a public scheduler in the
  sense above, with a public projection of the source view that the source
  language proves recoverable; this includes deriving the per-draw kernel and
  the per-player views from the builder's commands and the observation rule,
  and the typed-readout and payoff identities on erased histories;
- the remaining collection adapters in the deposit theorem's form: the
  first-opportunity retained menu as a restriction of the raw menu, its
  soundness (no charge on retained histories) and payoff matching, and the
  bounds for the other excluded actions (forbidden envelopes through coverage,
  missed bindings through the certain public charge);
- an actual watcher that achieves $\alpha$ for buried envelopes (the current
  backend is the idealized traffic sampler);
- inputs where late inclusion is sure ($\delta=0$). These give clean
  sure-success timing choices; a babbling completion seems to work but is not
  covered by the capstone.

### Without a usable deposit (the rule's own regime, paper sketch)

**Hypotheses:**

- the single-slot rule with lawful dead attempts;
- one protected opportunity per event;
- **uniform visibility:** every authored opening envelope of the event, dead
  or stale, is visible to every later decision maker before its decision
  (complete), or none is until all dependent decisions are taken (sealed);
- late inclusion of one owner does not depend on other owners' traffic;
- serial order, or the barrier order with only reveals concurrent;
- under complete visibility, at every late node some remaining slot has
  $qD>R$, so that attempting beats never attempting.

**Construction.**

- Every type opens at the protected turn and, after deferring, attempts at
  every late slot and retries.
- At every node every type uses the same trembles, so every success site
  carries $\pi(\cdot\mid v)$ and its source reply.
- Failure sites get any rational reply for their type-independent beliefs.

**Why it is sequentially rational.**

- By the identity of section 3 with $F_X=F_Y$ and $c=0$, attempting at slot
  $j$ beats holding by $\Pi_j q_j(S+D-F)\ge0$ for every type, where $\Pi_j$
  is the probability that every later attempt fails. Equality holds only when
  a later attempt is sure.
- Under sealing, attempting beats never by $q(S+D-F)>0$. Under complete
  visibility, attempting beats never by at least $qD-R>0$.
- Visible stale envelopes and repeated envelopes only label success sites,
  where every type's reply is fixed, or reveal a value that is already
  visible. They are prescribed uniformly and are payoff-irrelevant.
- Deferral pays $(1-\Pi)S+\Pi(F-D)\le S$, where $\Pi$ is the probability that
  every late attempt fails.

The disclosure-phase theorem's calibration should remove the $qD>R$
condition, as it does for a single emission; that extension is unproved.
Each hypothesis is needed, since dropping it admits a counterexample above:

| Hypothesis dropped | Counterexample |
| --- | --- |
| Uniform visibility | Section 4 |
| Lawful dead attempts | Section 5, complete publication |
| No cross-owner coupling | The concurrent-disclosure family |

### Margins and their factors

| Quantity | Condition |
| --- | --- |
| Forfeit | $D>R$; it is fixed before the builder |
| Collectable deposit | $\alpha\delta E>U-L$ deters every late send (builder-dependent) |
| Alignment, lawful, selective visibility | $q_jD>R$ at every slot whose dead attempts are treated differently (sufficient) |
| Split window, `G*` payoffs, selective | $q_1-\frac12<\frac{2K}{(1-q_2)R}<\frac12$ |
| Split, complete publication, charged | $q_1(1-q_2)D<(q_2-q_1)c<q_1(1-q_2)(D+R/2)$ |
| Profitable deferral at a face | $q_2R-(1-q_2)(D+c)>R/2$ (through Y), or $q_1R/2>(1-q_1)[(1-q_2)(D+R/2)+c]$ (through X at S1) |
| Attempt beats never | $q_2(D-R)>(1-q_2)c$ |
| Visible extra envelopes dominated | $c>R/2+(1-q_2)R/q_2$ |

## 8. What remains open

- **Native embeddings.** The counterexamples are comparison games at the
  level of `G*`. A native embedding would have to cover the following:
  - the compiled program and typed readout;
  - several envelopes per activation (harmless at $q_1=0$);
  - malformed and wrong-event packets;
  - listener raw actions (the listener here is activated only at its
    answer);
  - the slot-targeted contract itself, which does not yet exist in the
    runtime.
- **Charged dead attempts with a builder-dependent deposit.** Is a separate
  argument needed at inputs where late inclusion is sure, or does a babbling
  completion suffice in general?
- **Partial visibility.** Whether some deposit, or some restriction on
  publication policies short of uniform visibility, is enough when dead
  attempts are lawful and visibility is partial, for example a stateless
  leak that shows each pending envelope with probability strictly between
  zero and one. The selective instance above suggests that free pre-fate
  disclosure then defeats alignment even under $q_jD>R$, but this was not
  checked.

## The exact check

The exact rational script
[`single_slot_attempts_check.py`](../scripts/experiments/single_slot_attempts_check.py)
evaluates the comparison tree for the four plans. It checks the
following:

- the identity of section 3 and the common success direction;
- the split for every listener behaviour, by exact piecewise analysis in the
  failure answer and an independent grid check;
- retry beats no retry, and Y beats Z, at every vertex of listener
  behaviour;
- the face gains;
- the closed-form window at 580 parameter points;
- the complete-publication instance;
- the alignment under $q_jD>R$.

Controls in which the split fails, so that the impossibility proof does not
apply:

- equal reliabilities $99/100$, with $c=0$ and with $c=3$;
- the tuned builder with $c=30$;
- the unreliable-first-slot builder with $q_1=1/10$, where the window is
  missed.

The face step and the cross-ratio step are the paper steps of `G*`, whose
Lean form is `Vegas.Paper.late_leak_not_preserved_when_deferral_pays` for the
late-settling game.
