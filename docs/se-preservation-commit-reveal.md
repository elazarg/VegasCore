# Sequential equilibrium of commit–reveal programs on an asynchronous ledger

Status: mathematics on paper, not mechanized. Theorems 1 and 2 and
Proposition 1 have been through several adversarial reviews. Theorem 3 rests
on the conditional transport step (Lemma T, Section 4.5), whose current form
has not yet been independently reviewed.
Section 9 lists what is open.

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

**What kind of result this is.** The negative result is about a standard
compiler. The positive results are an *equilibrium implementation through
recovery rules that the compiler adds*: exclusion, a free first packet, and
a reset. These rules preserve the honest game's outcome law, but they change
what failures mean. An excluded player's utility is replaced by a fixed
payoff, and a reset voids surviving players' commitments. So this is not
preservation of the program's own failure semantics, and it is a separate
target from preservation under a fixed compiler and runtime (Section 8). The
positive theorems are existence results. For each honest SE they construct
one SE of the compiled game that preserves it, with suitable off-path
beliefs. They do not claim that every SE of the compiled game preserves it.

- **Theorem 1 (negative).** The standard compiler fails. It charges a forfeit
  for each failed reveal and continues the program, and it charges every
  authentic packet that is never accepted. There is a program with three
  commitments, three reveals, and no setup, guard or randomness, such that the
  following holds for every forfeit and deposit above fixed thresholds and
  every $\varepsilon>0$. Some admissible builder, with late-omission
  probability below $\varepsilon$, has native SEs, and none of them preserves
  the honest SE.
- **Theorem 2 (positive, one event at a time).** A modified compiler succeeds,
  with two changes.
  - *Exclusion.* A player whose event fails gets a fixed payoff below every
    honest payoff of theirs, and the others continue.
  - *A free first packet.* A player's first well-formed packet for an event is
    never charged, whether or not it is included. Everything else the player
    sends is charged. Equivalently: a player may sign at most one packet per
    move, and it must be well-formed. Violations are proved from signed
    packets, like double-signing; non-inclusion alone is never chargeable.

  For every program in the class, every forfeit, every deposit above the
  payoff spread and every admissible value-blind builder, every honest SE is
  preserved by some SE of the compiled game.
- **Theorem 3 (positive, concurrent).** The same holds when events run
  concurrently in an order that respects the source's information dependence.
  Five further conditions are needed:
  - concurrent commit phases are reset when a binding fails;
  - the builder is *success-separable*: whether an event succeeds depends only
    on its owner's delivery and on randomness private to that event, while the
    timing and order of inclusion are free, so a stable fee priority is
    allowed;
  - the builder is *per-event value-blind*: what it does with an event reads no
    unopened value other than that event's own opening;
  - its leaks are *content-blind*. Pending packets are visible: the builder
    may show any of them, in full, to any player, as a public mempool does.
    What is restricted is only *which* packets are shown to whom and when:
    that may depend on who sent them, but not on what they contain;
  - the exclusion payoff lies below every payoff the player can receive while
    not excluded.

  Examples 1–3 show that three of these are needed: success separability,
  the reset, and the stronger payoff bound. Whether value-blindness and
  content-blind leaks are needed is not shown.
- **Theorem 4 (source explanation).** Under the hypotheses of Theorem 3, honest
  players need to reason only about a source-level game $\Gamma^X$. It is the
  source program, with its own deferred guards, read with one extra rule: *a
  failure excludes its author with a fixed payoff*, plus the reset under
  concurrency. It is **not** the program's own failure semantics. Exclusion and
  reset are a recovery protocol that the compiler adds (Section 8). Each
  runtime fact an honest player can meet at a clean information set is
  explained in $\Gamma^X$, by one of three tiers:
  - the *mechanics* of runtime and compiler, which hold for every strategy
    profile;
  - where the mechanics allow more, *dominance*, which holds whatever others
    do;
  - otherwise, the *equilibrium* that Theorem 3 constructs.

  The third tier is a property of that constructed SE, not of every SE. For
  example, send times and handle slots remain mechanically available as
  signals; the constructed SE gives them no meaning.

Section 6 relates Theorems 1 and 2. Section 7 explains what the proofs need
from each change. Section 8 states what the compiler implements. Section 9
lists what is open.

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
| execution order | A partial order on events; an event is ready once its predecessors complete (4.1). |
| Stage S | The execution order equal to program order: events run one at a time. |
| phase | A maximal run of owned events of one kind, not interrupted by a sample (4.1). |
| reset | Under concurrency, voiding a commit phase's bindings after one of them fails, and re-running it (4.1). |
| guard reads | The data a guard depends on (1.1). |
| missed binding | Expiry of a commit event without an accepted binding. |
| raw menu | Everything a player may emit at an activation (1.2). |
| late packet | A packet for an event sent after its owner's protected turn. If it is sent at a clock $s$ with $s+\mathit{bound}_e\ge r_e+d_e$, protected inclusion is vacuous for it, and it may be omitted (1.2, 2.3). |
| protected turn | The owner's first activation while its event is ready. |
| charged packet | A packet the audit charges (1.3). |
| clean history / set | A history in which nobody emitted a charged packet; an information set that contains a clean history (5.2). |
| $m_j$ | The minimum of $j$'s gross payoff over compiled terminal histories in which $j$ is not excluded (1.3). |
| $\Gamma^X$ | The source game with exclusion (the X stands for exclusion; compare $\Gamma^H$, the honest game): the source's full commit menu, deferred guards, failure and exclusion (1.6). |
| guard obligation | A guard retained at a commit and checked at the reveal that completes its reads (1.1). |
| publicly doomed | A player whose published values admit no guard-satisfying assignment of its hidden commitments, so that a later reveal of its must fail (1.6). |
| privately doomed | A player whose own commitments admit no guard-satisfying assignment; it knows this, others may not (1.6). |
| $(\sigma^X,\mu^X)$ | The SE of $\Gamma^X$ of Proposition 1, with tremble sequence $\sigma^X_n$ (1.6). |
| lifted region | Clean native sets after an exclusion or with a publicly doomed player, where Theorem 3 plays the lift of $\sigma^X$ (4.4). |
| $\rho_n$ | The smallest positive probability that an honest tremble profile or Nature gives to any action (1.4). |
| guard satisfiability | The standing assumption that every commit's guard admits a value at every reachable public history (1.5). |
| tiers M, D, E | Mechanics, dominance and equilibrium: the three strengths of Theorem 4 (5.2). |
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

**Deferred guards (source semantics).** A commit stores any value of its
domain, and keeps its guard as an **obligation**. At a reveal, every obligation
that this reveal completes is decided:
- if one rejects, the *current* reveal's result is $\mathsf{fail}$;
- earlier published results stand.

So "commit $y=1$ against the guard $y=x$, publish $\mathsf{ok}(1)$ at the
reveal of $y$, then fail at the reveal of $x$" is ordinary source behaviour.
The runtime contract reproduces exactly this (1.2). It adds no earlier check.

Programs start from the **empty context**: no initial private inputs, no
initial commitments and no prior. Every commitment is revealed.

The **honest game** $\Gamma^H$ is the finite extensive-form game in which:

- each commit is a move of its owner, who chooses a value that its guards
  will accept;
- each reveal publishes;
- samples are chance moves.

A player's information set in $\Gamma^H$ is determined by the public results
and their own commitments. Write
$[\underline u_i,\overline u_i]$ for the range of $u_i$ over terminal
histories of $\Gamma^H$.

### 1.2 The ledger runtime

**Clock and events.** Time is a public clock in **slots**. Sections 2 and 3
use Stage S: events run one at a time in program order. Section 4 allows any
information-respecting execution order. An owned event $e$ becomes **ready**
at the clock $r_e$ when its predecessors complete. It completes in one of two
ways:

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
  records $\mathsf{fail}$ in two cases: the value lies outside the binding's
  domain (a wrongly typed binding), or an obligation that this reveal
  completes rejects. Otherwise it records $\mathsf{ok}(v)$, exactly as the
  source semantics does (1.1). Earlier published results stand.

An included opening is observed in full even when its result is
$\mathsf{fail}$. So a guard-rejected or out-of-domain opening publishes its value
*de facto*, though not as a result.

An opening whose value does not match is not accepted.

**Mempool and leaks.** An emitted packet is *pending* until it is included.
At each activation of $i$, the builder may *show* $i$ some pending packets of
other players. Showing a packet reveals its identifier, call and evidence.
This is the mempool: the model allows any pending packet to be shown to any
player before inclusion, and nothing in this note assumes pending packets
are private. Bindings are opaque, so seeing one reveals no value. A pending
opening reveals its value to whoever is shown it.

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
  one. Under concurrency this is required **per event**: the law concerning
  event $e$ may read the value of $e$'s own opening, but no other unopened
  value;
- **content-blind** (in its leaks) if which pending packets are shown to
  whom, and when, depends only on the history, the observer and the emitters
  of the pending packets, and not on their calls or evidence. A shown packet
  is still shown in full; the property restricts the choice of what to
  show, not what showing reveals;
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
  failed or unopenable opening, a reveal whose completed obligation rejects,
  or an expiry. Player $j$ is then **excluded**:
  - each later event of $j$ completes as a failure, without becoming ready
    for $j$. Such an automatic failure is not part of any phase: it
    triggers no reset (4.1), and it is not a failure for the phase-success
    event $\Phi$ (1.6);
  - $j$'s gross payoff is a fixed $a_j$;
  - every other player $i$ continues, and receives $u_i$ evaluated on the
    public results, in which every excluded player's later results are
    $\mathsf{fail}$.

  Theorem 2 requires $a_j<\underline u_j$. That forfeit, $\underline u_j-a_j>0$,
  may be arbitrarily small. Theorems 3 and 4 require $a_j<m_j$, where $m_j$ is
  the minimum of $j$'s gross payoff over all compiled terminal histories in
  which $j$ is not excluded. Those include histories in which others were
  excluded and $u_j$ reads their failures. The bound $m_j$ depends only on the
  payoffs.
- *Count audit.* A packet is **well-formed** for event $e$ if three things
  hold:
  - its emitter owns $e$;
  - it carries a valid token for $e$;
  - its call is correct for $e$. For a reveal, that means the opening of the
    bound value, which must lie in the binding's domain, with exactly its own
    certificate. For a commit, it means a binding with a fresh handle of the
    emitter and no evidence.

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

  *Enforcement.* Because a player is charged at most once, the count audit
  is the same as the rule: **a player may sign at most one packet per move,
  and it must be well-formed.** Which of two packets counts as "first" never
  matters. Every violation is proved by signed data alone, as in
  double-signing slashing:
  - two distinct packets that the player signed for the same event, with
    different serials or contents, prove an extra packet;
  - a single signed packet proves itself if it is malformed, carries
    evidence other than an opening's own certificate, or addresses an event
    its signer does not own.

  Non-inclusion alone is never chargeable: a packet that never lands proves
  nothing against its sender by that fact. A charge needs signed evidence of
  a violation, and then it applies whether or not the packets involved were
  included. Two signed packets for one move are charged even if neither
  landed. That is the difference from $C_0$'s audit, which charges every
  packet that was not accepted. Rebroadcasting the same signed
  packet, by its author or by anyone else, creates no second packet. To fit
  real fee markets, the signed packet must be separate from the fee-bearing
  transaction that carries it, so that a client can re-wrap and re-price it
  without signing again. The model leaves fees out (1.2); a fee bump is then
  a rebroadcast of the same packet, not a second one. What the audit cannot
  do by itself is *obtain* the packets. That is the reporting assumption,
  1.5(4).
- *Deposit.* $\alpha K_i>\operatorname{sp}_i$, where $\operatorname{sp}_i$ is
  the spread of $i$'s gross payoff over all compiled terminal histories.

Under concurrency, $C_1$ also performs the **phase reset** of 4.1.

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

**Tremble notation.** For a tremble sequence $\sigma^H_n$ of an honest SE,
$\rho_n$ denotes the smallest positive probability that $\sigma^H_n$ or Nature
gives to any action, and $\mathcal T$ is the horizon (1.5).

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
   horizon of at most $\mathcal T$ moves. Under concurrency, $\mathcal T$
   includes the re-runs of at most $n$ resets, since each reset excludes a
   player.
3. Players are finitely many.
4. **Reporting.** Emitting a packet means broadcasting it to the public
   mempool; the model has no private channel to the builder. Leaks (1.2)
   govern what a *player* has seen by the time it acts, not what eventually
   becomes public. So every emitted packet can eventually be obtained and
   reported. The charge needs no trust, because it is proved from signed
   packets (1.3, Enforcement). The assumption is that a charged packet is in
   fact reported and collected with conditional probability at least
   $\alpha$ (1.3). No reward for reporting is modelled; see 1.7.
5. **Guard satisfiability.** At every reachable public history of $\Gamma^X$
   (1.6), every commit's guard admits some value of its domain, given its
   owner's information.
   - Failed inputs never block this. An obligation accepts whenever its
     *successful* results are compatible with its code, so a guard is vacuous
     on a failed input. In Lean this is
     `Vegas.SourceProgram.Obligation.accepts_of_compatible`.
   - The assumption therefore concerns *published violating values*: a guard
     that reads another player's published value must still admit a value
     when that published value is one that no honest play produces.
   - The assumption is used by the honest game, by $m_j$, by D2, and wherever a
     non-excluded continuation is claimed to be worth at least $m_j$.

### 1.6 The source game with exclusion

Fix an execution order (Stage S, or an information-respecting order of 4.1).
Let $\Gamma^X$ be the following finite game.

- **Moves.** Events run phase by phase as in 4.1 (one at a time under Stage
  S). At each of its own events a player either moves or **fails**:
  - at a commit, the move is *any* value of the domain, with guards deferred
    exactly as in the source semantics (1.1); failing means missing the
    binding;
  - at a reveal, the move is to open; the result is $\mathsf{fail}$ if a
    completed obligation rejects; failing means not revealing.
- **Simultaneity.** Within a phase, owners move without observing other
  owners' choices in that phase, including failures. They observe all results
  of earlier phases. A player's own earlier choices are known to it.
- **Exclusion.** A player whose event fails, including through a rejected
  obligation, is excluded exactly as in $C_1$:
  - all its later results are $\mathsf{fail}$;
  - its payoff is the fixed $a_j$;
  - every other player receives $u_i$ on the public results, with every
    excluded player's later results failed.
- **Reset.** Under concurrency, if an active owner's commit fails, the
  phase's other commits are voided, with their guard obligations. Their
  owners commit again in a fresh phase. An excluded player's events are not
  part of any phase, so their automatic failures trigger no reset.

$\Gamma^X$ contains no blockchain detail: no clocks, packets, builder or
mempool. Compared with the honest game, it adds three things: the source's
full commit menu (guard-violating values included, with deferred guards), the
meaning of failure, and the reset. The honest game is the part of $\Gamma^X$
in which nobody fails and nobody commits a value that its guards will reject.
The **honest region** of $\Gamma^X$ is defined below from the record an
information set's owner observes. The counterpart property shows that every
honest-region set is reachable by honest play.

A player is **publicly doomed** at a history if its published values admit no
guard-satisfying assignment of its still-hidden commitments. Guards and
domains are public, so this is a function of public data. A publicly doomed
player will fail at a later reveal of its own. A hidden guard violation that
is not yet publicly doomed is invisible to others: every public record it
produces is also produced by some honest assignment.

A player is **privately doomed** if its own commitments admit no
guard-satisfying assignment. It knows this, others may not, and publicly doomed
implies privately doomed. Under Stage S a privately doomed player will fail at
a later reveal of its own. Under concurrency, a failure of another binding in
the same commit phase can void the violating binding through the reset. So
there "will fail" holds unless such a reset intervenes.

**Regions of $\Gamma^X$.** A set's region is determined by what its owner
observes: the results of earlier phases, and its own choices. Failures inside
the current phase are not observed (simultaneity). Each set falls in the first
region that applies:

1. **post-exclusion**: an exclusion is observed;
2. **doomed**: some active player is publicly doomed by the observed results;
3. **privately doomed**: the owner itself is privately doomed;
4. **honest region**: all other sets.

Separately, call a set **own-doomed** if its owner is privately doomed,
whatever its region. Regions 1–2 are *public*: they are functions of the
observed results. Whether a set is own-doomed is private.

**Counterpart property.** Every honest-region set $I$ contains a history with
no failure and no violation. To see this, take any history in $I$ and modify
it in two ways:
- *Other players' violations.* A violator is not publicly doomed, so its
  published values admit a guard-satisfying assignment of its hidden
  commitments. That assignment is *sequentially honest*: a joint assignment
  satisfying all of its guards satisfies each commit's guard given the data at
  that commit, because guards read only data available at the commit.
  Replacing the violator's hidden values with it gives a history with the same
  public record.
- *Unobserved failures.* A failure inside the current phase is not observed.
  Replace it by an honest move.

The owner's own choices are honest, since it is not privately doomed.

**Proposition 1 (an SE of $\Gamma^X$ extending the honest SE).** Fix an honest
SE $(\sigma^H,\mu^H)$ with tremble sequence $\sigma^H_n$.

1. If $a_j<\underline u_j$ for every $j$, then $\Gamma^X$ has an SE
   $(\sigma^X,\mu^X)$ such that:
   - on the honest region, play is $\sigma^H$: nobody fails and nobody
     violates;
   - on the honest region, beliefs about other players' values are $\mu^H$.
2. If $a_j<m_j$ for every $j$, the SE can moreover be chosen with
   **never fail**: at every information set, every player fails with
   probability zero. Moreover, at every stage $n$ of the construction, the
   probability of failing at a set depends only on the set's public region,
   not on its owner's values or on whether it is own-doomed.
3. Under concurrency, its value choices are **optimal given phase
   success**, defined below.

The same $(\sigma^X,\mu^X)$ serves all three parts. Parts 2 and 3 are
properties of the construction.

**Phase success.** At a commit set $I$ of $j$, write $\Phi$ for the event
that no binding of another active owner in the current phase fails.
Excluded owners' automatic failures are not counted; they are not part of
the phase. Every binding that $\Phi$ does count is a choice of an active
owner, and at every stage $n$ the profile is fully mixed, so
$\Pr_n(\Phi\mid I)>0$.

Conditioning on $\Phi$ changes more than beliefs about the past. It also
changes the law of other owners' choices later in the same phase, and it
does so jointly with their earlier private choices. Given $\Phi$, *every*
binding of each other owner in the phase succeeds. That conditions the
owner's whole trajectory, not each move separately, and keeps each later
choice's dependence on the owner's earlier private choices (a guard $y=x$
correlates them perfectly). In a general profile, failures could also
select: an owner that fails its second binding iff its first value was $0$
has first value $1$ given $\Phi$. The forced rule for own-doomed agents
rules out such selection in $\sigma^X_n$, since failure rates depend only on
the public region, but the definition below does not rely on it. So the
object to carry is the whole **phase outcome**
$\omega$: the hidden values of the active players other than $j$, and their
choices in the current phase, as they stand when the phase ends, earlier
hidden values included. Write
$$
\nu^X_n(I)=\Pr_n(\omega\in\cdot\mid I,\Phi),\qquad \nu^X(I)=\lim_n\nu^X_n(I),
$$
along the subsequence below, chosen so that these limits exist too. $j$'s
own choices are not part of $\omega$: given the public record at the start
of the phase they are independent of $\omega$, and others never observe them
within the phase, so $\Phi$ does not distort them. When $\Pr(\Phi\mid I)>0$ in
the limit, $\nu^X(I)$ is just the limit law conditioned on $\Phi$. When it is
zero, conditioning the limit is undefined, but $\nu^X(I)$ still is.

After the phase ends nothing is conditioned any more. For a $\Gamma^X$
history $h$ at the end of the phase, a node rather than an information set,
let $U(h)$ be $j$'s expected payoff from $h$ under $\sigma^X$. For a value
$v$, let
$$
W_I(v)=\mathbb E_{\omega\sim\nu^X(I)}\bigl[U(h(v,\omega))\bigr],
$$
where $h(v,\omega)$ is the end-of-phase history with $j$'s commitment $v$,
the outcome $\omega$, and $j$'s later choices in the phase drawn from
$\sigma^X$. Part 3 says: every value that $\sigma^X$ plays at $I$ with positive
probability maximizes $W_I$.

*Construction.* For each $n$ define a constrained agent-form game on
$\Gamma^X$. Every information set is an agent with its own menu.

- **Honest-region agents are forced.** Their behaviour is
  $\sigma^H_n\cdot(1-\eta_n-\eta_n^2)$ on honest actions. Failing gets
  $\eta_n$, the same at every set and for every value. Guard-violating values
  share $\eta_n^2$ uniformly. A set with no guard-violating value (every
  reveal, and a commit whose guards accept every value) has nowhere to put
  $\eta_n^2$; there honest actions get $\sigma^H_n\cdot(1-\eta_n)$.
- **Own-doomed agents are forced**, in every region. They move, with the
  value drawn from a fixed law of full support on the domain. Failing gets
  $\eta_n$ in regions 3–4 and $\eta_n^{M_1}$ in regions 1–2, the same as the
  non-doomed agents of that region (Part 2 shows those use exactly these
  rates). This takes precedence over the two other rules.
- **All other agents are free.** They choose any behaviour that gives every
  action probability at least $\eta_n^{M_1}$, for a fixed exponent
  $M_1\ge2$. Part 2 below needs the minimum to be $O(\eta_n)$, which this gives.

*Why own-doomed agents may be forced.* For an own-doomed player, moving
weakly dominates failing, and its value is irrelevant, pointwise:
- failing excludes it now, for $a_j$;
- after moving, it is either excluded later, for $a_j$, or rescued by a
  reset that voids its violating binding (under concurrency, only while that
  binding's phase is open). A rescued player is not excluded by that
  binding, and its payoff is at least $a_j$, since every gross payoff is
  either $a_j$ or a non-excluded payoff of at least $m_j>a_j$. Under Stage S
  there is no reset, so its payoff is $a_j$ whatever it does, and Part 1
  needs no more. Under concurrency the rescue case uses $a_j<m_j$, which
  Theorems 3 and 4 assume;
- the value it chooses either stands next to a binding that excludes it, or
  is voided with it.

So the forced rule is optimal at every own-doomed set, at any belief. It
also makes failure uninformative: whether an agent fails does not depend on
whether its owner is doomed.

The sequences satisfy two conditions:
$$
\eta_n=o(\rho_n),\qquad \eta_n^2=o(\rho_n^{\mathcal T}).
$$

Each free agent's payoff is continuous in the profile, and its constrained
strategy set is a nonempty compact convex polytope. Best responses to Bayes
beliefs, which are well defined because the profile is fully mixed, have
closed graph and convex values. So the constrained game has an equilibrium
$\sigma_n$ by Kakutani's theorem. Pass to a subsequence along which $\sigma_n$
and its Bayes beliefs $\mu_n$ converge, to $(\sigma^X,\mu^X)$, and along
which the conditioned laws $\nu^X_n(I)$ of the phase outcome at commit sets
converge too (Part 3). There are finitely many sets, so one subsequence serves.

*Consistency.* $(\sigma^X,\mu^X)$ is the limit of Bayes beliefs of fully mixed
profiles, with Nature's laws fixed. This is Kreps–Wilson consistency.

*Beliefs on the honest region.* Take an honest-region set $I$.
- It contains a history with no failure and no violation. Its weight is at
  least $\rho_n^{\mathcal T}$ times factors common to the set.
- A history in $I$ in which another player violated carries a factor
  $\eta_n^2$. Its counterpart, with the same public record and a sequentially
  honest assignment (counterpart property), may need up to $\mathcal T$ of
  that author's earlier honest choices to differ. So it weighs at least
  $\rho_n^{\mathcal T}$ times the same common factors. The violator's own
  moves after the violation are at own-doomed sets, each with probability at
  most $1$. Other players' sets and regions are the same in both histories, so their
  factors cancel. Since $\eta_n^2=o(\rho_n^{\mathcal T})$, violating histories
  get zero limit weight.
- A history in $I$ with a failure has it inside the current phase, unobserved,
  since an observed failure would put $I$ in the post-exclusion region. The
  failure carries a factor $\eta_n$ against at least $\rho_n$ for the honest
  move in its place. Since $\eta_n=o(\rho_n)$, these histories also get zero
  limit weight.
- On the remaining histories play is $\sigma^H_n$ times a factor
  $(1-\eta_n-\eta_n^2)$ or $(1-\eta_n)$ per move. Which one applies at a
  commit can depend on its owner's hidden values, through its guards. The two
  differ by a ratio $1+O(\eta_n^2)$, and a history has at most $\mathcal T$
  moves, so the factors agree across the set up to $1+o(1)$. So the
  posterior over other players' values is $\mu^H_n(I)$, up to a factor
  $1+o(1)$, and its limit is $\mu^H(I)$.

*Sequential rationality on the honest region.* By the one-shot deviation
principle for consistent assessments (Hendon, Jacobsen and Sloth 1996), it
suffices to compare single deviations at an honest-region set $I$ of player
$j$, with everyone following the limit profile afterwards.

- **Following $\sigma^H$.** Under the limit profile nobody fails and nobody
  violates on the honest region, so play stays in it. The continuation is the
  honest one, with expected value $V^H\ge\underline u_j>a_j$.
- **Another honest action.** It also keeps play in the honest region and yields
  that action's honest continuation value. That value is at most the value of
  $\sigma^H$'s actions, by sequential rationality of $(\sigma^H,\mu^H)$ at the
  honest information set with the same beliefs.
- **Failing** yields $a_j$, since $j$ is excluded.
- **Violating** makes $j$ privately doomed.
  - Under Stage S, every commitment is revealed, so $j$ fails at the reveal
    that completes the violated obligation, or earlier. It is then excluded,
    and its payoff is $a_j$ whatever happens in between.
  - Under concurrency, the violating binding is voided only if another binding
    of the same commit phase fails. With $\mu^X$-probability one, the other
    owners of the phase are at honest-region sets: they hold no violation and
    observe no failure. There they fail with probability $\eta_n\to0$. So the
    deviation yields $a_j$ in the limit.
  - A privately doomed $j$ cannot buy a reset with its own failure, since its
    own failure excludes it.

  Neither comparison depends on how the free agents play.

So $\sigma^H$ is optimal at $I$.

*Sequential rationality elsewhere.* At own-doomed sets, the forced rule is
optimal by the dominance above. Every other agent is free. In the
constrained game it plays an exact best response to its Bayes beliefs, subject
to the minimum probability. In the limit, every action that it plays with
positive probability is a best response to $\mu^X$ and $\sigma^X$. That is the
standard argument that limits of perturbed agent-form equilibria are
sequential. With the one-shot deviation principle, this gives sequential
rationality at every free set.

*Part 2: never fail.* Let $a_j<m_j$. At honest-region and own-doomed sets
$j$ fails with probability $\eta_n$ or $\eta_n^{M_1}$, by construction. The free sets need a backward
induction at each fixed large $n$. The induction runs on $j$'s **value**, not
on its failure probability: a free agent of $j$ might violate rather than fail,
and under Stage S a violation also excludes.

For a set $I$ of $j$, write $k$ for the maximum, over all continuations
from $I$, of the number of $j$'s own sets from $I$ on, counting $I$ itself and
re-runs after resets. So $k\ge1$, and $k$ is at most $\mathcal T$ by 1.5(2).
A terminal history counts as $k=0$. Write $\operatorname{sp}_j$ for the spread of $j$'s gross payoff (1.3).

**Claim.** At every set $I$ of $j$, forced or free, at which $j$ is not
privately doomed and has at most $k$ own sets from $I$ on, $j$'s value in the
constrained game at stage $n$ is at least $m_j-c_k\eta_n$. Here
$c_0=0$ and $c_{k+1}=c_k+2\operatorname{sp}_j$, so $c_k=2k\operatorname{sp}_j$.
The case $k=0$ is a terminal history in which $j$ is not excluded, worth at
least $m_j$. The current set's own trembles are what the step from $c_{k-1}$
to $c_k$ pays for: at a final reveal with $k=1$, the value is about
$m_j-2\eta_n\operatorname{sp}_j$, not $m_j$.

*Proof of the claim.* Consider the action "move": a guard-accepted value at a
commit, which exists by guard satisfiability, or "open" at a reveal. After it,
$j$ is still not privately doomed. Each continuation reaches either an own
later set of $j$, which has at most $k-1$ own sets from it on and satisfies the
claim with $k-1$ by the induction hypothesis, or a terminal history in which
$j$ is not excluded, worth at least $m_j=m_j-c_0\eta_n$. Under
concurrency a reset may void $j$'s binding; $j$ then commits again and is still
not excluded. So "move" is worth at least $m_j-c_{k-1}\eta_n$.

- At a free set, $j$ best-responds, subject to the minimum probability
  $\eta_n^{M_1}$ on each of its actions, of which there are at most $\bar c$
  (the largest menu size). Its value is therefore at
  least that of "move", minus $\bar c\,\eta_n^{M_1}\operatorname{sp}_j\le\eta_n\operatorname{sp}_j$ for
  large $n$, since $M_1\ge2$.
- At a forced honest-region set, $j$ plays $\sigma^H_n$ scaled as in the
  construction. Honest actions keep it not privately doomed. Failing and
  violating cost at most $\operatorname{sp}_j$ each, with total probability
  at most $\eta_n+\eta_n^2\le2\eta_n$. So its value is at least
  $m_j-c_{k-1}\eta_n-2\eta_n\operatorname{sp}_j$.

Either way, the value is at least $m_j-c_k\eta_n$. $\square$

With $C=c_{\mathcal T}=2\mathcal T\operatorname{sp}_j$, failing yields
$a_j<m_j-C\eta_n$ for large $n$. So at every free set of a non-doomed $j$,
failing is strictly worse than an available action, by a margin bounded away
from zero. In the constrained game it therefore gets exactly its minimum
$\eta_n^{M_1}\to0$. This uses that the minimum is $O(\eta_n)$, which
$M_1\ge2$ gives. So for large $n$, free agents fail with probability exactly
$\eta_n^{M_1}$, honest-region agents with exactly $\eta_n$, and own-doomed
agents with the rate of their region: the failure probability is a function
of the public region alone.

*Part 3: phase-success optimality.* At stage $n$, the payoff of committing
$v$ at $I$ is $\Pr_n(\Phi\mid I)\,W_{I,n}(v)+R_n$, where $W_{I,n}$ is the
stage-$n$ version of $W_I$. The remainder $R_n$ covers $\neg\Phi$, in which
the reset voids $v$, and it does not depend on $v$:
- a voided value reaches no payoff;
- it tells nobody anything, since others never observe it and it is
  independent of their values;
- $j$'s own later sets differ only by that value, so they face the same
  decision problem, and their constrained values agree.

$\Pr_n(\Phi\mid I)$ does not depend on $v$ either, because others choose
without observing it. A free agent best-responds exactly, so any value it
plays above the minimum probability maximizes $W_{I,n}$. Here
$W_{I,n}(v)=\mathbb E_{\omega\sim\nu^X_n(I)}[U_n(h(v,\omega))]$, with $U_n$ the
stage-$n$ value from an end-of-phase node and $j$'s later in-phase choices
drawn from $\sigma_n$. Then $W_{I,n}\to W_I$:
- $\nu^X_n(I)\to\nu^X(I)$ by the choice of subsequence. This carries the
  conditioned joint law of others' trajectories in the phase, which
  $\sigma^X$ alone would not;
- $U_n\to U$ pointwise, since the value from a node is a polynomial in the
  profile and $\sigma_n\to\sigma^X$, in a finite game;
- $j$'s later in-phase choices converge to $\sigma^X$, and are not
  conditioned. So in the limit every value in the support of $\sigma^X$ at $I$
maximizes $W_I$. At honest-region sets, others fail with probability at most
$\eta_n\to0$ and violators have zero weight, so $\Pr(\Phi\mid I)\to1$.
Then $\nu^X(I)$ is the honest law: $\mu^H(I)$ for the past, and $\sigma^H$ for
others' later choices in the phase. So $W_I$ is the honest continuation
value, and $\sigma^H$ maximizes it by its sequential rationality. $\square$

Two remarks:
- Under concurrency, a violating value can tie with an honest one only when
  the phase is surely reset. The violation is then voided anyway, so this does
  not affect failing.
- Sets at which a player has no move do not arise: an excluded player's events
  never become ready, and an information set exists only where its owner
  moves. $\square$

A player can be excluded only by its own failure or by its own violation. So
under "never fail", every exclusion in $\sigma^X$ is the excluded player's own
doing, through a violation or a failure that is a tremble.

Under the weaker bound alone, "never fail" can break. Take a Stage S program in
which C's reveal precedes A's, with $u_A=-X$ if C's reveal failed and
$u_A=0$ otherwise. Let $a_A=-X/2$. Then $a_A<\underline u_A=0$ but
$a_A>m_A=-X$. After C is excluded, every continuation in which A stays in pays
$-X<a_A$, so A strictly prefers to fail.

### 1.7 Assumptions at a glance, and how realistic they are

Compiler design choices (exclusion, the payoff $a_j$, the one-packet rule,
the reset, the deposit) are not assumptions about the world; Sections 7–8
discuss them. The assumptions are these.

| Assumption | Where | Used by | Realism |
| --- | --- | --- | --- |
| Pending packets may be seen by anyone | 1.2 | all | Not an assumption: the model allows it. |
| Contract guarantees: opportunity, protected inclusion, timeliness, completion | 1.2 | all | Liveness and censorship resistance: an owner's single on-time packet lands within a known bound, whatever others send. Reasonable when deadlines are long against inclusion delays; fails under sustained censorship. |
| Builder is exogenous, with a law known to players | 1.2 | all | Standard for equilibrium analysis. A profit-seeking builder (MEV) is not covered (Section 9). |
| Value-blind builder (per event, under concurrency) | 1.2, 4.2 | Theorems 2–4 | Automatic for bindings, which are opaque. For openings in flight it forbids using a value read from the mempool when handling *other* events. Restrictive against content-aware builders. |
| Content-blind leaks | 1.2 | Theorems 3–4 | Which pending packets reach whom may not depend on their contents. Ordinary gossip roughly fits; selective relaying by content does not. |
| Success separability (S1–S3) | 4.2 | Theorems 3–4 | The strongest builder assumption: a *late* packet's success rests on luck private to its event. Real congestion is correlated (Section 9). It constrains only late, off-path packets; on-time packets are covered by protected inclusion. Example 1 shows that some such condition is needed. |
| Reporting: charged packets are reported and collected with probability at least $\alpha$ | 1.5(4) | D1, Lemma C, hence Theorems 2–4 | Every emitted packet is broadcast, so it can be obtained, and the charge is verifiable from signatures. What is assumed is that someone reports it. Charges are burned, so reporting is not rewarded in the model; a bounty from the slashed deposit is the natural fix (Section 9). The factor $\alpha$ absorbs imperfect reporting. |
| No off-ledger communication | 1.5(1) | all | Unenforceable; a modelling assumption, as is standard. |
| Finite domains and horizon | 1.5(2) | all | Excludes sealed-bid auctions over $\mathbb N$. |
| Guard satisfiability | 1.5(5) | Proposition 1, D2 | A checkable condition on programs. |
| Unforgeable evidence (signatures, binding commitments) | 1.2 | all | Standard cryptographic assumption. |

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

The program has no guards, so deferred guards play no role here.

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
content-blind. It is blind to late packets in its inclusion law: conditioned on
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

An opening call without its own certificate is accepted by the contract when
its value matches (1.2), but the settled audit of $C_0$ charges it (1.3).
Step 1 below treats it as a charged packet.

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

A wrongly typed binding behaves like $\bot$: by the domain check (1.2), its
opening is never accepted with a value.

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

**Theorem 2.** Assume Stage S and the deposit-first order with compiler
$C_1$, and fix:

- any program of 1.1;
- any payoffs $a_j<\underline u_j$;
- any $\alpha>0$ and deposits with $\alpha K_i>\operatorname{sp}_i$;
- any honest SE $(\sigma^H,\mu^H)$;
- any value-blind builder of 1.2. Blindness to late packets is not assumed.

Then some native SE preserves $(\sigma^H,\mu^H)$.

### 3.1 Construction

**Regions.** A *charged action* emits a charged packet. Information sets fall
into three regions:

- **forced**: sets containing a history with no charged action, no
  exclusion, and no publicly doomed player;
- **excluded**: sets after an exclusion or a public doom. Both are functions
  of public data, so these are disjoint from the forced sets;
- **free**: all other sets.

Publicly doomed sets are off the honest path but inside $\Gamma^X$: they are
reached by an ordinary source-level deviation, a guard-violating commit. The
delivery lemma (Lemma B) needs the continuation value after success to exceed
$a_j$. Under Theorem 2's bound $a_j<\underline u_j$ alone, that fails after an
exclusion or a public doom: a player's continuation value can then fall below
$a_j$, as the example after Proposition 1 shows. So Theorem 2 fills the sets
after an exclusion or a public doom with an agent-form equilibrium, and claims
nothing source-level there. Theorem 3, under $a_j<m_j$, lifts the $\Gamma^X$
SE of Proposition 1 there instead (4.4).

**Projection.** A binding is *bad* if one of three things holds:
- its slot holds no value (unopenable);
- it holds a value outside the domain (wrongly typed);
- its value, together with the author's other values, violates one of the
  author's guards.

The third kind is an ordinary $\Gamma^X$ action (1.6). The first two map to
"commit some value of the domain, then fail". The note uses this one mapping
throughout.

A history with no charged action projects to a history of $\Gamma^X$: its
committed values, sample draws and publications, with deferred guards. Let $I$
be a forced set at which player $i$ has a choice (a binding value, or an
opening). Then $I$ projects to a $\Gamma^X$ information set $\Pi(I)$, which
$I$ refines by operational data: activations, receipts, serials, handle slots,
leaks and timing.

At a forced set nobody is publicly doomed. So every public record there is
also produced by an honest assignment. For example, take
`commit x : {0,1}; commit y where y = x; reveal y; ...; reveal x`. If the
author binds $y=1$ and $x=0$, the reveal of $y$ publishes $\mathsf{ok}(1)$,
which is also the record of the honest pair $(1,1)$. The violation shows up
only at the reveal of $x$, which fails. If instead $x$'s domain is $\{0\}$,
the author is publicly doomed once $y=1$ is published, and the set leaves the
forced region.

Now suppose $i$ itself holds a bad binding. Then $i$ will fail at the reveal
that completes the violated obligation, or at the reveal of the unopenable or
wrongly typed binding. At Stage S there is no reset, so $i$'s gross payoff is
$a_i$ in every continuation of $\sigma^*$, and every uncharged action of $i$
is optimal. $\sigma^*$ plays as if each of $i$'s bad bindings held a fixed
honest value, with the exceptions listed below.

This is consistent with Theorem 2's treatment of doom. Once the violation
becomes public, the set leaves the forced region. The excluded region is filled
by an agent-form equilibrium that best-responds to native beliefs, so no
$\Gamma^X$ selection has to be matched. Theorem 3, which lifts $\sigma^X$,
instead plays $\sigma^X_n$ at an owner's own guard-violating sets (4.4).

**The profile $\sigma^*$ on the forced region.**

- *First activation while the event is ready.* The owner sends its free
  packet:
  - for a binding, the value is drawn from $\sigma^H$ at $\Pi(I)$, with a
    fresh handle of the owner, chosen independently of the value, and no
    evidence. On the honest region of $\Gamma^X$ this agrees with
    $\sigma^X$, by Proposition 1. At an owner's own bad binding it is the
    as-if-honest rule above;
  - for a reveal, the packet is the certified opening of the bound value.
- *Late delivery.* If the owner has sent nothing for an unresolved event, it
  follows a fixed policy $\varphi^*$.
  - At each activation, $\varphi^*$ decides whether to send the free packet
    now, so as to maximize the conditional probability that the event
    succeeds.
  - $\varphi^*$, including its tie-breaking rule, is a function of the public
    data, the owner's operational view, and the value being delivered only.
    For a binding it reads no value.
  - A late binding draws its value from $\sigma^H$ at $\Pi(I)$.
- *Bad bindings.*
  - At the reveal of an unopenable or wrongly typed binding, no well-formed
    packet exists, so the owner stays silent.
  - A guard-violating binding may be opened, since both choices exclude the
    owner.
- *Otherwise*, silence. In particular, nothing further is sent after the free
  packet.

**Trembles.** Take the honest tremble sequence $\sigma^H_n\to\sigma^H$, with
beliefs $\mu^H_n\to\mu^H$. Let $c$ bound the menu sizes, and take $\rho_n$ as
in 1.4. At each forced set the perturbed profile is built as follows:

- The prescribed component gets mass $1-\eta_n-\eta_n^2-\eta_n^{M_2}$, and
  inside it honest choices follow $\sigma^H_n$ at the projection. So an honest
  action $x$ has probability $\sigma^H_n(x)(1-\eta_n-\eta_n^2-\eta_n^{M_2})$,
  which is the same rescaling at every set.
- *Timing deviations* get probability $\eta_n$. That is silence at a first
  activation, or the send time that $\varphi^*$ does not choose; each forced
  set has at most one.
- The other native-only uncharged actions share $\eta_n^2$, uniformly. These
  are values outside the honest set, bad bindings and other handle slots.
  Where a set has no such action, the $\eta_n^2$ goes to the prescribed
  component.
- Charged actions share $\eta_n^{M_2}$.

The sequences satisfy four conditions:
$$
\eta_n=o(\rho_n),\qquad \eta_n^2=o(\rho_n^{\mathcal T}),\qquad M_2>2\mathcal T,
\qquad \eta_n^{M_2-2\mathcal T}=o\bigl((\rho_n/c)^{\mathcal T}\bigr).
$$
So a history with a charged action has weight at most $\eta_n^{M_2}$. That is
negligible against any history without one, whose weight is at least
$(\eta_n^2/c)^{\mathcal T}\rho_n^{\mathcal T}$.

The condition $\eta_n^2=o(\rho_n^{\mathcal T})$ handles bad bindings. The
honest counterpart of a bad binding, with the same public record, may have to
change up to $\mathcal T$ of the author's hidden commitments. Take a guard
$y=x_1\wedge x_2\wedge x_3$ with every $x_i=0$ on path, and the deviation
$y=1$. The counterpart then needs $x_1=x_2=x_3=1$, each an honest tremble.

All native-only factors that can differ across types are therefore of the
form $1+o(1)$, uniformly.

**Excluded and free regions.** For each $n$, take an equilibrium of the
agent-form game in which forced sets play the perturbed $\sigma^*$, and all
other sets choose freely with minimum probability $\eta_n^{M_2}$ on every action.
It exists by Kakutani's theorem. Pass to a convergent subsequence of profiles
and Bayes beliefs.

### 3.2 Proof

**Lemma A (forced beliefs are honest).** Two claims hold.

1. At every forced set, the limit belief puts zero weight on histories with a
   charged action. At forced sets at which no reveal is pending, it also
   puts zero weight on histories in which another player holds a bad
   binding.
2. At a forced set $I$ at which no reveal is pending, the belief about
   **other players'** values over the $\Gamma^X$ set $\Pi(I)$ is
   $\mu^X(\Pi(I))$. It puts all its mass on nodes where the others are honest,
   and there it equals $\mu^H$. If the owner itself holds a bad binding, the
   claim still concerns only the others' values. The owner's own commitments
   are known to it.

At forced sets with a pending reveal, only the charged-action part of the
first claim is asserted; Lemma B covers them. The bad-binding part can fail
there. While an unopenable binding's reveal is pending, others may observe
its owner's silence, and the honest counterpart of that silence needs
several timing trembles. Nothing needs it, because while a reveal is pending
the other players' only uncharged action is silence.

*Proof.*

- *Charged actions* are negligible by the choice of $M_2$.
- *A bad binding* carries a factor of at most $\eta_n^2$. Its honest
  counterpart, with the same public record, carries at least
  $\rho_n^{\mathcal T}$ times the common factors, and
  $\eta_n^2=o(\rho_n^{\mathcal T})$. At a forced set nobody is publicly doomed,
  so such a counterpart exists. The two operational records have the same law,
  since well-formed bindings carry no evidence and are opaque. Until the bad
  binding's reveal, its owner times its moves exactly as the counterpart
  does. When no reveal is pending, that reveal has not begun: otherwise it
  would have completed, and a bad binding's reveal fails and excludes its
  owner, which would take the set out of the forced region.
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
- **Adaptive policies.** $s$ may read everything $j$ observes while its
  event is pending. At Stage S nothing else is in flight on a forced history,
  so that is the builder's data about $j$'s own event. It is independent of
  everything the continuation's payoff depends on: others' hidden values (by
  value-blindness, and bindings are opaque), later samples, and later play,
  which reads no timing. So success is independent of the continuation
  payoff given $j$'s information, and the payoff is $P_sV+(1-P_s)a_j$ for
  every such $s$. Under concurrency this fails, and Lemma B3 replaces it.
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

From a forced set at which no other player's reveal is pending, with
probability one under the beliefs (Lemma A), play leaves the forced region
in only two ways: the deviator's own charged action, or the deviator's own
exclusion. (While another player's reveal is pending, the deviator's only
uncharged action is silence, and Lemma C covers the charged ones.) Nobody can make another player fail.
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
- **Own bad binding.** At Stage S there is no reset, so every uncharged
  action yields $a_j$. Silence is the only uncharged action at the reveal of an
  unopenable or wrongly typed binding.
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

## 4. Theorem 3: concurrent execution

This section extends Theorem 2 from Stage S to concurrent execution that
respects the source's information dependence.

### 4.1 Execution orders and the phase reset

An **execution order** is a partial order $\prec$ on the program's events. An
owned event becomes **ready** once all its $\prec$-predecessors have completed.
The order is **information-respecting** if two conditions hold.

1. **Mixed kinds keep program order.** If a commit and a reveal, or a sample
   and any other event, appear in some order in the program, then $\prec$
   orders them the same way. So a commit sees exactly the publications that
   precede it in the program. A reveal that follows a commit in the program
   can be sent before that commit completes only as a charged packet, since it
   has no valid token.
2. **Same owner keeps program order.** Two events of one owner are ordered as
   in the program. So every owner has at most one ready event, which matters
   because one activation emits at most one packet.

Guards read only values their owner knows at the commit, and their deferred
obligations are decided at the author's own reveals (1.1). So guards impose
nothing further.

Consequences:

- Two concurrently ready owned events are of the same kind, with distinct
  owners.
- A **phase** is a maximal run, in program order, of owned events of one kind
  that is not interrupted by a sample. It may contain several events of one
  owner, ordered among themselves, while other owners' events run alongside
  them.
- Execution proceeds phase by phase. Consecutive phases are separated by a
  barrier, and samples are barriers too.
- Stage S is the special case where $\prec$ is the program order.

**Phase reset (part of $C_1$ under concurrency).** Suppose a binding of an
active owner in a commit phase fails, through a missed binding or expiry.
(An excluded owner's events never become ready, are not part of the phase,
and trigger nothing.) Then:

1. its owner is excluded, as in $C_1$;
2. at the end of the phase, every other binding of that phase is **voided**;
3. the remaining owners of the phase commit again, in a fresh commit phase
   with fresh deadlines and fresh events.

A voided binding is never revealed and reaches no payoff. Its guard
obligation is discarded with it. Its free first packet stays uncharged. Any
later packet for the voided event is charged, like any further packet.

Note that another player's clean silence in a commit phase can void your
binding through the reset. That is the reset's purpose.

Reveal phases need no reset, because a reveal is not a decision in the honest
game. A program whose commit phases are singletons (commits in program order)
never resets.

### 4.2 Success separability

For each owned event $e$ with owner $j$, the builder's randomness splits into
a component $\xi_e$ private to $e$, and a remainder.

- **(S1) Success is private.** Whether $e$ succeeds is a function of three
  things:
  - $\xi_e$;
  - the clocks at which $j$ emits packets for $e$, counted from $e$'s
    readiness clock $r_e$;
  - the content of those packets: well-formedness, and for a reveal the guard
    rule.

  $j$'s activations while $e$ is ready are determined by $\xi_e$. The packets
  shown to $j$ at those activations (leaks) come from the remainder.
- **(S2) Independent seeds with fixed laws.** The builder's randomness
  consists of exogenous seeds: one $\xi_e$ per owned event, and a remainder
  seed. The seeds are independent of each other, of Nature, and of the
  players' private randomization. The law of each $\xi_e$ is fixed in
  advance and depends only on $e$, stated relative to $r_e$. An event re-run
  after a reset is a new event, with a fresh seed.
- **(S3) The seed is read only through the event.** $\xi_e$ enters the run
  only as (S1) says: through $j$'s activations while $e$ is ready, and through
  $e$'s success or failure. Everything else the builder does is a function of
  the remainder seed and of the history so far.

(S2) constrains seeds, not endogenous quantities. Choices, readiness clocks
$r_f$ of later events and the remainder's behaviour may all depend on $\xi_e$,
through $j$'s activations, its emissions and $e$'s completion. What (S2–S3)
give is freshness: at any history at which $e$ is unresolved, $\xi_e$ is
independent of everything else in the run given $j$'s activations for $e$ so
far. Nothing before $r_e$ reads $\xi_e$, and afterwards the only
$\xi_e$-dependent data in the history are those activations, which $j$ sees.
In particular the builder cannot show $j$ a signal about $j$'s own future
activations.

The remainder may depend on the whole history, subject to per-event
value-blindness and content-blind leaks:

- *when* an included packet is included, and in what order relative to
  others (for example a stable priority induced by fees, which are not
  modelled);
- activations other than an owner's own while its event is ready;
- clock advances and leaks.

(S1–S3) are an assumption separate from protected inclusion. They say that a
late packet may fail, but neither its failure nor its success is correlated
with anything another player can influence.

The marginal version is not enough, that is, requiring only that each event's
success *probability* be unaffected by others' traffic. If successes can be
correlated through timing, a player who gains from another's failure prefers
anticorrelated timing, and how much it prefers it depends on its continuation
value. (S2–S3) exclude this.

**A builder that meets every condition.** The conditions can be met together.
Fix, for each owned event $e$, a deadline $d_e$, a bound $1\le b_e<d_e$, a
law $L_e$ on $\{0,\dots,\mathit{delay}_e\}$ with
$\mathit{delay}_e+b_e<d_e$, and a probability $p_e\in(0,1]$.
- *Seeds.* $\xi_e$ consists of a draw $D_e\sim L_e$ and independent coins
  $c_{e,0},c_{e,1},\dots$ with $\Pr(c_{e,k}=1)=p_e$. All seeds are
  independent, and the remainder is deterministic.
- *Activations.* The owner of $e$ is first activated at $r_e+D_e$, and then
  at every tick while $e$ is ready. Every other player is activated at every
  tick.
- *Inclusion.* A packet sent at tick $s$ with $s+b_e<r_e+d_e$ (on time) is
  included in that tick. A late packet sent at tick $s$ is included at the
  first tick $t\ge s$ before the deadline with $c_{e,t-r_e}=1$, if there is
  one. The order of packets included in the same tick is left unspecified.
  It does not matter here: the contract accepts the first included packet
  from an event's owner, and on clean histories each owner sends one packet
  per event. The builder never needs to see or rank all pending packets
  together. Protected inclusion asks only that each owner's own on-time
  packet lands in time.
- *Leaks.* At each activation, every pending packet is shown to the
  activated player.

The contract of 1.2 holds: opportunity by $D_e\le\mathit{delay}_e$, protected
inclusion with bound $b_e$, timeliness and completion. The builder is
value-blind, since nothing reads a value, and its leaks are content-blind.
(S1)–(S3) hold:
- whether $e$ succeeds depends only on $\xi_e$, the owner's send ticks
  relative to $r_e$, and the packets' content;
- the owner's activations for $e$ are determined by $D_e$;
- everything else is deterministic given the history.

This shows that the interface is consistent and not vacuous. It does not
show that it is realistic. Late inclusion here is luck private to each
event, while real congestion is shared across events. Correlated shocks
violate (S2), and remain open (Section 9).

### 4.3 Statement

**Theorem 3.** Take the deposit-first order, with compiler $C_1$ including the
phase reset, and fix:

- a program of 1.1 with an information-respecting order;
- payoffs $a_j<m_j$;
- $\alpha>0$ and deposits with $\alpha K_i>\operatorname{sp}_i$;
- an honest SE $(\sigma^H,\mu^H)$, and the SE $(\sigma^X,\mu^X)$ of $\Gamma^X$
  that Proposition 1(2) builds from it, with its tremble sequence $\sigma^X_n$;
- a per-event value-blind, content-blind, success-separable builder satisfying
  the contract of 1.2 (opportunity, protected inclusion, timeliness,
  completion) for every event.

Then some native SE preserves $(\sigma^H,\mu^H)$. This holds for every builder
continuation: after a barrier the remainder's law may depend on earlier data.
The laws of the $\xi$ never change.

The assessment it constructs has one further property:

**(P) Past-blindness.** At every clean native set outside the forced region
(defined in 4.4), the prescribed source-level play is the lift of $\sigma^X$ at
the projected $\Gamma^X$ set. These are the sets after an exclusion or with a
publicly doomed player, including the rest of a phase after an exclusion inside
it. Source-level play means the choice of value, and the choice between moving
and failing.

$\Gamma^X$ has no operational data, so this play reads none, and it is
past-blind automatically. The delivery policy $\varphi^*$ reads only the fixed
law of $\xi_e$, the owner's activations and clock relative to $r_e$, and the
value being opened. Play on the free region may read anything, but the free
region has vanishing weight at every set outside it.

### 4.4 Construction

**Regions.** These replace the regions of Theorem 2. Each set belongs to the
first region that applies:

1. **free**: sets containing no history without charged actions;
2. **lifted**: sets containing a history without charged actions in which
   some player has been excluded, or some active player is publicly doomed.
   They include the rest of a phase after an exclusion inside it;
3. **forced**: all remaining sets. These contain a history without charged
   actions, with no exclusion and nobody publicly doomed.

Exclusions and public doom are functions of public data, so these regions are
well defined. Excluded players' own sets carry a constant gross payoff, and
their only uncharged action is silence.

**The native profile at stage $n$.** At forced and lifted sets the profile is
built from $\sigma^X_n$:

- **Source-level choices.** These are the choice of a value, and the choice
  between moving and failing. They are read from $\sigma^X_n$ at the projected
  $\Gamma^X$ set $\Pi(I)$.
  - $\Pi(I)$ ignores in-phase observations: others' in-phase expiries,
    receipts, leaks, and in reveal phases others' openings. It
    also ignores the owner's own timing, so every activation of the owner for
    one event projects to the same $\Gamma^X$ set. This is the same matching
    map as in Theorem 4.
  - The native profile is specified at every raw activation, as a behaviour
    strategy, not as a plan. Write $\alpha_n=\sigma^X_n(\text{fail})$ at
    $\Pi(I)$. By Proposition 1(2) it depends only on the public region of
    $\Pi(I)$, so it does not depend on the owner's values or on whether it is
    doomed.
  - *First activation* while the event is ready and nothing is sent: send the
    free packet now with probability $1-\alpha_n-\zeta_n$, with its value
    drawn from $\sigma^X_n$ at $\Pi(I)$ conditioned on moving; stay silent with
    probability $\alpha_n+\zeta_n$.
  - *Later activations* while the event is unresolved and nothing is sent
    (**late sets**): do what $\varphi^*$ does, send now or wait, with
    probability $1-\zeta_n$, and the other with probability $\zeta_n$. A late
    send draws its value from $\sigma^X_n$ at $\Pi(I)$ conditioned on moving.
  - So a source-level failure is not "never send". It is silence at the
    first activation followed by late play that never gets included. In the
    limit, every late set follows $\varphi^*$, and every first activation
    sends.
  - On forced sets, $\Pi(I)$ is in the honest region of $\Gamma^X$, or in its
    privately doomed region when the owner holds its own guard-violating
    binding, which is an ordinary $\Gamma^X$ action. Both follow $\sigma^X_n$.
    On the honest region that is $\sigma^H_n$ scaled as in Proposition 1. At
    the owner's own guard-violating sets it is Proposition 1's play there.
  - Native-only bad bindings (unopenable or wrongly typed) are in the
    $\zeta_n^2$ tier below. At commit-phase sets, others' beliefs give them
    zero weight while their owner is active (Lemma A3, part 1). Their
    owner sends on time and otherwise plays as if the bad binding held a fixed
    honest value. Any uncharged choice is optimal for it, by the own-bad-binding
    argument of 4.5.
- **Timing deviations** are the $\zeta_n$ terms above: extra silence at the
  first activation, and a send-or-wait choice that $\varphi^*$ does not make.
  They are the same at every set and for every value.
- **Native-only values** share $\zeta_n^2$. These are unopenable and wrongly
  typed bindings, and handle slots other than the prescribed one.
- **Charged actions** share $\zeta_n^{M_3}$.

Let $\rho^X_n$ be the smallest positive probability that $\sigma^X_n$ or Nature
gives to any action. Choose $\zeta_n\to0$ and $M_3$ such that
$$
\zeta_n^2=o\bigl((\rho^X_n)^{\mathcal T}\bigr),\qquad M_3>2\mathcal T,\qquad
\zeta_n^{M_3}=o\bigl((\zeta_n^{2}\rho^X_n/c)^{\mathcal T}\bigr),
$$
where $c$ bounds the menu sizes. The first condition makes native-only bad
bindings of active players negligible against their counterparts with the
same public record, which may differ in up to $\mathcal T$ earlier choices.
The comparison needs no further timing trembles. Until the reveal of the bad
binding, its owner plays exactly as the honest counterpart does. It draws
the bad value in place of an honest one, at the same callback. Before that
reveal, the two histories carry the same timing factors. The others make
charged histories negligible against clean ones.

**Delivery policy.** $\varphi^*$ is chosen among *own-service* policies. Their
send times depend only on the owner's activations and the clock relative to
$r_e$, and, for a reveal, on the value being opened. A binding's delivery
policy reads no value. From every activation record of $j$ for $e$,
$\varphi^*$ maximizes the event's remaining success probability, computed from
the fixed law of $\xi_e$. A policy that reads more, such as leaks, receipts or
others' openings in flight, can select *which* continuations succeed, so its
payoff is not a function of its success probability alone. Lemma B3(b) shows
that it still does no better than $\varphi^*$.

**Free region.** For each $n$, take an equilibrium of the agent-form game in
which forced and lifted sets play the profile above, and free sets choose
freely with minimum probability $\zeta_n^{M_3}$ on every action. It exists by
Kakutani's theorem. Pass to a subsequence along which the profiles, their
Bayes beliefs, and the conditioned laws of the phase outcome at commit sets
(Lemma A3(2)) converge.

**How native and $\Gamma^X$ weights compare.** For a clean history $h$,
$$
\Pr_n(h)=\Pr{}^X_n(\Pi(h))\cdot N_n(h)\cdot(1+o(1)),
$$
where $\Pr^X_n$ is the $\Gamma^X$ probability under $\sigma^X_n$. The factor
$N_n$ collects four things:
- the builder's draws, the leaks and the collection;
- the timing tier;
- the native-only tier;
- the ratio between the native weight of a failure and its $\Gamma^X$ weight.

*Move and failure weights.* Fix an owned event $e$ at a set with public
region $\pi$. Let $\lambda_n(e)$ be the probability that late play, starting
from silence at the first activation, is never included. It depends only on
the fixed law of $\xi_e$, on $\varphi^*$ and on $\zeta_n$, by (S1–S3), and for a
reveal also on the value being opened. Then natively:
$$
\Pr_n(\text{move with }v)=\sigma^X_n(v)\cdot c^{\mathrm{mv}}_n,\qquad
\Pr_n(\text{fail})=\sigma^X_n(\text{fail})\cdot c^{\mathrm{fl}}_n,
$$
with
$$
c^{\mathrm{mv}}_n=\frac{(1-\alpha_n-\zeta_n)+(\alpha_n+\zeta_n)(1-\lambda_n(e))}{1-\alpha_n},
\qquad
c^{\mathrm{fl}}_n=\frac{(\alpha_n+\zeta_n)\,\lambda_n(e)}{\alpha_n}.
$$
Both factors depend only on $e$, on $\pi$ and on $n$, since $\alpha_n$ does,
by Proposition 1(2). They do not depend on the owner's values or on whether
it is doomed. For a reveal they may also depend on the value being opened,
which is public after a success, and after a failure belongs to an excluded
player. Since $\alpha_n+\zeta_n\to0$, $c^{\mathrm{mv}}_n\to1$ and the native
probability of failing tends to zero.

The native failure weight need not be close to the $\Gamma^X$ one; it is not
compared with it. Every history in an information set has the same publicly
observed results, so the factors of observed moves and failures are common
to the set and cancel in beliefs. Moves and failures within the current
phase that are not yet observed are handled by conditioning on $\Phi$
(Lemma A3), under which they are all moves, with the common factor
$c^{\mathrm{mv}}_n$. Every other part of $N_n$ reads no unopened value:
bindings are opaque, the builder is per-event value-blind, and binding
policies read no value. A failure factor that depends on the value being
opened reads only the failing player's own value, which is payoff-irrelevant
after its exclusion and independent of the active players' values given the
public history.

### 4.5 Proof

**Lemma T (conditional transport).** This lemma isolates the step that
carries beliefs from $\Gamma^X$ to the native game. Fix a native information
set $I$ of owner $j$ in a commit phase. Let $\Phi$ be the event that no
binding of another active owner in the current phase fails. The transported
object concerns the *other* owners only. $j$'s past is part of $I$. $j$'s
choices after $I$ are summed out first, by (T0).

Extend the other owners' play in every history of $I$ to the end of the
phase, and project the clean extended histories to $\Gamma^X$. The public
record up to $I$ is fixed, so a projection is a pair $x=(o,e)$:
- $o$ is the private trajectories of the other owners active at $I$: their
  hidden values and their choices in the phase;
- $e$ is the private choices of excluded owners.

Call an extended history **regular** if it is clean, $\Phi$ holds in it, and
no *other* owner active at $I$ holds a native-only bad binding in it.
Assume, at every stage $n$:

- **(T0) The focal owner can be summed out.** The other owners' choices in
  the phase, the success of their bindings, and $\Phi$ do not depend on $j$'s
  choices after $I$.
- **(T1) Negligible remainder.** The extended histories in $I$ in which $\Phi$
  holds but which are not regular have total weight $o(\Pr_n(\text{regular}))$.
- **(T2) Factorization.** For a regular $h$ with projection $x$,
  $\Pr_n(h)=\Pr^X_n(x)\,N_n(h)\,(1+o(1))$ uniformly. Here $\Pr^X_n$ is the
  $\Gamma^X$ weight under $\sigma^X_n$.
- **(T3) Product form on a product domain.** There are finite sets $O$ and
  $E$ such that the projections consistent with $\Pi(I)$ in which $\Phi$
  holds are exactly $O\times E$, and $\Pr^X_n(o,e)=A_n(o)\,B_n(e)$ on all of
  $O\times E$, with zeros allowed. In particular the excluded choices
  available do not depend on $o$.
- **(T4) The operational factor ignores $o$.** For every $(o,e)\in O\times E$,
  $\sum_{h\text{ regular},\ \Pi(h)=(o,e)}N_n(h)=K_n(e)\,(1+o(1))$
  uniformly, with $K_n$ not depending on $o$. Regular histories project only
  into $O\times E$.
- **(T5) Possibility.** $\Pr_n(\text{regular})>0$.

Then, at every stage $n$, the native law of $o$ given $I$ and $\Phi$ and the
$\Gamma^X$ law of $o$ given $\Pi(I)$ and $\Phi$ are within $o(1)$ in total
variation. So they have the same limits along any subsequence.

*Proof.* By (T0), $j$'s choices after $I$ affect neither $o$ nor $\Phi$, so
they sum to one and drop out. Restrict first to regular histories. By (T2)–(T4),
the native regular weight of $o$ is
$$
\sum_{e\in E}A_n(o)\,B_n(e)\,K_n(e)\,(1+o(1))=A_n(o)\,C_n\,(1+o(1)),
\qquad C_n=\sum_{e\in E}B_n(e)K_n(e).
$$
The sum runs over the same set $E$ for every $o$, by (T3). By (T3), the
$\Gamma^X$ weight of $o$ given $\Pi(I)$ and $\Phi$ is $A_n(o)\,C'_n$, with
$C'_n=\sum_{e\in E}B_n(e)$. (T5) gives $C_n>0$. In $\Gamma^X$, $C'_n>0$ because
$\sigma^X_n$ is fully mixed. After normalizing, the regular native law and
the $\Gamma^X$ law agree up to a factor $1+o(1)$, uniformly in $o$, so they
are within $o(1)$ in total variation. By (T1), the irregular histories add
mass $o(1)$ to the conditional law given $I$ and $\Phi$. That moves it by at
most $o(1)$ in total variation, though not uniformly state by state.
$\square$

The lemma fixes the order of operations:
- the focal owner's own future is summed out, since others never see it;
- excluded owners are summed out over a common domain, so their
  posteriors, which may differ between the two games, never enter;
- nothing is compared history by history;
- each other owner's trajectory stays whole inside $A_n$, so correlations
  within one owner, such as a guard $y=x$, are preserved.

**Lemma A3 (beliefs at forced and lifted sets).** Three claims hold.

1. At every forced or lifted set, the limit belief puts zero weight on
   histories with a charged action. At every forced or lifted set in a
   commit phase, it also puts zero weight on histories in which *another*
   player that is active at the set holds a native-only bad binding. The
   set's owner may hold one itself. It knows this, and every history in its
   set contains that binding. Its choices there are settled by the
   own-bad-binding argument below, which needs no belief transport.

   The bad-binding claim is limited on purpose. A bad binding behaves
   differently from an honest one only at its own reveal, where its owner
   has no valid opening. That reveal is in a reveal phase, where no belief
   claim is made. Afterwards its owner is excluded. There the honest
   counterpart of an observed silence can be rarer than the bad binding. It
   needs a source-level failure or several timing trembles, while the bad
   binding fails at no further cost. So the posterior on an excluded
   player's bad binding need not vanish. Nothing depends on it: an excluded
   player's hidden values reach no payoff, and they are independent of the
   active players' values given the public history.
2. Call $\Phi$ (no other active owner's binding in the phase fails)
   **possible** at a native set $I$ if some clean history in $I$ extends,
   with positive probability and without charged actions, to one in which
   $\Phi$ holds. This does not depend
   on $n$: every stage-$n$ profile gives every player action positive
   probability, and the network's law is fixed, so the support is the same
   at every stage. At every forced or lifted set $I$ in a commit phase at
   which $\Phi$ is possible, define $\nu(I)$ as in Proposition 1: the limit of
   the stage-$n$ native laws, given $I$ and $\Phi$, of the phase outcome
   $\omega$, projected to $\Gamma^X$. Then $\nu(I)=\nu^X(\Pi(I))$. On forced
   sets this is the honest law, by Proposition 1.

   Where $\Phi$ is impossible, no claim is made, and none is needed. Every
   history in which $\Phi$ holds then has a charged action, so in the limit
   some other binding of the phase fails with probability one. The reset
   voids the owner's binding, and every value is optimal. This covers an observed failure, and
   also a failure that is certain before it is observed. For example, A
   missed its protected turn and the network drops every late packet, so A
   will expire, but B has not yet seen the expiry. (Failure means an active
   owner's failure, as in $\Phi$; excluded owners' automatic failures do not
   count and void nothing.)

   Natively, $\Pr(\Phi\mid I)$ need not tend to one even on forced sets, as
   that example shows. In $\Gamma^X$ it does on the honest region. Only the
   conditional law given $\Phi$ is transported.
3. In particular, the owner predicts the others' not-yet-chosen values of
   the phase by $\nu^X(\Pi(I))$, jointly with their earlier hidden values.
   A future value can depend on its owner's earlier private choices: if A
   holds a hidden bit $x$ and commits $y$ under the guard $y=x$, the two are
   perfectly correlated, even on honest paths. So the prediction is a joint
   law, not a product of marginals.

*Why condition on $\Phi$.* B's value matters only if no other binding of
the phase fails (Lemma D3), so $\Phi$ is the event its choice reads. The
claim is stated given $\Phi$ so that the in-phase pattern of moves and
failures, which B may partly observe natively (an accepted binding) but not
in $\Gamma^X$ (simultaneity), drops out of the comparison. Under the
construction of 4.4 that pattern is also uninformative about values, since
failure rates depend only on public data in both games. The conditional
statement does not rely on this, and it is taken as a limit of conditioned
stage-$n$ laws, so it stays defined where $\Phi$ has limit probability zero
natively.

No belief claim is made in reveal phases. There a player may see another's
opening in flight, or its receipt, and so know a value that $\Pi(I)$ does not
record. No decision needs such a claim: a reveal phase has no value choice,
moving versus failing is settled pointwise (D2 of Theorem 4, or the
own-bad-binding argument), and Lemma B3 holds at any belief. This matches
Theorem 2, whose Lemma A asserts honest beliefs only where no reveal is
pending.

*Proof.* **Claim 1.** Charged histories have weight at most
$\zeta_n^{M_3}$ against at least $(\zeta_n^2\rho^X_n/c)^{\mathcal T}$ for a clean
history in the set, so they are negligible by the choice of $M_3$. Take a
history in which another active player $k$ holds a native-only bad binding.
$k$ has not yet reached the reveal of that binding, since that reveal would
have excluded it. Its counterpart replaces the bad value with an honest one,
together with up to $\mathcal T$ earlier choices of $k$. It is in the same
information set: the owner of the set is not $k$, and sees neither $k$'s
values nor $k$'s private choices. It has the same public record and the
same timing, so the same operational factors. The bad binding carries
$\zeta_n^2$ against at least $(\rho^X_n)^{\mathcal T}$, which is negligible by
the first condition of 4.4. The same comparisons hold inside $\Phi$. The
counterpart of a bad-binding history has the same in-phase behaviour, so
the same $\Phi$ status. A charged history in which $\Phi$ holds is compared
with a clean one in which $\Phi$ holds, which exists when $\Phi$ is possible.

**Claim 2** is Lemma T, for the set's owner $j$. Its hypotheses hold as
follows.
- **(T0).** The other owners' in-phase choices are made at native sets whose
  source-level play is $\sigma^X_n$ at the projection. $\Pi$ ignores in-phase
  observations, so that play does not read $j$'s in-phase behaviour. Their
  delivery is own-service. By (S1)–(S3), their bindings' success depends
  only on their own seeds and emissions. $\Phi$ concerns them only. A failure
  of $j$ would trigger a reset, but that comes after the phase's choices,
  which is where $o$ is measured.
- **(T1)** is claim 1, inside $\Phi$.
- **(T2)** is the factorization of 4.4. Native source-level play at a set is
  $\sigma^X_n$ at its projection, including for the others' later in-phase
  choices. So $\Pr^X_n(x)$ is built from the same kernels: each owner's choice
  given its own private history, with Nature's laws.
- **(T3).** In $\Gamma^X$ every choice reads only public data and its owner's
  own commitments. Each public result is a function of one owner's choice
  and earlier public data. So, given the public record up to $I$, the
  constraint "consistent with $\Pi(I)$" is a separate constraint on each
  owner's trajectory, and the weight is a product of per-owner factors.
  $\Phi$ constrains each other owner's in-phase trajectory separately: all
  its bindings succeed. The domain is therefore a product over owners, and
  grouping gives $O\times E$ with $A_n$ for the other active owners and $B_n$
  for the excluded ones. $j$'s own trajectory is fixed by $I$ up to $I$,
  and summed out after $I$ by (T0).
- **(T4).** An excluded owner's private choices enter $N_n$ only through that
  owner's own factors: its native-only and timing trembles, including a bad
  binding, and the builder's treatment of its own events, which may read its
  own delivered values. These go into $K_n(e)$. The other active owners'
  private choices do not enter $N_n$ at all:
  - in a commit phase no opening is in flight (order rule 1), so every value
    $N_n$ could read from earlier phases is already public at $I$;
  - given $\Phi$, every other owner's binding in the phase is a move, so the
    only choices left in $o$ are values. Their operational law is value-free:
    bindings are opaque, the builder is value-blind, binding delivery reads
    no value, and the timing tier is the same at every set and for every
    value;
  - each move carries the common factor $c^{\mathrm{mv}}_n$ of 4.4, which
    depends only on the event, its public region and $n$.
- **(T5).** $\Phi$ is possible at $I$, and possibility does not depend on $n$.

Lemma T gives convergence in total variation at each stage, so the limits
agree: $\nu(I)=\nu^X(\Pi(I))$, along the subsequence of 4.4.

Without $\Phi$, (T4) fails: an observation such as an accepted binding
depends on whether its owner moved or failed, and a doomed owner's choice
between them can depend on its hidden values. Without summing out excluded
owners over a common domain, the comparison would also fail. An excluded
owner's bad binding may dominate its native posterior, and it projects to
one fixed value, while $\Gamma^X$ keeps that owner's earlier choice spread.

**Claim 3** is the part of claim 2 that concerns the others' not-yet-chosen
values. It is a joint law with their earlier hidden values, kept whole in
$A_n$. $\square$

**Lemma D3 (value choice under reset).** Take a forced set in a commit phase
at which owner $j$ chooses a value $v$, together with any own-service delivery
policy. Then $j$'s expected payoff is
$$
\Pr(\text{no failure in the phase})\cdot V^H(v)\;+\;\text{terms independent of }v .
$$
Here $V^H(v)$ is $j$'s honest continuation value of $v$, at belief
$\mu^H(\Pi(I))$. So the honest choice $\sigma^H$ is optimal. (If $\Phi$ is
impossible at $I$ (Lemma A3), the first term vanishes and every value is
optimal.)

*Proof.* There are three cases.

- *$j$'s own binding fails.* Then $j$ gets $a_j$.
- *Some other binding of the phase fails, while $j$'s succeeds.* The reset
  voids $v$. The continuation is the lift of $\sigma^X$ after the reset. Its
  value to $j$ does not depend on $v$:
  - $v$ is never revealed and reaches no payoff;
  - it tells $j$ nothing about the others' values, which are independent of it
    given the public history.
- *No binding fails.* Every value stands, and play continues by $\sigma^H$.
  Conditional on this event, the other values of the phase are still
  distributed by $\sigma^H$, because success is independent of values by
  (S1–S3) and value-blindness. So the conditional continuation value is
  $V^H(v)$ by Lemma A3.

The probability of each case does not depend on $v$. This needs the
in-phase failure rates of the other owners, and of $j$ itself, to be
value-independent. They are: trembles are uniform across values, binding
delivery reads no value, and by (S1–S3) each other owner's success is a
function of its own seed and its own emissions, which do not read $j$'s
choices. $\square$

Without the reset, the second case would keep $v$, and $j$ would optimize
against a mixture that includes another player's failure. That is Example 3.

**Lemma B3 (delivery).** Take a forced or lifted history at which $j$'s
event $e$ is unresolved and $j$ has sent nothing for it. Others in the phase
may be late, or may already be excluded. Let $j$ hold no bad binding. Consider
policies $s$ that send at most the free packet. Call $s$ *own-service* if it
reads only $j$'s activations for $e$, the clock relative to $r_e$, and, for a
reveal, the value being opened. A general policy may read everything $j$
observes, including leaks, receipts and others' openings in flight. Let $P^*$
be the largest remaining success probability of an own-service policy, which
$\varphi^*$ attains. Then:

- (a) every own-service policy $s$ yields $P_s\,V+(1-P_s)\,a_j$, where $V$
  does not depend on $s$ and $V\ge m_j>a_j$. So every type ranks own-service
  policies by $P_s$ alone;
- (b) every policy yields at most $P^*V+(1-P^*)\,a_j$, the payoff of
  $\varphi^*$.

A general policy is not a two-outcome lottery with a fixed $V$. Suppose
another player's bit is uniform, $j$'s continuation after success is worth 1
or 2 according to that bit, and sending surely succeeds. Then always sending
earns $1.5$, while sending only after seeing one of the bits succeeds with
probability $\tfrac12$ and earns $\tfrac12$ or $1$, not $\tfrac12\cdot1.5$. Part
(b) bounds such policies anyway.

*Proof.* Write $Z$ for everything in the run other than $\xi_e$ and $j$'s
choices for $e$: Nature, the players' private randomization (including $j$'s
own later randomization), the other seeds and the remainder seed. By (S2–S3),
$\xi_e$ is independent of $Z$ given $j$'s information at the history. At each
stage $n$ this is Bayes' rule: the likelihood of $j$'s observations factors
into a term in $\xi_e$ (activations so far, and no resolution yet) and a term
in $Z$. The product form survives the limit.

- *Failure* gives $a_j$.
- *Success.* Given $Z$ and the success of $e$, $j$'s gross payoff is a number
  $G(Z)$ that does not depend on $s$:
  - $s$ changes only inclusion timing, order and leaks;
  - the phase's other events succeed or fail as functions of their own seeds,
    their owners' own-service policies or trembles, and their packets'
    content (S1–S3);
  - prescribed play within the phase ignores in-phase observations, because
    it is played at $\Pi(I)$, and after the barrier it is past-blind (P).

  $G(Z)\ge m_j$ for every $Z$, for three reasons:
  - $j$ is not privately doomed, and its prescribed continuation never fails
    (Proposition 1(2));
  - $\sigma^X$ may prescribe a violating value only where the binding is
    surely voided by a reset, and the value after a reset is at least $m_j$
    by never fail;
  - nobody else can exclude $j$.

  So the payoff of $s$ is $a_j+\mathbb E\bigl[(G(Z)-a_j)\,\pi_s(Z)\bigr]$,
  where $\pi_s(Z)$ is the probability that $e$ succeeds given $Z$.
- *Given $Z$, every policy acts as an own-service policy.* By (S3), before
  $e$ resolves, everything $j$ observes is a function of $Z$, of $j$'s
  activations for $e$, of the clock and of $j$'s own emissions. With $Z$
  fixed, $s$ is therefore an own-service policy, and $\pi_s(Z)\le P^*$ because
  $\xi_e$ has its fixed law given $Z$.
- *Conclusion.* For an own-service $s$, $\pi_s(Z)=P_s$ for every $Z$, which
  gives (a) with $V=\mathbb E[G(Z)]$. For a general $s$, $G(Z)-a_j\ge0$ and
  $\pi_s(Z)\le P^*$ give (b).

For a reveal, $P_s$ may depend on the value being opened, which is public
after success, and $\varphi^*$ reads only that value. At lifted sets the
continuation is the lift of $\sigma^X$, which reads no timing. If $j$ itself
holds a bad binding, use the own-bad-binding argument below. $\square$

**Own bad bindings.** Let $j$ hold a bad binding $b$, either native-only or
guard-violating.
- *If $b$'s commit phase has closed without a reset*, $b$ stands. $j$ will be
  excluded at the reveal that $b$ dooms, or earlier. Its gross payoff is $a_j$
  whatever it does, so every uncharged action is optimal.
- *If $b$'s commit phase is still open*, a failure of another binding of the
  phase voids $b$ through the reset. Then $j$ commits again, and its
  continuation is worth $V_{\mathrm{reset}}\ge a_j$. It is at least $m_j$ by
  never fail, unless $j$ holds another bad binding that still stands, in which
  case it equals $a_j$. Either way the conclusion below holds. A delivery
  policy $s$ for $b$ yields
  $$
  P_s\bigl[\pi\,V_{\mathrm{reset}}+(1-\pi)\,a_j\bigr]+(1-P_s)\,a_j ,
  $$
  where $\pi$ is the probability of a co-phase failure. For an own-service
  $s$, $\pi$ does not depend on $s$ (S1–S3), so the payoff is weakly
  increasing in $P_s$. A general policy is bounded as in Lemma B3(b), with
  $G=V_{\mathrm{reset}}$ after a co-phase failure and $G=a_j$ otherwise; both
  are at least $a_j$. Sending on time, or by $\varphi^*$ when late, is
  optimal, and the ranking does not depend on $j$'s type.
- *Choosing a violating value at an honest set* is dominated in the limit,
  since $\pi\to0$ there.

**Lemma C** (charged one-shot deviations do not pay) holds verbatim.

**Sequential rationality.** Single deviations suffice. No player can make
another fail without a charged action: another player's emissions enter
neither $\xi_e$ nor the content of $e$'s packets (S1), and prescribed send
rules are own-service, so they do not react to others' traffic. The cases:

- **Honest value choice in a commit phase.** It is optimal among honest values
  by Lemma D3. Sending at once succeeds surely, by protected inclusion. The
  alternatives are no better:
  - late delivery gives at most $P^*V+(1-P^*)a_j\le V$ (Lemma B3);
  - a bad binding gives $a_j$;
  - charged actions are worse (Lemma C).
- **Reveal at a first activation.** Sending succeeds surely and is worth at
  least $m_j>a_j$, whatever others do in the phase. Withholding gives $a_j$.
  Delaying cannot help, because nothing later reads the timing (P).
- **Late delivery.** $\varphi^*$ is optimal among all policies (Lemma
  B3(b)).
- **After the free packet, non-owners, excluded players.** As in Theorem 2.
- **Own bad bindings.** By the own-bad-binding argument above. At the
  owner's own guard-violating sets, the prescribed play is $\sigma^X_n$'s, and
  its source-level choices are optimal by $\sigma^X$'s sequential rationality,
  as at lifted sets.
- **Lifted sets.** These are the sets after an exclusion or with a publicly
  doomed player, including the rest of a phase after an exclusion.
  - Prescribed moves are $\sigma^X$'s. Native beliefs may be finer than
    $\Gamma^X$'s (Lemma A3), so unconditional continuation values may differ
    between the two games. The argument therefore does not compare them. It
    uses only the following.
  - *Continuations agree pointwise.* Given the values and the public
    history, a $\Gamma^X$ move's native continuation is the lift of
    $\sigma^X$, and its payoff equals the $\Gamma^X$ payoff: moving at the
    first activation succeeds surely (M1), and outcomes map by M2.
  - *Value choices.* Natively, under the limit assessment, committing $v$ at
    $I$ is worth $\Pr(\Phi\mid I)\,W(v)+R$, with $\Pr(\Phi\mid I)$ and $R$
    independent of $v$ (Lemma D3's decomposition, which holds at lifted sets
    with continuation $\sigma^X$). If $\Pr(\Phi\mid I)=0$ in the limit,
    including where $\Phi$ is impossible (an observed failure, or one that is
    already certain), every value is optimal. Otherwise $W(v)$ is the
    expectation, under the limit assessment given $\Phi$, of the native
    continuation value from the end of the phase. With a positive
    denominator, that conditional law of the phase outcome is the limit of
    the stage-$n$ conditional laws, which is $\nu(I)=\nu^X(\Pi(I))$ by Lemma
    A3(2). The native value from the end of the phase is $U$ of its
    projection, by pointwise agreement and past-blindness (P). So
    $W=W_{\Pi(I)}$, and $\sigma^X$'s values maximize it by Proposition 1(3).
  - *Moving versus failing.* Moving is optimal pointwise for a player that
    is not doomed (D2 of Theorem 4), whatever the beliefs. A doomed player is
    covered by the own-bad-binding argument.
  - A runtime deviation is one of three kinds:
    - a $\Gamma^X$ deviation: another value, or failing, which the two
      previous items cover;
    - a timing deviation, which yields at most $P^*V+(1-P^*)a_j\le V$
      (Lemma B3), or $a_j$ for a doomed player;
    - a charged action (Lemma C).
  - **Finer native information.** Natively, $j$ may observe in-phase events
    that $\Pi(I)$ ignores: others' in-phase expiries, receipts, leaks, and in reveal phases others' openings. These do not change what is
    optimal.
    - *Commit phases.* By Lemma D3, $j$'s value matters only when the phase
      has no failure. Given that event, every in-phase observation has a
      likelihood that does not depend on values (Lemma A3). Without the
      conditioning this can fail, because a doomed owner's move can depend on
      its values. So conditioning on the observation leaves the argmax
      unchanged. If an in-phase failure has been observed, $j$'s binding will
      be voided, and any value is optimal.
    - *Moving versus failing.* This is settled by D2 of Theorem 4 when $j$ is
      not privately doomed, and by the own-bad-binding argument otherwise.
    - *Reveal phases.* There is no value choice. A doomed player's payoff is
      constant there, since reveal phases have no reset.

**Consistency.** There is one tremble sequence: the native profile at stage $n$
of 4.4 together with the free-region equilibrium at stage $n$. Every belief is
the limit of its Bayes beliefs. On forced sets in commit phases they are
$\mu^H$. On lifted sets they need not equal $\mu^X(\Pi(I))$; what Lemma A3(2)
gives, and the proof uses, is $\nu(I)=\nu^X(\Pi(I))$, the conditioned law of
the whole phase outcome. Its limits exist along the subsequence of 4.4,
which is chosen for them.

**Preservation.** On the path every owner sends its free packet at its first
activation, which succeeds surely. So no exclusion or reset occurs, and play
follows $\sigma^H$. The joint law of public results and net payoffs is the
honest one. $\square$

### 4.6 Examples showing the conditions are needed

Each example has complete information, so every claimed choice is strict and
every SE makes it.

#### Example 1: coupled late inclusion violates (S1–S3)

The example is fully specified below. It adapts, to $C_1$, a game from an
earlier analysis
([attribution](concurrent-disclosure-se-boundary.md)).

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

#### Example 2: the bound $a_j<\underline u_j$ is too weak under concurrency

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

#### Example 3: a concurrent commit phase without reset

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

## 5. Theorem 4: honest players reason only about the source

Theorems 2 and 3 say that an equilibrium outcome survives compilation. The aim
here is stronger. An honest player, whose client code is compiled from the
program, should never need to understand runtime behaviour. Whatever happens
at runtime should be explained by something that can happen in the source.
The explanation should come from the mechanics wherever possible, and from
incentives only where the mechanics leave room.

### 5.1 The source game

The source-level game is $\Gamma^X$ of 1.6. It contains the source's own
commit menu with deferred guards, failure with exclusion, and under
concurrency the reset. Its equilibrium $\sigma^X$ is the one of Proposition
1(2). That equilibrium has three properties:
- it plays $\sigma^H$ on the honest region;
- no player that is not privately doomed ever fails;
- it is one assessment on all of $\Gamma^X$, including after exclusions and
  public doom, and Theorem 3 lifts it there.

Under Theorem 2's weaker bound, Proposition 1(1) gives an SE of $\Gamma^X$
extending $\sigma^H$, but "never fail" can fail after an exclusion (the example
after Proposition 1). Theorem 2's native construction does not lift
$\Gamma^X$ play after an exclusion or a public doom: it fills those sets with
an arbitrary agent-form equilibrium. So, under Theorem 2's hypotheses alone,
tier E below holds only at sets before any exclusion or public doom.

### 5.2 Statement

Call a runtime history **clean** if no player has emitted a charged packet in
it. Call an information set **clean** if it contains a clean history. The
clean sets are exactly those in the forced and lifted regions of 4.4.

The **matching map** sends a clean set $I$ of player $j$ to an information
set $I^X$ of $\Gamma^X$ at the same event. Every history of nonzero limit
weight in $I$ has the same public results, including failures and resets, and
the same own commitments of $j$. These map to a $\Gamma^X$ public history by
M2 below, together with $j$'s own commitments. A guard-violating binding of
$j$ is itself a $\Gamma^X$ commit. An unopenable or wrongly typed binding of
$j$ maps to "commit some value of the domain, then fail", with one fixed value
chosen per binding. Within the current phase,
$I^X$ records only $j$'s own choices, as simultaneity requires. $I$ refines
$I^X$ by operational data.

**Theorem 4.** Assume the hypotheses of Theorem 3, and let $(\sigma^*,\mu^*)$
be the native SE it constructs. Then the following hold, at three tiers of
strength.

**(M) Mechanics: for every strategy profile.**

- **M1. On-time honest actions succeed.** Suppose a packet is the owner's
  first and only packet for its event, is well-formed, and is sent at the
  owner's first activation while the event is ready. For a reveal, suppose
  also that no obligation this reveal completes rejects. Then the packet is
  accepted before the deadline and the event succeeds, whatever anyone else
  sends.
- **M2. Clean outcomes are source outcomes.** Every clean runtime history has
  the public results and gross payoffs of some history of $\Gamma^X$. Each
  event's result is that of a $\Gamma^X$ move or of its owner's failure:
  - a guard-violating binding is a $\Gamma^X$ commit, and the reveal that
    completes the violated obligation fails, as in the source semantics;
  - an unopenable or wrongly typed binding is followed by a failed reveal, so
    it maps to "commit some value of the domain, then fail".

  Resets map to $\Gamma^X$ resets.
- **M3. Clean packets carry no evidence about unopened values.** Two parts:
  - The only evidence a clean packet carries is an opening's own certificate,
    for the value being delivered. Bindings carry none.
  - The builder's laws, the leak rule and audit collection read no unopened
    value other than the value of the opening being delivered.

  Two consequences follow:
  - At a set where $j$ has a commit choice, no reveal is pending, by order
    rule 1. So $j$ holds no certified unopened value of an active player:
    every certified value it has seen was published or belongs to an excluded
    player. That includes the value of an included opening whose result is
    $\mathsf{fail}$ (guard-rejected or out of domain). It is seen in full, so
    it is published *de facto*, but its author is excluded.
  - *Uncertified* signals remain mechanically possible. A player can choose its
    handle slot or its send time as a function of its values. Tier E (E5)
    deals with them.
- **M4. Nobody's clean actions affect another's success or charges, once
  that owner's emissions are fixed.** Fix the owner's emissions for its event
  (which packets, and at which of its activations). Then:
  - for an on-time packet, success is M1, under every execution order;
  - for a late packet it follows from (S1–S3): success depends only on
    $\xi_e$, whose law is fixed, and on those emissions.

  The qualifier matters. An owner whose send rule reads others' traffic, say
  "send only if A's opening has been seen", lets A's emission change its own
  emissions, and so its success. That is the owner's own choice. Tier E
  shows it gains nothing (Lemma B3(b)), and in $(\sigma^*,\mu^*)$ send rules
  are own-service, which no other player's traffic reaches.
  - Charges attach to the emitter.
  - The one effect another player's clean action can have is to void your
    binding, by failing in your commit phase and so triggering a reset. That
    is a $\Gamma^X$ reset (M2), not an effect on success.

**(D) Dominance: guaranteed incentives, whatever the others do.**

- **D1. Charged packets never pay.** Suppose $j$ is uncharged at an
  information set. An action that emits a charged packet yields at most
  $\max\mathrm{gross}_j-\alpha K_j$. Every clean continuation yields at least
  $\min\mathrm{gross}_j$, which is larger. So disclosures, junk, extra copies
  and malformed packets are never sent by a rational player.
- **D2. Failing at an on-time turn never pays.** Suppose $j$ sends its free
  packet now, and sends on time, with guard-accepted values, at every later
  turn of its own. Then $j$ is
  never excluded, unless $j$ holds a bad binding. So it receives a
  non-excluded payoff of at least $m_j>a_j$, whatever others do, and
  failing (which gives $a_j$) is worse. This holds even after $j$ has seen
  others' openings in flight before its own reveal, so front-running a reveal
  gains nothing.

  D2 compares sending with *failing*. It does not compare sending now with
  sending *later*: against others who read timing, delaying could pay. That
  comparison is tier E.

**(E) Equilibrium: in $(\sigma^*,\mu^*)$, at clean sets.** Limit beliefs at
clean sets put zero weight on unclean histories (Lemma A3).

- **E1. Beliefs are source beliefs.** Take a clean set $I$ at which the owner
  has a value choice, with no failure observed in its phase. What its value
  choice reads is the law of the phase outcome (others' unopened values and
  their choices in the phase) given that no other binding of the phase
  fails, taken as a limit of conditioned laws ($\nu$, Lemma A3). That law is
  the one at $I^X$ in $\Gamma^X$. It includes a prediction of others'
  not-yet-chosen values, jointly with their earlier hidden values, given
  that all their bindings in the phase succeed. Where $\sigma^X$ fails
  surely, that prediction comes from the tremble sequence. The unconditioned belief may be finer: an
  accepted binding in the phase shows that its owner moved, and a privately
  doomed owner's move can depend on its hidden values (Lemma A3). Values seen in included openings whose result is
  $\mathsf{fail}$ belong to excluded players. By the product structure they say
  nothing about active players' values. Two special cases:
  - for an owner holding its own bad binding, value choices are irrelevant.
    After the bad binding's phase closes, its payoff is $a_j$. Before that,
    only delivery matters, and sending on time is optimal (4.5, own bad
    bindings);
  - in a phase where a failure has already occurred, every value will be
    voided, so any value is optimal.

  Reveal decisions need no belief, because D2 settles them.
- **E2. Play is source play.** At clean sets, prescribed play is $\sigma^X$ at
  $I^X$. This includes an owner's own guard-violating sets. The one exception
  is an owner holding its own native-only bad binding (unopenable or wrongly
  typed), which has no $\Gamma^X$ counterpart of its own. There the owner
  sends on time, and its value choices are irrelevant (4.5). Runtime data
  enters only through the client's choice of *when* to send, $\varphi^*$.
- **E3. Timing deviations are source lotteries.** For an event the owner has
  not yet sent, every own-service deviation in send time (silence, late
  sending, another time) has expected payoff
  $$
  P\cdot V+(1-P)\cdot a_j .
  $$
  This is a lottery between two $\Gamma^X$ outcomes: the honest move, with
  continuation value $V$, and $j$'s own failure. The success probability $P$
  is a runtime quantity, but it enters only as a weight. A send time that
  also reads others' in-flight data can correlate success with the
  continuation, so it is not such a lottery. It is bounded by the best of
  them, $P^*V+(1-P^*)a_j$, which $\varphi^*$ attains. The other uncharged
  deviations map directly to $\Gamma^X$ actions:
  - another value maps to another $\Gamma^X$ commit: an honest move, or, at
    lifted sets, possibly a violating commit;
  - another handle slot maps to the same move;
  - a bad binding maps to "commit some value of the domain, then fail".
- **E4. Timing reads only the delivered value.** Every type ranks
  own-service send rules by $P$ alone, and none of its other send rules does
  better. So in equilibrium a player's send time is a function of the
  value being delivered (for a reveal) and of operational data, and of
  nothing else it knows. The delivered value is public after success.
- **E5. Cheap talk carries no meaning.** Handle slots, send times and
  inclusion order carry no information about any active player's unopened
  value at a clean set with a value choice, beyond what the fact that its
  owner moved reveals. Observers' beliefs ignore them
  (E1), and prescribed play never reads them (E2).

### 5.3 Proof

**M1.** Opportunity and timeliness give an activation while $e$ is ready, at a
clock $s\le r_e+\mathit{delay}_e$. Protected inclusion needs the packet to be
the owner's only identifier for $e$. It then gives a receipt by clock
$s+\mathit{bound}_e<r_e+d_e$, before expiry. The contract accepts it:

- a well-formed binding has a fresh owned handle;
- a well-formed opening is certified, and by assumption no completed
  obligation rejects.

Other emitters' packets do not void protected inclusion.

**M2.** Run through the contract's outcomes for a clean history:

- an accepted binding: an honest move, or a bad binding;
- an accepted opening: $\mathsf{ok}(v)$, or $\mathsf{fail}$ if a completed
  obligation rejects, exactly as in the source semantics;
- an expiry: a failure.

An unopenable binding has no opening, and a wrongly typed binding's opening is
not well-formed (domain check, 1.3). If such an opening is included anyway, it
records $\mathsf{fail}$ (1.2). Either way the reveal fails. Exclusion and reset
are defined identically in
$C_1$ and $\Gamma^X$. So the payoffs coincide: $a_j$ for excluded players, and
$u_i$ on public results with excluded players' later results failed for the
others.

**M3.**

- A clean packet is well-formed, or is the first packet for its event (also
  well-formed). Well-formed bindings carry no evidence, and well-formed
  openings carry only their own certificate.
- The law clause is value-blindness, content-blind leaks, and the collection
  condition of 1.3.
- The claim at commit-choice sets uses order rule 1: no reveal is in flight
  during a commit phase. Every opening seen earlier either succeeded
  (published) or failed (author excluded).

**M4.** With the owner's emissions fixed: for on-time packets, this is M1.
For late packets, by (S1) success is a function of $\xi_e$, the owner's
emission clocks and the content of its packets. By (S2–S3) the law of $\xi_e$ is fixed, and $\xi_e$ is a seed
independent of every other player's randomization; another player's
emissions reach $\xi_e$'s event only through the remainder, which success
does not read. Charges attach to the emitter by 1.3.

**D1.** This is the computation of Lemma C. It applies at any information set
where $j$ is uncharged, whatever the continuation.

**D2.** By M1, each on-time free packet succeeds. M1 rests on protected
inclusion, which holds on every legal history whatever others emit, charged
packets included. By guard satisfiability (1.5), $j$ can commit acceptable
values at every later commit. So $j$ is excluded only through its own bad
binding. A non-excluded terminal payoff is at least $m_j$ by definition, and
$m_j>a_j$.

**E1 and E5.** At clean sets, Lemma A3 gives zero weight to unclean
histories. At sets with a value choice, it also gives zero weight to active
players' bad bindings. At clean sets with a value choice,
which lie in commit phases, it gives honest beliefs over the projection
before any exclusion or public doom, and $\Gamma^X$ beliefs at doomed sets
and after exclusions.

Cheap-talk channels carry no information because their native law, given
which owners moved, is value-independent:

- handle slots tremble uniformly, at a rate that does not depend on values;
- send times follow $\varphi^*$, which reads only operational data and, for a
  reveal, the delivered value;
- inclusion order is chosen by the value-blind remainder.

So these channels drop out of the factor $N_n$.

**E2.** This holds by construction. At forced and lifted sets, $\sigma^*$
plays the lift of $\sigma^X$ at the projected set. That includes an owner's
own guard-violating sets (4.4). On forced sets of owners without a bad binding
it is $\sigma^H$, by Proposition 1. Native-only bad bindings are the stated
exception. The only runtime-dependent choice is $\varphi^*$.

**E3.** The timing case is Lemma B3: for own-service policies, failure
gives $a_j$, success gives a continuation value $V$ that does not depend on
the policy, and $P$ is the policy's success probability. Other policies are
bounded by Lemma B3(b). The other deviations change only the move or
the handle, which is a $\Gamma^X$ action by M2.

**E4.** This is Lemma B3: $\arg\max P_s$ over own-service policies depends
only on the fixed law of $\xi_e$, the clock and the delivered value, and by
B3(b) no other policy does better.

$\square$

### 5.4 What each tier asks of an honest player

| Runtime phenomenon | Explained by | Tier | What it rests on |
| --- | --- | --- | --- |
| An honest move takes effect | the move itself | M1 | contract (protected inclusion) |
| Outcomes after misbehaviour | a $\Gamma^X$ outcome | M2 | exclusion, reset, deferred guards |
| Evidence about others' hidden values | none exists in clean traffic | M3 | well-formedness, value-blind builder |
| Seeing a failed opening (omitted but leaked, or included with result $\mathsf{fail}$) | an excluded player's irrelevant value | M3 | exclusion, product structure |
| Others interfering with your success | impossible while your client sends by itself; at most a reset of your phase | M4, E3 | protected inclusion, success separability |
| Disclosures, junk, copies | never sent | D1 | deposit $\alpha K_i>\operatorname{sp}_i$ |
| Withholding after seeing others' openings | never chosen | D2 | $a_j<m_j$ |
| Your value choice and your beliefs | the source game $\Gamma^X$ | E1, E2 | equilibrium |
| When to send if late | maximize success; the client automates this | E3, E4 | equilibrium (Lemma B3) |
| Handles, timing, order as signals | carry no information | E5 | equilibrium |

An honest player relies on tiers M and D unconditionally. Tier E is where it
relies on the others playing the constructed equilibrium. Tier E is not only
about off-path events: on the path, value choices and beliefs (E1, E2) rely
on others not signalling through handles or timing (E5), which the mechanics
alone do not exclude.

Theorem 4 covers clean sets only. After an *observed* charged packet, the
client's play is no longer source-level. A player who has already been charged
pays nothing more for further charged packets, because the charge is capped,
so it can disclose its values verifiably at no extra cost. That situation has
no source counterpart. It arises only after a strictly dominated action (D1).

### 5.5 Limits

- **The meaning of failure.** The explanation uses $\Gamma^X$, the honest game
  with the source-level failure rule and the reset. It does not explain
  programs whose own failure branches keep the failing player in strategic
  play. Theorem 1 shows that such programs can require runtime detail, such as
  whether a failed opening was seen, which no source-level event expresses.
- **What the client must know.** The off-path delivery policy $\varphi^*$
  reads the law of $\xi_e$. On the path the client needs nothing about the
  builder.
- **Builder conditions.** The tiers rest on the contract (protected
  inclusion), on value-blindness, and under concurrency on success
  separability. These are assumptions about the chain, not about the source.

## 6. How Theorems 1 and 2 relate

Theorem 1's mechanism has three links:

1. Alice's payoff after a failed reveal depends on Bob's later answer.
2. Bob's answer reads what he saw of the omitted opening.
3. So the timing of a late send is a type-dependent choice. The beliefs this
   forces at the success records make a protected-turn deviation profitable.

Exclusion cuts the first link. $C_0$ also charges a dead first packet. That
makes the cost of a late send depend on the route, which would recreate a
type-dependent choice even after exclusion (Section 7).

## 7. Why the proofs need each change

For Theorem 2, these are obstructions to the proof, not counterexamples.
Theorem 1 is a counterexample only for $C_0$ as a whole, which combines the
first two features below. For Theorem 3, Examples 1–3 of 4.6 are genuine
counterexamples.

- **Exclusion with a fixed payoff.** Without it, link 1 of Section 6 holds.
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
- **The source game includes violations.** A guard completed at a later
  reveal lets a guard-violating binding publish values first and fail later.
  That is source behaviour, so the explanation must use $\Gamma^X$, with its
  full commit menu, rather than the honest game. Sets where a published value
  already dooms its author are inside $\Gamma^X$ but off the honest path. Their
  play comes from an SE of $\Gamma^X$ (Proposition 1), or under Theorem 2's
  bound from the excluded-region equilibrium.
- **Under concurrency** (Theorem 3), three more conditions:
  - success separability, needed by Example 1;
  - $a_j<m_j$, needed by Example 2;
  - the reset, needed by Example 3.

## 8. What the compiler implements

Exclusion, the phase reset and the play of $\sigma^X$ after an exclusion are a
**recovery protocol** that the compiler adds. They are not a compilation of the program's
own failure branches:

- the honest game has no failures, so on its paths none of these rules ever
  fires;
- the preservation target constrains only the honest outcome law and the
  absence of charges on path. Off-path rules are the compiler's to choose, as
  the forfeit and the deposit are.

Under the program's *full* semantics, failures are results and utilities read
them. There a reset would change the meaning, since another player's failure
leaves a commitment standing. So these compilers are correct for programs
whose intended meaning is the honest game. Programs in which failure is
meaningful source behaviour need a different compiler, for example deliberate
withholding with specified consequences.

The recovery rules are part of the public contract, known to all players.
Theorem 4 shows that they are also the whole source-level story an honest
player needs: the source game $\Gamma^X$.

## 9. Open questions and limitations

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
  - the continuation lifts an SE of the corresponding source game, which
    reads only source-level information, as Theorem 3 lifts $\sigma^X$;
  - the excluded player's continuation value is then route-independent and
    below $\underline u_j$.
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
- **Infinite domains**, for example sealed-bid auctions over $\mathbb N$, are
  outside all four theorems.
- **Builder-first order.** If the deposit may depend on the builder's law,
  Theorems 2 and 3 apply unchanged. Whether $C_0$ preserves SE in that order
  is not settled.
- **Mechanization.** No theorem is machine-checked. The finite games,
  information sets and runtime conditions are taken from a Lean formalization,
  and Appendix A maps the names.

**Activations versus a realistic clock.** In the model, the builder
*activates* players: it decides when each player may emit. Real players are
not activated. They send whenever they choose, and what varies is when
blocks and pending packets reach them. A realistic model has a decision
point for every player at every tick. The builder then controls only
information arrival: inclusion and order (miners), and propagation of blocks
and pending packets (gossip). With that clock, the native game is a finite
*factored-observation stochastic game* (FOSG; Kovařík, Schmid, Burch, Bowling
and Lisý, *Artificial Intelligence* 303, 2022). The GameTheory library
formalizes FOSGs (`GameTheory.Languages.FOSG.Game`) with a translation to
extensive form. The note keeps the activation model. A worked draft of the
tick model exists. It was set aside because it changes many statements and
needs its own review. What is known:

- *Artifacts of the activation model:*
  - a builder can deny a player decision points, which a real network cannot;
  - "at most one packet per activation", where a real player may send
    several at once (the extra ones would be charged anyway);
  - the readiness token "attached only while the event is ready". The
    realistic token cites the block that made the event ready, which cannot
    be produced earlier, so no one can send for an event before seeing that
    block. That token stays valid after the event completes, so a first
    packet sent too late would be free rather than charged.
- *Theorems 2–4: open for the realistic clock.* A builder that activates
  every player at every tick does satisfy their conditions, but that
  specialization is not the realistic model. The realistic model also has
  delayed observation of blocks, and readiness tokens that stay valid after
  an event completes. Those bring new information sets and new actions, for
  example a free first packet sent after expiry. The theorems do not cover
  them. Transferring Theorems 2–4 needs its own proof.
- *Expected to hold with ticks, checked informally only:*
  - **Theorem 1**, with relabelled ticks. Bob's extra decision points carry
    no new information, and silence is his only uncharged action at them.
  - **Examples 2 and 3.** The second player's later move comes from a
    one-tick delay before the readiness block reaches it, rather than from
    the activation order.
- *Does not survive as written:*
  - **Example 1.** Its strictness uses the fact that each player has one
    activation before the last tick. With a decision point at every tick, a
    player could send "a little late" and still rescue everyone, so sending
    becomes weakly optimal and an SE without failures exists. A variant
    that treats every late packet alike, and gossips only on-time packets,
    restores the example.

**Questions an external reviewer will ask.**

- *Why is the builder a chance process, not a strategic player (MEV)?* The
  theorems treat the builder as exogenous, with a known law. A builder that
  profits from ordering or censorship is a player with its own payoff, and
  none of the results covers it. Theorem 1 is unaffected, since an exogenous
  builder is a special case. For Theorems 2–4, a strategic builder is
  open.
- *Is value-blindness realistic, given that payloads sit in the mempool?*
  Bindings are opaque, so for them it is only a statement about commitment
  hashes. For openings in flight it is a real restriction: a builder could
  read a pending opening's value and treat it differently. Per-event
  value-blindness still lets the builder read the value of the opening being
  delivered. What it forbids is using that value for *other* events.
- *Can the recovery protocol be implemented?*
  - **The reset** is a contract rule: void the phase's bindings and reopen the
    phase. Its cost is extra rounds, bounded by the number of players.
  - **Collection** with conditional probability at least $\alpha$ needs
    charged packets to be reported to the contract. Every emitted packet is
    broadcast to the mempool, and proving a violation needs only the signed
    packets (1.3, Enforcement). The gap is incentives: the model burns
    charges, so reporters gain nothing. A bounty paid from the slashed
    deposit is the natural fix; it is not modelled.

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
- the agent-form fixed point;
- that the contract's deferred guard obligations coincide with the source's
  (`Vegas.SourceProgram.Obligation.completedBy` and
  `Vegas.SourceProgram.Obligation.accepts`);
- information-respecting orders as the runtime's dependency modes;
- the phase reset in the contract;
- success separability as a predicate on schedulers, with fixed laws for the
  private components;
- the perturbed agent-form construction of Proposition 1 on $\Gamma^X$, and
  its lift in Theorem 3 along one tremble sequence;
- guard satisfiability (1.5) for the programs in scope;
- the domain check on openings (1.2, 1.3).
