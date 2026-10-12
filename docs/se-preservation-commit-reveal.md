# Sequential equilibrium of commit–reveal programs on an asynchronous ledger

Status: mathematics, prepared for external review (2026-10-12). No theorem is
mechanized.

Review history:
- Theorems 1 and 2 had independent adversarial reviews, and then one further
  review of the consolidated text that re-checked every arithmetic step.
- Theorem 3, on concurrency, had two adversarial reviews as a separate note:
  - the first found a counterexample, now Example 3, which led to the
    commit-phase reset;
  - the second found nothing fatal.
- The merged text, with Theorem 4, then had two further reviews. They led to:
  - the source game $\Gamma^X$ with the source's own deferred guards, and
    Proposition 1 (1.6);
  - the tier split of Theorem 4;
  - fixed laws for the private success randomness in (S2);
  - most recently:
    - residual games taken inside $\Gamma^X$, with one selection map;
    - privately doomed players;
    - the tremble order for bad bindings;
    - a domain check on openings;
    - the guard-satisfiability assumption.

**Not yet reviewed in their current form:**
- Proposition 1 and the residual selection map (1.6);
- the treatment of publicly and privately doomed players, including the
  doom-related parts of Theorem 2 (3.1, 3.2);
- Theorems 3 and 4 as merged here (Sections 4 and 5).

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
- **Theorem 2 (positive, one event at a time).** A modified compiler succeeds,
  with two changes.
  - *Exclusion.* A player whose event fails gets a fixed payoff below every
    honest payoff of theirs, and the others continue.
  - *A free first packet.* A player's first well-formed packet for an event is
    never charged, whether or not it is included. Everything else the player
    sends is charged.

  For every program in the class, every forfeit, every deposit above the
  payoff spread and every admissible value-blind builder, every honest SE is
  preserved.
- **Theorem 3 (positive, concurrent).** The same holds when events run
  concurrently in an order that respects the source's information dependence.
  Three further conditions are needed:
  - concurrent commit phases are reset when a binding fails;
  - the builder is *success-separable*: whether an event succeeds depends only
    on its owner's delivery and on randomness private to that event, while the
    timing and order of inclusion are free, so a stable fee priority is
    allowed;
  - the builder is *per-event value-blind*: what it does with an event reads no
    unopened value other than that event's own opening;
  - its leaks are *author-only*: they depend on who emitted pending packets,
    not on their content;
  - the exclusion payoff lies below every payoff the player can receive while
    not excluded.

  Examples 1–3 show that each condition is needed.
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
| $\Gamma^X$ | The source game with exclusion: the source's full commit menu, deferred guards, failure and exclusion (1.6). |
| guard obligation | A guard retained at a commit and checked at the reveal that completes its reads (1.1). |
| publicly doomed | A player whose published values admit no guard-satisfying assignment of its hidden commitments, so that a later reveal of its must fail (1.6). |
| privately doomed | A player whose own commitments admit no guard-satisfying assignment; it knows this, others may not (1.6). |
| initialized $\Gamma^X$ program | $\Gamma^X$ started from a nonempty public history, possibly with doomed players and published violating values, and a product prior sequence on the active players' hidden commitments (1.6). |
| selection map $R$ | The fixed rule choosing the residual SE after an exclusion, used by both Proposition 1 and Theorem 3 (1.6). |
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
initial commitments and no prior. Every commitment is revealed. Section 4.3
also uses *initialized* programs, which start from a nonempty state.

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
  failed or unopenable opening, a reveal whose completed obligation rejects,
  or an expiry. Player $j$ is then **excluded**:
  - each later event of $j$ completes as a failure, without becoming ready
    for $j$;
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
4. The audit observes every emitted packet, including packets sent privately
   to the builder, with the collection bounds of 1.3. How dead packets are
   reported (for example, by watchers submitting signed packets) is outside
   the model.
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
- **Reset.** Under concurrency, if a commit fails, the phase's other commits
  are voided, with their guard obligations. Their owners commit again in a
  fresh phase.

$\Gamma^X$ contains no blockchain detail: no clocks, packets, builder or
mempool. Compared with the honest game, it adds three things: the source's
full commit menu (guard-violating values included, with deferred guards), the
meaning of failure, and the reset. The honest game is the subgame of
$\Gamma^X$ in which nobody fails and nobody commits a value that its guards
will reject. Call the information sets reached that way the **honest region**
of $\Gamma^X$.

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

**Initialized $\Gamma^X$ programs.** Proposition 1 and Theorem 3 also use
$\Gamma^X$ started from a nonempty state. An initialized $\Gamma^X$ program
fixes three things:
- an initial public history of $\Gamma^X$: publications, possibly including
  published violating values, the exclusion set, and possibly publicly doomed
  players;
- for each active player, its existing hidden commitments;
- a **product prior sequence** $\pi_n\to\pi$ on those commitments, with full
  support (bad bindings included). The product is across players.

An empty-context program is the special case with nothing initialized.

**Consistency along a prior sequence.** For an initialized game, an assessment
is *consistent along $\pi_n$* if its beliefs are limits of Bayes beliefs under
the prior $\pi_n$ and fully mixed profiles. This perturbs Nature's initial
draw as well as the players, so it is not Kreps–Wilson consistency for the
initialized game taken alone. It is only ever used inside a larger game, where
$\pi_n$ is itself the Bayes posterior that the larger game's fully mixed
profile induces at the start of the residual game. So the combined assessment
is Kreps–Wilson consistent in the larger game. At the top level the context is
empty, there is no initial draw, and samples keep their fixed laws, so the
final assessment is standard Kreps–Wilson.

**Residual games and the selection map.** Let $h$ be a public history of
$\Gamma^X$ after an exclusion, and $\pi_n$ a product prior sequence for the
active players' hidden commitments.
- The **residual game** at $(h,(\pi_n))$ is $\Gamma^X$ started from $h$ with
  those players.
- Its **residual honest game** is the subgame in which no active player that is
  not privately doomed fails or violates. A doomed player's reveal fails by its
  guard.

Fix once and for all a **selection map** $R$. It assigns to each
$(h,(\pi_n))$ an SE of the residual honest game that is consistent along
$\pi_n$, extended to the residual $\Gamma^X$ game by Proposition 1 applied with
fewer active players. Such an SE exists: take a limit of perturbed equilibria
with prior $\pi_n$. $R$ reads $h$ and the sequence only. Proposition 1 and
Theorem 3 use the same $R$; the recursion is well founded by induction on the
number of active players.

**Regions of $\Gamma^X$** (the first that applies):
1. **post-exclusion**: sets after an exclusion;
2. **doomed**: other sets in which some active player is publicly doomed;
3. **privately doomed**: other sets of a player that is itself privately
   doomed;
4. **honest region**: all other sets. Each contains a history with no failure
   and no violation: others' hidden violations are not publicly doomed, so
   each has an honest counterpart with the same public record.

**Proposition 1 (an SE of $\Gamma^X$ extending the honest SE).** Fix an
initialized $\Gamma^X$ program with prior sequence $\pi_n$, and an SE
$(\sigma^H,\mu^H)$ of its honest game that is consistent along $\pi_n$.

1. If $a_j<\underline u_j$ for every $j$, then $\Gamma^X$ has an SE
   $(\sigma^X,\mu^X)$, consistent along $\pi_n$, whose play on the honest
   region is $\sigma^H$, with nobody failing and nobody violating. On the honest
   region, its beliefs about other players' values are $\mu^H$.
2. If $a_j<m_j$ for every $j$, the SE can moreover be chosen to have two more
   properties:
   - **Never fail.** No player that is not privately doomed ever fails.
   - **Residual play.** After an exclusion at $h$, play is $R(h,(\pi^X_n))$.
     Here $\pi^X_n$ is the posterior of the active players' hidden commitments
     at $h$, along the SE's own tremble sequence.

*Proof.* We use a perturbed agent-form construction, by induction on the
number of active players. The construction has four parts:

- *Honest region.* Play is forced to $\sigma^H_n$, scaled by
  $1-\eta_n-\eta_n^2$. Failures tremble with probability $\eta_n$, which does
  not depend on values. Guard-violating values share probability $\eta_n^2$.
  The sequences satisfy $\eta_n=o(\rho_n)$ and $\eta_n^2=o(\rho_n^{\mathcal T})$.
- *Post-exclusion (case 2).* Play is forced to $R(h,(\pi^X_n))$, with its own
  trembles at the common index $n$.
- *Post-exclusion (case 1), doomed and privately doomed sets.* These sets
  choose freely, with minimum probability $\eta_n^2$ on every action.
- *Limit.* A Kakutani fixed point exists for each $n$. Pass to a convergent
  subsequence of profiles and Bayes beliefs.

*Beliefs on the honest region.* The failure trembles do not depend on values. A
violating history has a factor $\eta_n^2$. Its honest counterpart with the same
public record may differ in up to $\mathcal T$ of the author's hidden
commitments, so its weight is at least $\rho_n^{\mathcal T}$ times the common
factors. Since $\eta_n^2=o(\rho_n^{\mathcal T})$, violations get zero limit
weight. So beliefs about other players' values are $\mu^H$.

*One-shot deviations on the honest region:*
- **Failing** yields $a_j$.
- **Violating** makes $j$ privately doomed, so it yields $a_j$.
  - Under Stage S, $j$ is excluded at the reveal that completes the violated
    obligation, or earlier if it fails.
  - Under concurrency, a co-phase failure could reset the violation away. But
    under the limit profile nobody fails on the honest region, so this has
    probability $0$, and the deviation yields $a_j$ in the limit.
- **Following $\sigma^H$** yields the honest continuation, which is worth at
  least $\underline u_j>a_j$.
- **Among honest values**, $\sigma^H$ is optimal by honest sequential
  rationality.

*Case 2.* Consider a player that is not privately doomed.
- By guard satisfiability, it can commit acceptable values at every later
  commit. So it has a continuation that never fails and never violates. That
  continuation keeps it non-excluded, which is worth at least $m_j>a_j$.
- Failing yields $a_j$. So at every set where it chooses freely, failing is
  strictly worse, and gets only the minimum probability, which vanishes in the
  limit.
- On the honest region it never fails by construction.
- After an exclusion it never fails, by induction (the residual play is $R$).

*Privately doomed sets.* Every action of the doomed player yields $a_j$, up to
the vanishing reset event, so free choice is optimal there.

*Free sets.* The remaining free sets are optimal by the agent-form limit
argument.

*Consistency.* The post-exclusion entry beliefs are the posterior $\pi^X_n$, so
$R$'s assessment, which is consistent along $\pi^X_n$, combines with the outer
sequence into one consistent assessment. $\square$

Under the weaker bound alone, "never fail" can fail after an exclusion. Take a
Stage S program in which C's reveal precedes A's, with $u_A=-X$ if C's reveal
failed and $u_A=0$ otherwise, and $a_A=-X/2$. Then $a_A<\underline u_A=0$ but
$a_A>m_A=-X$, and after C is excluded A strictly prefers to fail.

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
reached by an ordinary source-level deviation, a guard-violating commit. Under
Theorem 2's bound $a_j<\underline u_j$ alone, a player's continuation value at
such a set can fall below $a_j$, as the example after Proposition 1 shows.
Lemma B's type-independence could then fail there. So Theorem 2 treats these
sets like sets after an exclusion. Theorem 3, under $a_j<m_j$, lifts the
$\Gamma^X$ SE of Proposition 1 there instead (4.4).

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
wrongly typed binding. Every uncharged action of $i$ is optimal, because its
gross payoff is $a_i$ in every continuation of $\sigma^*$. $\sigma^*$ plays
as if each of $i$'s bad bindings held a fixed honest value, with the
exceptions listed below.

**The profile $\sigma^*$ on the forced region.**

- *First activation while the event is ready.* The owner sends its free
  packet:
  - for a binding, the value is drawn from $\sigma^H$ at $\Pi(I)$, which is
    $\sigma^X$ there by Proposition 1, with a fresh handle of the owner,
    chosen independently of the value, and no evidence;
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

The sequences satisfy four conditions:
$$
\eta_n=o(\rho_n),\qquad \eta_n^2=o(\rho_n^{\mathcal T}),\qquad M>2\mathcal T,
\qquad \eta_n^{M-2\mathcal T}=o\bigl((\rho_n/c)^{\mathcal T}\bigr).
$$
So a history with a charged action has weight at most $\eta_n^M$. That is
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
other sets choose freely with minimum probability $\eta_n^M$ on every action.
It exists by Kakutani's theorem. Pass to a convergent subsequence of profiles
and Bayes beliefs.

### 3.2 Proof

**Lemma A (forced beliefs are honest).** Two claims hold.

1. At every forced set, the limit belief puts zero weight on histories with a
   charged action or with another player's bad binding.
2. At a forced set $I$ at which no reveal is pending, the belief about
   **other players'** values over the $\Gamma^X$ set $\Pi(I)$ is
   $\mu^X(\Pi(I))$. It puts all its mass on nodes where the others are honest,
   and there it equals $\mu^H$. If the owner itself holds a bad binding, the
   claim still concerns only the others' values. The owner's own commitments
   are known to it.

At forced sets with a pending reveal, only the first claim is asserted;
Lemma B covers them.

*Proof.*

- *Charged actions* are negligible by the choice of $M$.
- *A bad binding* carries a factor of at most $\eta_n^2$. Its honest
  counterpart, with the same public record, carries at least
  $\rho_n^{\mathcal T}$ times the common factors, and
  $\eta_n^2=o(\rho_n^{\mathcal T})$. At a forced set nobody is publicly doomed,
  so such a counterpart exists. The two operational records have the same law,
  since well-formed bindings carry no evidence and are opaque.
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

**Phase reset (part of $C_1$ under concurrency).** Suppose a binding of a
commit phase fails, through a missed binding or expiry. Then:

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
- **(S2) Independence and a fixed law.** The law of each $\xi_e$ is fixed in
  advance. It depends only on the event $e$, stated relative to $r_e$, and not
  on the history. The family $(\xi_e)_e$ is independent across events, and
  independent of the remainder of the builder's randomness, of every player's
  choices, and of every $r_f$. An event re-run after a reset is a new event,
  with a fresh independent $\xi$.

The remainder may depend on the whole history, subject to per-event
value-blindness and author-only leaks:

- *when* an included packet is included, and in what order relative to
  others (for example a stable priority induced by fees, which are not
  modelled);
- activations other than an owner's own while its event is ready;
- clock advances and leaks.

(S1–S2) are an assumption separate from protected inclusion. They say that a
late packet may fail, but neither its failure nor its success is correlated
with anything another player can influence.

The marginal version is not enough, that is, requiring only that each event's
success *probability* be unaffected by others' traffic. If successes can be
correlated through timing, a player who gains from another's failure prefers
anticorrelated timing, and how much it prefers it depends on its continuation
value. (S2) excludes this.

### 4.3 Statement

The induction below passes through programs that start from a nonempty state.
An **initialized program** is an initialized $\Gamma^X$ program in the sense of
1.6:
- its initial public state may contain exclusions, publicly doomed players and
  published violating values;
- it comes with a product prior sequence $\pi_n\to\pi$ with full support;
- its honest SE must be consistent along that sequence (1.6).

The sequence matters because a residual game starts from the native
posterior *along the tremble sequence*, not from its limit. Types with zero
limit mass, which arise only through trembles, still determine beliefs at
off-path sets. An honest SE consistent along a given prior sequence exists:
take a limit of perturbed equilibria with prior $\pi_n$.

An active player holding a bad binding in the prior is handled as in Theorem 2.
It is projected as if it held a fixed honest value, and its weight vanishes
against every honest type.

An empty-context program is the special case with nothing initialized.
Product priors are preserved by honest play: each player's honest choice reads
only public data and its own commitments, so given the public history the
players' hidden commitments are independent.

**Theorem 3.** Take the deposit-first order, with compiler $C_1$ including the
phase reset, and fix:

- an initialized program with an information-respecting order;
- payoffs $a_j<m_j$;
- $\alpha>0$ and deposits with $\alpha K_i>\operatorname{sp}_i$;
- an honest SE $(\sigma^H,\mu^H)$, consistent along the program's prior
  sequence;
- a per-event value-blind, author-only, success-separable builder satisfying
  the contract of 1.2 (opportunity, protected inclusion, timeliness,
  completion) for every event.

Then some native SE preserves $(\sigma^H,\mu^H)$. Its beliefs are consistent
along $\pi_n$ together with the native trembles. This holds for every builder
continuation: after a barrier the remainder's law may depend on earlier data,
and each such continuation is again a builder of the stated class. The laws of
the $\xi$ never change.

The assessment it constructs has one further property:

**(P) Past-blindness.** On the forced and post-barrier regions (defined in
4.4), from each barrier on, the prescribed play is a function of four things:

- the public results;
- the exclusion set;
- each player's own commitments;
- data recorded after the barrier.

It does not read operational data (timing, serials, leaks) recorded before the
barrier. In particular, $\varphi^*$ reads only the fixed law of $\xi_e$, the
owner's activations and clock relative to $r_e$, and the value being opened.
Play on the free region may read anything, but the free region has vanishing
weight at every set outside it.

### 4.4 Construction

The construction is by induction on the number $k$ of active players. For
$k=0$ there is nothing to show. Assume the theorem, with (P), for fewer than
$k$ active players.

**Regions.** These replace the regions of Theorem 2. Each set belongs to the
first region that applies:

1. **free**: sets containing no history without charged actions;
2. **post-barrier**: sets containing a history without charged actions that
   lies after a barrier preceded by an exclusion. This applies even when
   publicly doomed players remain active;
3. **doomed**: sets containing a history without charged actions, in which
   some active player is publicly doomed;
4. **forced**: all remaining sets. These contain a history without charged
   actions in which no exclusion precedes the last barrier and no player is
   publicly doomed. They include the rest of a phase after an exclusion inside
   it.

Excluded players' own sets carry a constant gross payoff, and their only
uncharged action is silence.

**One tremble structure.** The native construction and Proposition 1 use the
same perturbation:
- honest choices follow $\sigma^H_n$;
- timing deviations, which are the native source of failures, get $\eta_n$;
- violating and other native-only values get $\eta_n^2$;
- charged actions get $\eta_n^M$, as in 3.1;
- doomed sets play the lift of $\sigma^X_n$, the perturbed profile of
  Proposition 1, at the same index $n$, with native-only actions trembling as
  in 3.1;
- post-barrier sets play the lift of $R$, at the same index $n$.

So the native weight of a clean history equals its $\Gamma^X$ weight under
$\sigma^X_n$, times a factor that depends on no active player's unopened
value, up to $1+o(1)$. A native failure arises from a timing tremble followed
by a failed delivery, so its probability differs from the $\Gamma^X$ failure
tremble. The difference is a factor that reads only operational data and, for a
reveal, the failing player's own delivered value. That value belongs to a
player who is excluded once it fails.

**Within a phase (forced region).** Play follows $\sigma^*$ of 3.1, including
between an exclusion and the next barrier, with two changes.

- **Delivery policy.** $\varphi^*$ is chosen among *own-service* policies.
  Their send times depend only on the owner's activations and the clock
  relative to $r_e$, and, for a reveal, on the value being opened. A binding's
  delivery policy reads no value. $\varphi^*$ maximizes the event's success
  probability, computed from the fixed law of $\xi_e$.

  By (S1–S2), conditioning on anything else cannot raise that probability:
  leaks and others' receipts come from the remainder, which is independent of
  $\xi_e$. So $\varphi^*$ is optimal among all delivery policies.
- **Honest values in a commit phase** are drawn from $\sigma^H$ at the
  projection $\Pi(I)$, whatever the native order of the phase's bindings. In a
  phase where a failure has already occurred, every binding will be voided,
  so any value is optimal, and $\sigma^*$ still draws from $\sigma^H$.

**After a barrier preceded by an exclusion (post-barrier region).** Let $h$ be
the $\Gamma^X$ public history to which the native public history projects
(M2). It keeps every publication, including published violating values, every
exclusion, and every publicly doomed player. Under the phase reset, the voided
bindings are removed and the phase's remaining owners commit again.

The residual program is the initialized $\Gamma^X$ program at $h$, with the
prior sequence defined **exactly** as
$$
\pi_n:=\mu^X_n(h).
$$
This is the $\Gamma^X$ posterior of the active players' hidden commitments
(bad ones included) along the tremble sequence $\sigma^X_n$ of Proposition 1.
Each $\pi_n$ is a product prior: in $\Gamma^X$ each choice reads only public
data and its owner's own commitments.

Play from the barrier onward is the native lift of $R(h,(\pi_n))$. By
induction, Theorem 3 with fewer active players provides that lift, for every
builder continuation, and it is past-blind.

**The native posterior matches $\pi_n$ uniformly.** At any post-barrier entry
set, the native posterior over the active players' hidden commitments is
$\pi_n(1+o(1))$, with the $o(1)$ uniform over the finitely many entry sets.
The reasons:

- by the single tremble structure above, the native weight of each history is
  its $\Gamma^X$ weight under $\sigma^X_n$, times an operational factor, times
  $1+o(1)$;
- the operational factor reads no active player's unopened value: bindings are
  opaque, the builder is per-event value-blind, and binding policies read no
  value;
- every leaked or included-but-failed opening belongs to a player who is
  excluded or already published;
- the excluded players' values enter only through the marginal over their own
  coordinates, which the product structure separates.

A uniform factor $1+o(1)$ on the prior does not change the limit of any ratio
of tremble probabilities. So the native beliefs inside the residual
continuation equal $R$'s beliefs in the limit, including at its off-path sets.
Consistency makes every observer's marginal about player $i$ the same.

**Doomed region.** Play is the lift of $\sigma^X_n$ of Proposition 1(2), at
the same index $n$ as the native trembles:
- at each native set, the prescribed $\Gamma^X$ move is drawn from
  $\sigma^X_n$ at the projected set $\Pi(I)$;
- the delivery of that move follows $\varphi^*$;
- native-only actions tremble as in 3.1.

$\sigma^X$ reads no runtime data, so this play is past-blind.

**Excluded players** stay silent, as before.

**Trembles and the free region.** Trembles are as in 3.1, with these
differences:

- the residual SEs, given by $R$, carry their own tremble sequences, built
  along the prior sequence $\pi_n$ at the barrier. So the two sequences are
  indexed together by construction;
- the free region is filled by perturbed agent-form equilibria, as before.

### 4.5 Proof

**Lemma A3 (beliefs within a phase).** Three claims hold.

1. At every forced set, the limit belief puts zero weight on histories with a
   charged action or with another player's bad binding.
2. At every doomed set, the limit belief about other players' values over
   $\Pi(I)$ is $\mu^X(\Pi(I))$. The operational factor reads no unopened
   value, so the native posterior is the $\Gamma^X$ posterior.
3. Suppose, in addition, that the set is forced, in a commit phase, and its
   owner has an honest choice. Then:
   - the owner's belief about the others' honest values already chosen is
     $\mu^H(\Pi(I))$;
   - the owner predicts the others' not-yet-chosen values of the phase by
     $\sigma^H$.

*Proof.* The weights work as in Lemma A, with $\eta_n^2=o(\rho_n^{\mathcal T})$
for bad bindings. At forced sets nobody is publicly doomed, so every bad
binding has an honest counterpart with the same public record. The new
operational data within a phase are the order and timing of others'
inclusions. Their law reads no unopened binding value: bindings are opaque,
the builder is per-event value-blind, and binding policies read no value. So
the factor $N_n$ does not depend on the values. At doomed sets, the prescribed
moves are $\sigma^X_n$'s at the common index, so the same factorization gives
the $\Gamma^X$ posterior.

The phase's not-yet-chosen values of other owners are chosen at information
sets that contain no other owner's value from the phase. An owner's own
earlier values in the phase are in its own information, as in the honest
game. $\square$

**Lemma D3 (value choice under reset).** Take a forced set in a commit phase
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
  $V^H(v)$ by Lemma A3.

The probability of each case does not depend on $v$. A binding's delivery
reads no value, and by (S2) others' successes do not depend on $j$'s choices.
$\square$

Without the reset, the second case would keep $v$, and $j$ would optimize
against a mixture that includes another player's failure. That is Example 3.

**Lemma B3 (delivery is one-dimensional).** Take a forced history at which
$j$'s event $e$ is unresolved and $j$ has sent nothing for it. Others in the
phase may be late, or may already be excluded. For every type of $j$ without a
bad binding, every policy $s$ that sends at most the free packet yields
$$
P_s\,V+(1-P_s)\,a_j ,
$$
where $V$ does not depend on $s$ and $V\ge m_j>a_j$. So every type ranks these
policies by $P_s$ alone. The same holds at doomed sets, with the continuation
given by $\sigma^X$.

*Proof.*

- *Failure* gives $a_j$.
- *Success.* Two things determine the continuation:
  - The outcomes of the phase's other events depend only on their own $\xi_f$,
    their owners' own-service policies or trembles, and their packets'
    content. So they do not depend on $s$ (S1–S2).
  - After the barrier, play is either $\sigma^H$ (if no one failed) or the
    residual SE. Both depend only on public results, exclusions and
    commitments, by (P).

  Within the phase, $s$ changes only inclusion timing and leaks. These are
  information that nobody's prescribed play reads: under $\sigma^*$, a
  binding's value choice reads no timing (Lemma A3), and the continuation
  after the barrier is past-blind.

  So $V$ is an expectation of $j$'s non-excluded gross payoff, which is at
  least $m_j$, and it does not depend on $s$. For a reveal, $P_s$ may depend
  on the value being opened, which is public after success, and $\varphi^*$
  reads only that value.
- *Doomed sets.* The continuation after the phase is $\sigma^X$, which reads
  no timing. If $j$ itself is publicly doomed, its payoff is $a_j$ whatever it
  does. $\square$

**Lemma C** (charged one-shot deviations do not pay) holds verbatim.

**Sequential rationality.** Single deviations suffice. No player can make
another fail without a charged action: another player's emissions enter
neither $\xi_e$ nor the content of $e$'s packets (S1). The cases:

- **Honest value choice in a commit phase.** It is optimal among honest values
  by Lemma D3. Sending at once succeeds surely, by protected inclusion. The
  alternatives are no better:
  - late delivery gives $P_sV+(1-P_s)a_j\le V$ (Lemma B3);
  - a bad binding gives $a_j$;
  - charged actions are worse (Lemma C).
- **Reveal at a first activation.** Sending succeeds surely and is worth at
  least $m_j>a_j$, whatever others do in the phase. Withholding gives $a_j$.
  Delaying cannot help, because nothing later reads the timing (P).
- **Late delivery.** $\varphi^*$ is optimal (Lemma B3).
- **After the free packet, non-owners, own bad bindings, excluded players.**
  As in Theorem 2.
- **Doomed sets.** Prescribed moves are $\sigma^X$'s, which are sequentially
  rational in $\Gamma^X$ at the belief $\mu^X(\Pi(I))$ (Lemma A3). A runtime
  deviation is either a $\Gamma^X$ deviation, a timing deviation (Lemma B3),
  or a charged action (Lemma C).
- **From a barrier after an exclusion onward.** Sequential rationality holds
  by induction, provided the lift of $R(h,(\pi_n))$ is an SE in the native
  continuation.

  It is. By (P), and by Lemma A3 applied to the pre-barrier operational data,
  that data is independent of every active player's hidden value given the
  public history. The only values that leaked and were never published belong
  to excluded players. They are:
  - uninformative about the active players' values, by the product prior;
  - payoff-irrelevant, since the excluded players' results are failed;
  - read by no active player's prescribed strategy, by (P).

  So, along the sequence, conditioning on the pre-barrier data leaves every
  active player's belief equal to $\pi_n(1+o(1))$ (4.4). The assessment of $R$
  therefore carries over, beliefs and rationality alike.

**Consistency.** The outer and residual tremble sequences share the index
$n$. The residual sequence is built along $\pi_n$. Within a residual
continuation, the remaining entry weights are value-independent common
factors (Lemma A3), up to a uniform $1+o(1)$. So the native Bayes beliefs
converge to the residual ones, including at the residual's off-path sets.

**Preservation.** On the path every owner sends its free packet at its first
activation, which succeeds surely. So no exclusion or reset occurs, and play
follows $\sigma^H$. The joint law of public results and net payoffs is the
honest one. $\square$

### 4.6 Examples showing the conditions are needed

Each example has complete information, so every claimed choice is strict and
every SE makes it.

#### Example 1: coupled late inclusion violates (S1–S2)

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
- after an exclusion it plays the residual SE chosen by the selection map $R$.

Under Theorem 2's weaker bound, Proposition 1(1) gives an SE of $\Gamma^X$
extending $\sigma^H$, but "never fail" can fail after an exclusion (the example
after Proposition 1). Theorem 2's native construction does not lift
$\Gamma^X$ play after an exclusion or a public doom: it fills those sets with
an arbitrary agent-form equilibrium. So, under Theorem 2's hypotheses alone,
tier E below holds only at sets before any exclusion or public doom.

### 5.2 Statement

Call a runtime history **clean** if no player has emitted a charged packet in
it. Call an information set **clean** if it contains a clean history. The
clean sets are exactly those in the forced, doomed and post-barrier regions of
4.4.

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
- **M4. Nobody's clean actions affect another's success or charges.**
  - For an on-time packet this is M1, under every execution order.
  - For a late packet it follows from (S1–S2): success depends only on
    $\xi_e$, whose law is fixed, and on the owner's own emissions.
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
  packet now, and sends on time at every later turn of its own. Then $j$ is
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
  has a value choice. Its belief about others' unopened values, and its
  prediction of the not-yet-chosen values of its phase, are those at $I^X$
  under $\sigma^X$. Values seen in included openings whose result is
  $\mathsf{fail}$ belong to excluded players. By the product structure they say
  nothing about active players' values. Two special cases:
  - for an owner's own bad binding the value choice is irrelevant, since its
    payoff is $a_j$;
  - in a phase where a failure has already occurred, every value will be
    voided, so any value is optimal.

  Reveal decisions need no belief, because D2 settles them.
- **E2. Play is source play.** At clean sets, prescribed play is $\sigma^X$ at
  $I^X$. Runtime data enters only through the client's choice of *when* to
  send, $\varphi^*$.
- **E3. Timing deviations are source lotteries.** For an event the owner has
  not yet sent, every uncharged deviation in send time (silence, late sending,
  another time) has expected payoff
  $$
  P\cdot V+(1-P)\cdot a_j .
  $$
  This is a lottery between two $\Gamma^X$ outcomes: the honest move, with
  continuation value $V$, and $j$'s own failure. The success probability $P$
  is a runtime quantity, but it enters only as a weight. The other uncharged
  deviations map directly to $\Gamma^X$ actions:
  - another value maps to another honest move;
  - another handle slot maps to the same move;
  - a bad binding maps to "commit some value of the domain, then fail".
- **E4. Timing reads only the delivered value.** Every type ranks send times
  by $P$ alone. So in equilibrium a player's send time is a function of the
  value being delivered (for a reveal) and of operational data, and of
  nothing else it knows. The delivered value is public after success.
- **E5. Cheap talk carries no meaning.** Handle slots, send times and
  inclusion order carry no information about any active player's unopened
  value at a clean set with a value choice. Observers' beliefs ignore them
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
- The law clause is value-blindness, author-only leaks, and the collection
  condition of 1.3.
- The claim at commit-choice sets uses order rule 1: no reveal is in flight
  during a commit phase. Every opening seen earlier either succeeded
  (published) or failed (author excluded).

**M4.** For on-time packets, this is M1. For late packets, by (S1) success is a
function of $\xi_e$, the owner's emission clocks and the content of its
packets. By (S2) the law of $\xi_e$ is fixed and independent of everything
another player controls. Charges attach to the emitter by 1.3.

**D1.** This is the computation of Lemma C. It applies at any information set
where $j$ is uncharged, whatever the continuation.

**D2.** By M1, each on-time free packet succeeds. M1 rests on protected
inclusion, which holds on every legal history whatever others emit, charged
packets included. By guard satisfiability (1.5), $j$ can commit acceptable
values at every later commit. So $j$ is excluded only through its own bad
binding. A non-excluded terminal payoff is at least $m_j$ by definition, and
$m_j>a_j$.

**E1 and E5.** At clean sets, Lemma A3 gives zero weight to unclean
histories and to others' bad bindings. It gives honest beliefs over the
projection before any exclusion or public doom, and $\Gamma^X$ beliefs at doomed
sets. After an exclusion, 4.4 gives beliefs equal in the limit to those of
$R(h,(\pi_n))$, which is $\sigma^X$ there because Proposition 1 uses the same
$R$.

Cheap-talk channels carry no information because their native law is
value-independent:

- handle slots tremble uniformly, at a rate that does not depend on values;
- send times follow $\varphi^*$, which reads only operational data and, for a
  reveal, the delivered value;
- inclusion order is chosen by the value-blind remainder.

So these channels drop out of the factor $N_n$.

**E2.** This holds by construction. $\sigma^*$ plays three things:
- $\sigma^H$ at the projection before any exclusion or public doom;
- the lift of $\sigma^X$ at doomed sets;
- the residual SE after an exclusion.

All three are $\sigma^X$, because Proposition 1(2) uses the same tremble
structure and the same selection map $R$. The only runtime-dependent choice is
$\varphi^*$.

**E3.** The timing case is Lemma B3: failure gives $a_j$, success gives a
continuation value $V$ that does not depend on the policy, and $P$ is the
policy's success probability. The other deviations change only the move or
the handle, which is a $\Gamma^X$ action by M2.

**E4.** This is the type-independence part of Lemma B3: $\arg\max P_s$
depends only on the fixed law of $\xi_e$, the clock and the delivered value.

$\square$

### 5.4 What each tier asks of an honest player

| Runtime phenomenon | Explained by | Tier | What it rests on |
| --- | --- | --- | --- |
| An honest move takes effect | the move itself | M1 | contract (protected inclusion) |
| Outcomes after misbehaviour | a $\Gamma^X$ outcome | M2 | exclusion, reset, deferred guards |
| Evidence about others' hidden values | none exists in clean traffic | M3 | well-formedness, value-blind builder |
| Seeing a failed opening (omitted but leaked, or included with result $\mathsf{fail}$) | an excluded player's irrelevant value | M3 | exclusion, product structure |
| Others interfering with your success | impossible; at most a reset of your phase | M4 | protected inclusion, success separability |
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

Exclusion, the phase reset and post-barrier residual play are a **recovery
protocol** that the compiler adds. They are not a compilation of the program's
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
  - the continuation lifts an SE of the residual honest game, chosen from
    public results only, by induction on the number of active players (as in
    4.4);
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
  - **Collection** with conditional probability at least $\alpha$ needs dead
    packets to reach the contract. The model assumes that watchers report
    every emitted packet (1.5), and that assumption is not derived.

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
- the induction over initialized $\Gamma^X$ programs with prior sequences,
  and the single selection map $R$ shared by Proposition 1 and Theorem 3;
- guard satisfiability (1.5) for the programs in scope;
- the domain check on openings (1.2, 1.3).
