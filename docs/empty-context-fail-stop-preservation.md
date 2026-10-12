# SE preservation for empty-context programs under a fail-stop compiler

Status: mathematics only, written 2026-10-12. Not mechanized. One
adversarial review found a verifiable-disclosure counterexample to the first
draft. A binding packet could carry checkable evidence of its own value
without being charged. That review's fixes are incorporated: the canonical
packet is now the whole packet with no evidence, plus the gaps of Section 7.
Companion to the
[empty-context counterexample](empty-context-se-counterexample.md), which
refutes deposit-first preservation for the current compiler.

## 1. Question and answer

The counterexample shows that the current compiler (the forfeit pass, which
continues the program's failure branches, with an audit that charges every
authentic packet that is never accepted) cannot preserve sequential
equilibrium (SE) when the deposit is fixed before the builder. This note asks
whether a different concrete compiler can. It answers yes, at Stage S, for a
compiler that changes two things:

- **Fail-stop.** The first failed owned event ends the game with fixed
  payoffs. The program's failure branches are never run.
- **Free identical copies.** The audit does not charge a copy of an owner's
  canonical packet for an event that was ready when the copy was sent, whether
  the copy is accepted, duplicated or never included. Every other authentic
  packet is charged.

Both changes alter adopted semantics, so adopting them is an owner decision
(Section 7).

The refutation uses both features this compiler removes: strategic play after
a failed opening (the term $F$ of the counterexample), and charges whose size
depends on the delivery route. Section 6 shows why each one breaks the
argument below.

## 2. Assumptions

1. **Programs.** Straight-line programs over commit (optionally guarded),
   reveal, sample and return, starting from the empty context, with finite
   payload types. Guards read data available to the author at the commit:
   public data, publications made before the commit, and the author's own
   commitments. A guard is evaluated at the reveal that completes its reads,
   which is one of the author's own. So the author can always choose an
   accepted value. Every commitment is revealed. An unrevealed commitment
   reaches no payoff and no guard evaluation, so a compiler can drop it.
2. **Utilities and the honest game.** As in the counterexample: utilities
   read public results only. The *honest game* $H$ has every commitment hold a
   value accepted by its guard, and every reveal open. Write $[L_i,U_i]$ for
   the range of player $i$'s utility over terminal histories of $H$.
3. **Compiler FS.**
   - *Events.* Stage S: one owned event at a time, in program order; sample
     events are drawn by the runtime from their source law.
   - *Abort.* An owned event of player $j$ *fails* if it ends without success:
     a missed binding, a failed or unopenable opening, a guard rejection, or
     expiry. The first failure ends the game. Player $j$ receives a fixed
     $a_j<L_j$, and every other player $i$ receives a fixed constant
     $c_i^{(j)}$. Neither depends on any value or record. The forfeit is
     $L_j-a_j>0$, and it need not exceed the payoff range.
   - *Audit.* A packet (the whole `WitnessedPacket`: call, evidence and
     token) is *canonical* if it is identical to its owner's canonical packet
     for an event that was ready when it was sent.
     - For a reveal, the canonical packet is the opening of the bound value,
       carrying exactly the evidence the runtime requires for that opening.
     - For a commit, it is the first binding packet sent while the event was
       ready, provided it uses a fresh handle the owner owns and carries **no
       evidence**.

     Canonical packets are never charged. Every other authentic packet is
     *forbidden*, including:
     - a packet sent while its event is not ready, which includes copies sent
       after completion;
     - a packet of a non-owner;
     - a malformed packet;
     - an opening of a different value;
     - a second, different binding;
     - a binding with a used or foreign handle;
     - any packet whose evidence or other fields differ from the canonical
       packet, so in particular **every disclosure of an unopened value**.

     Each forbidden packet is charged $K_i$ (capped once per player). The
     audit sees every emitted packet, included or not. At every history at
     which a forbidden packet is emitted, the charge is collected with
     conditional probability at least $\alpha>0$. The collection law reads no
     unopened value. Charges are burned, so they enter no player's gross
     payoff.
   - *Deposit.* $\alpha K_i>\Delta_i$, where $\Delta_i$ is the spread of
     player $i$'s gross payoff over all compiled terminal histories (honest
     outcomes, own abort $a_i$ and the constants $c_i^{(j)}$).
4. **Runtime.** The bounded raw signed-message runtime with its full raw
   menus: silence, malformed calls, copies, extra identifiers, evidence
   attachments, messages at forbidden times, and unopenable bindings. The
   game is finite: finite menus and a finite horizon $H$.
5. **Builder.** A public chance process satisfying `AsyncContract`
   (opportunity within `delay`, protected inclusion within `bound`, complete
   play) and `AsyncTimely` (`delay + bound < deadline` for every owned event),
   all on every legal history. It is **value-blind**: its scheduling,
   inclusion and leak laws read public data, packet identities, authors, and
   the value of the opening being delivered. They read no other unopened value,
   and in particular no evidence that a forbidden packet carries about an
   unopened candidate. The runtime's scheduler view contains pending payloads,
   so this restricts the builder. A canonical binding carries no evidence, so
   it is opaque. The author-only observation rule gives the leak part.
   Blindness to late packets is **not** assumed. Players know the builder's
   law, not its realization.
6. **Preservation.** As in the counterexample: the native SE induces the honest
   SE's joint law of public results and realized net payoffs, and charges and
   forfeits nobody on its paths.

### Quantifier order

Fix the program and utilities. Then fix the abort payoffs $a,c$, the
collection rate $\alpha$ and the deposits $K$, which depend only on the
payoffs. Then fix an honest SE. Then fix any builder satisfying assumption 5.
The native SE is chosen last and may depend on all of these, including the
builder's law. **The deposit does not depend on the builder**, so this is the
deposit-first order of the counterexample.

## 3. Theorem

Under the assumptions of Section 2, in this quantifier order, every SE of the
honest game has a native SE of the compiled program that preserves it.

## 4. Construction

**Projection.** Call a binding *bad* if it is unopenable, wrongly typed or
rejected by its guard. A native history with no failure and no bad binding
determines an honest history: its committed values, sample draws and
publications. Let $I$ be a native information set of player $i$ that contains
such a history and at which $i$ has an honest choice (choosing a binding value,
or opening). Player $i$ knows the public results and their own commitments
there. So $I$ projects to an honest information set $\pi(I)$. The native set
refines $\pi(I)$ by operational data: activations, receipts, serials, handle
slots, leaks and timing.

If $i$ itself holds a bad binding, $i$'s own revealing it ends in its abort
$a_i$ whatever else happens. That is unless another player fails first, which
nobody does under $\sigma^*$. So every action is optimal there, and $\sigma^*$
plays an arbitrary honest-looking action.

**The profile $\sigma^*$.** Fix an honest SE $(\sigma^H,\mu^H)$.

- *First activation.* At the owner's first activation while its event is
  ready, the owner sends one canonical packet. For a binding, the value is
  drawn from $\sigma^H$ at $\pi(I)$, with a fresh owned handle chosen
  independently of the value and no evidence. For a reveal, the packet is the
  opening. Then the owner stays silent for that event.
- *Delivery.* At every other forced node where the owner's event is still
  unresolved, the owner follows a fixed delivery policy $\pi^*$ of canonical
  sends and silence. Such nodes include a later activation with nothing sent
  yet, and a node after a trembled extra copy, which voids the sole-identifier
  protection. $\pi^*$ maximizes the conditional probability that the event
  succeeds from that node. Section 5 shows that $\pi^*$ can be chosen to depend
  only on the owner's operational record, the public data and the opened value,
  never on other unopened values. When nothing is sent yet and the event is a
  binding, the value is again drawn from $\sigma^H$ at $\pi(I)$. When the
  protected sole identifier is pending, silence is in the argmax, since
  success is already sure.
- *Everything else.* Silence. No forbidden packet is ever sent.

**Trembles.** Take the honest tremble sequence $\sigma^H_n\to\sigma^H$ with
beliefs $\mu^H_n\to\mu^H$. Native actions tremble in three tiers:

- honest choices at native histories follow $\sigma^H_n$ at the projection;
- *native-only non-forbidden* actions get probability $\eta_n$:
  - silence at the first activation;
  - a canonical send that $\pi^*$ does not choose;
  - a binding outside the honest values, or a bad binding;
  - each handle slot other than the one $\sigma^*$ picks;
- forbidden packets get probability $\eta_n^M$.

$\eta_n$ is the same at every information set, so it never depends on a value
the actor holds. Two requirements fix the sequence:
- $\eta_n=o(\rho_n)$, where $\rho_n$ is the smallest positive probability
  that $\sigma^H_n$ or Nature gives to any action. Then one native-only
  deviation outweighs no honest tremble.
- $M>H$ and $\eta_n^{M-H}=o(\rho_n^{H})$. Then a history with a forbidden
  packet, of weight at most $\eta_n^M$, is negligible against any
  forbidden-free history, of weight at least $\eta_n^H\rho_n^H$.

Information sets that contain a history with no forbidden packet are the
*forced* region, where play is $\sigma^*$ perturbed as above. The rest is the
*free* region, reachable only through a forbidden packet.

**Free region.** For each $n$, take an equilibrium of the agent-form game in
which forced information sets play the perturbed $\sigma^*$, and free
information sets choose freely subject to the minimum probability $\eta_n^M$
on every action. It exists by Kakutani's theorem on the finitely many free
agents. Pass to a convergent subsequence of profiles and Bayes beliefs; the
limit is the assessment.

## 5. Proof

**Lemma A (beliefs in the forced region).** At every forced information set
the limit belief puts zero weight on histories with a forbidden packet or with
another player's bad binding. At a forced information set $I$ that projects,
the limit belief over $\pi(I)$ is $\mu^H(\pi(I))$.

*Proof.* A forced set contains a forbidden-free history, of weight at least
$\eta_n^H\rho_n^H$. Histories with a forbidden packet have weight at most
$\eta_n^M$, which is negligible by the choice of $M$. A bad binding has an
extra factor $\eta_n$ against the honest alternative with the same public
record, whose operational record has the same law (a canonical binding is
opaque). So its limit weight is zero. A forbidden-free history without bad
bindings factors as
$$
\Pr_n(h)=\Pr{}^H_n(\pi(h))\cdot N_n(h),
$$
where $\Pr^H_n$ is the honest probability under $\sigma^H_n$ and the source
chance, and $N_n$ collects the builder's draws, the leaks, the collection and
every native-only choice. By value-blindness and by the construction of the
trembles and of $\pi^*$, the law of the operational record given the honest
history depends on the honest history only through its public data and the
opened values. No packet in such a history carries evidence about an
unopened value: canonical bindings carry none, and every other packet is
forbidden. All earlier events completed, so the opened values are public at
$I$. Hence
$\sum_{h\in I,\,\pi(h)=x}N_n(h)$ is the same for every $x\in\pi(I)$, and
the posterior over $\pi(I)$ equals $\mu^H_n(\pi(I))\to\mu^H(\pi(I))$.
$\square$

The evidence clause of the audit is essential. Consider Battle of the Sexes,
in which both players commit and then both reveal. Without that clause, Alice
could attach checkable evidence of her value to an uncharged binding, Bob's
records would read it, and Alice would gain by committing first in
substance.

**Lemma B (delivery is one-dimensional).** Fix a forced history at which
player $j$'s event is still unresolved, and suppose every later choice in
the forced region follows $\sigma^*$. Then for every type of $j$ (its
commitments and private observations, which carry no unopened value of
anyone else) with no bad binding, every canonical delivery policy $s$
yields
$$
q_s\,V+(1-q_s)\,a_j ,
$$
where $q_s$ is the success probability of $s$ and $V\ge L_j$ is $j$'s honest
continuation value at the projected information set. So every type ranks
delivery policies by $q_s$ alone, and a policy maximizing $q_s$ is optimal for
all of them.

*Proof.* Canonical packets carry no charge, and abort pays $a_j$ whatever the
route. After success, $\sigma^*$ plays the projection of $\sigma^H$, and by
Lemma A other players hold honest beliefs, whatever the delivery route and
the record it left. So the continuation is the honest continuation of the
published value. Its value $V$ is at least $L_j$, which exceeds $a_j$. Since
$V-a_j>0$, the payoff increases strictly in $q_s$. The success probability
$q_s$ depends only on the builder and the policy. They may read the value being
opened, so $q_s$ and $\pi^*$ may depend on it. That value is public after
success, and failure ends the game. They read no other unopened value. So
$\arg\max_s q_s$ is the same set for every type that delivers the same opened
value, and $\pi^*$ selects from it using operational data and that value only.
For a late binding, $q_s$ does not depend on the value (value-blindness), so
the value choice is the honest one scaled by $q_s$. A type with a bad binding
has continuation value $a_j$ whatever it does, so it is indifferent and may
follow $\pi^*$ too.
$\square$

**Lemma C (forbidden packets are strictly dominated).** At any information
set, replacing a strategy that sends a forbidden packet with positive
probability by the same strategy with that packet removed strictly raises the
expected payoff.

*Proof.* Couple the two strategies on the same randomness. They agree on every
path where the packet is not sent. On the paths where it is sent, the
difference in gross payoff is at most $\Delta_j$, whatever happens later,
including in the free region. The charge costs at least $\alpha K_j>\Delta_j$
in expectation on those paths, unless $j$ was already charged there. That
requires an earlier forbidden packet, so apply the argument to the first one.
$\square$

**Sequential rationality, forced region.** By the one-shot deviation principle
for consistent assessments in finite games (Hendon, Jacobsen and Sloth 1996),
it suffices to check single deviations. Under the limit profile, play from a
forbidden-free history leaves the forced region only through the deviator's
own forbidden packet. By Lemma A, forced sets put zero limit weight on
histories that are not forbidden-free.

- *Honest choice at a first activation.* By Lemma A the beliefs are
  $\mu^H(\pi(I))$. An honest action followed by the immediate canonical send
  succeeds surely: by `Opportunity`, protected inclusion and `AsyncTimely`,
  the sole identifier is included before the deadline. So its value is the
  honest continuation value. Inclusion also means acceptance: a canonical
  packet with a fresh owned handle (for a binding), or the verified opening
  of the stored value (for a reveal), is accepted when included while ready.
  A guard rejection is accepted with a failure result, but honest values pass
  their guards. So $\sigma^H$ is optimal among honest actions
  by honest sequential rationality. The native alternatives are no better:
  - silence followed by late delivery yields $q_sV+(1-q_s)a_j\le V$ (Lemma B);
  - an unopenable or guard-violating binding ends in the author's own abort
    $a_j<V$ under $\sigma^*$, since nobody else fails first;
  - forbidden packets are strictly worse (Lemma C).
- *Late delivery.* $\pi^*$ is optimal by Lemma B, and Lemma C excludes
  forbidden packets. A late binding value follows $\sigma^H$, which is optimal
  because $q_s$ does not depend on the value.
- *Non-owners.* Silence is optimal: a non-owner's only alternatives are
  forbidden packets, excluded by Lemma C.

**Sequential rationality, free region.** Each free agent plays, in the
perturbed game, a constrained best response to Bayes beliefs under a fully
mixed profile. The standard limit argument (Selten's perfect equilibrium in
agent form implies sequential optimality) gives optimality at the limit
assessment. The forced agents are fixed throughout and do not affect this
argument.

**Consistency.** The assessment is the limit of the Bayes beliefs of the fully
mixed profiles of the construction, with Nature and the builder fixed. This is
Kreps–Wilson consistency.

**Preservation.** On the limit path every owner sends one canonical packet at
its first activation. It is included before the deadline, so no event fails
and no forbidden packet is sent: nobody is charged or forfeited. Bindings
follow $\sigma^H$, samples follow their source law, and the builder's
randomness affects no public result. So the joint law of public results and
net payoffs is the honest one. $\square$

## 6. Why each change is needed

- **Fail-stop.** If failure branches continue, a seen omitted opening informs
  the listener's later play, and the counterexample's term $F$ makes delivery
  timing a type-dependent choice. Lemma B fails there: payoff after failure
  depends on the type. The counterexample note refutes the current compiler,
  which has both continued failure branches and charged copies. It does not
  isolate fail-stop: whether free copies alone, without fail-stop, would
  suffice is not settled. The term $F$ suggests they would not.
- **Free identical copies.** Suppose a dead or duplicate canonical packet is
  charged. Then a delivery policy is a pair (success probability $q$, expected
  charge $C$), and type $V$ prefers policy 2 to policy 1 when
  $(q_2-q_1)(V-a_j)>C_2-C_1$. This is the case with the capped charge of the
  current audit: one copy costs $K(1-q_1)$, and two copies cost $K$ (at least
  one is dead). If the builder makes $Kq_1$ fall strictly between
  $(q_2-q_1)(L_j-a_j)$ and $(q_2-q_1)(U_j-a_j)$, then types with high
  continuation values send two copies and types with low values send one.
  This holds for every $K$, because the builder is chosen after the deposit.
  The copy count shows in serials and receipts, so Lemma A fails.
  Whether this alone yields a counterexample is **not settled here**. It
  breaks this proof.
- **Deposit $\alpha K_i>\Delta_i$.** Lemma C needs it. It depends only on
  payoffs and on the audit, never on the builder.
- **Charging every disclosure.** Without it, a binding with attached
  evidence discloses a value verifiably and without charge, so the commit
  order of the honest game is lost (the Battle of the Sexes example after
  Lemma A).
- **Value-blind builder.** Lemma A needs the operational law to read no
  unopened value. A builder that reads commitment contents can correlate its
  records with hidden types.

`AsyncContract` is per event and holds on every legal history, so one player's
late success cannot shorten the next owner's window. This is why the
"failure shifted to another stage" negative of the
[whole-game delivery note](commit-reveal-research/whole-game-delivery-preservation.md#the-knowledge-and-realism-boundaries)
does not apply: there, a player delays its own success so that the next stage
fails.

## 7. Scope, relation to earlier notes, and what remains

- **Owner decisions.** Fail-stop replaces the program's failure branches. The
  intended target compiles the honest game, which has no failures, so nothing
  of the source is lost. But it differs from the adopted forfeit pass.
  Free canonical copies differ from the adopted audit, which can forbid a dead
  canonical packet. The
  [delivery-control note](commit-reveal-research/delivery-control-preservation.md)
  already describes this variation as "a different utility/accountability
  interface, not an authorized change to adopted semantics".
- **Relation to that note.** It proves preservation for an abstract delivery
  interface: fixed-value send, wait and retry menus with one controller per
  opening. This note specializes to the raw runtime of empty-context
  programs. That adds raw forbidden traffic (Lemma C, which needs the deposit),
  unopenable and guard-violating bindings, late bindings, samples, and the
  `AsyncContract` builder class.
- **Concurrency.** Stage S only. With concurrent events, a player can see
  another's pending opening before making its own choice. Fail-stop does not
  remove that front-running channel, so the concurrent stage needs its own
  analysis.
- **Mechanization must check.**
  - The projection $\pi$ on raw native information sets.
  - Value-blindness of the runtime's scheduler view, of the leak rule and of
    audit collection.
  - That `ProtectedInclusion` with a sole identifier plus `AsyncTimely` gives
    sure success at the first activation. That property gives a receipt.
    Acceptance follows from the handle checks and from opening verification.
    Expiry cannot come first, because both clocks count from readiness.
  - The evidence field: an audit verdict that marks every packet differing
    from the canonical one as forbidden, and a builder that reads no evidence
    about unopened candidates.
  - The coupling of Lemma C under the capped audit, with collection bounded
    below conditionally on every history.
  - The agent-form fixed point for the free region.
  - Finite menus (serials and raw values bounded) and a finite horizon.
  - Finite payload types (assumption 1) are needed for finiteness. The
    auction examples, with infinite payload types, are outside the theorem.
- **Builder-first.** Implied for this compiler: the deposit already does not
  depend on the builder.
