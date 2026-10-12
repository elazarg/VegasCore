# SE preservation for empty-context programs when failing players are excluded

Status: mathematics only, written 2026-10-12. Not mechanized.

Review history:
- The first draft (fail-stop: the first failure ends the game) had one
  adversarial review. It found a verifiable-disclosure counterexample: a
  binding packet could carry checkable evidence of its own value without being
  charged.
- The second draft fixed that and the review's other gaps, but it defined
  "free copies" by send time, which the audit cannot observe.
- This revision does two things. It replaces ending the game by **exclusion**:
  the failing player leaves and the others continue. It also restates the
  audit rule using only data the audit can observe.

- A review of this revision found no fatal error. Its fixes are
  incorporated:
  - Lemma C is now one-shot, because of the charge cap;
  - bad-binding types stay silent at their reveals;
  - the excluded player's payoff is constant gross only;
  - Section 7 is corrected: with a fixed exclusion payoff, removing the
    failing player's later actions is not needed.

Companion to the
[empty-context counterexample](empty-context-se-counterexample.md), which
refutes deposit-first preservation for the current compiler.

## 1. Question and answer

The counterexample shows that the current compiler cannot preserve sequential
equilibrium (SE) when the deposit is fixed before the builder. That compiler
is the forfeit pass, which continues the program's failure branches with the
failing player still in play, plus an audit that charges every authentic
packet that is never included. This note asks whether a different concrete
compiler can. It answers yes, at Stage S, for a compiler that changes two
things.

- **Exclusion.** When an owned event of player $j$ fails, $j$ is excluded.
  Every later event of $j$ is recorded as a failure without $j$ acting, and $j$
  receives a fixed payoff $a_j$ below every honest payoff of $j$. The other
  players continue under the program's own semantics, with $j$'s results
  failed. Ending the game at the first failure is the special case in which the
  others also receive constants.
- **The first packet is never charged for not being included.** The audit
  charges by content and count, never for non-inclusion. Each owner's first
  well-formed packet for an event is free, whether it is included or not,
  provided it carries no disclosure. Every other authentic packet is charged:
  further packets for the same event, disclosures, malformed packets, and
  packets of non-owners.

The refutation uses exactly what these changes remove:
- the failing player's payoff depends on how others continue, and others
  continue with private knowledge of its leaked values (the term $F$ of the
  counterexample);
- a dead first packet is charged, so the charge depends on the delivery route.

Section 6 shows why each change is needed, and Section 7 asks which parts of
"exclusion" can be relaxed.

## 2. Assumptions

1. **Programs.** Straight-line programs over commit (optionally guarded),
   reveal, sample and return, starting from the empty context, with finite
   payload types.
   - Guards read data available to the author at the commit: public data,
     publications made before the commit, and the author's own commitments.
   - A guard is evaluated at the reveal that completes its reads, which is one
     of the author's own. So the author can always choose an accepted value.
   - Every commitment is revealed. An unrevealed commitment reaches no payoff
     and no guard evaluation, so a compiler can drop it.
2. **Utilities and the honest game.** Utilities $u_i$ read public results
   only (a value or failure for each reveal). The *honest game* $H$ has every
   commitment hold a value accepted by its guard, and every reveal open. Write
   $[L_i,U_i]$ for the range of $u_i$ over terminal histories of $H$.
3. **Compiler EX.**
   - *Events.* Stage S: one owned event at a time, in program order. Sample
     events are drawn by the runtime from their source law.
   - *Exclusion.* An owned event of player $j$ *fails* if it ends without
     success: a missed binding, a failed or unopenable opening, a guard
     rejection, or expiry. Player $j$ is then excluded:
     - each later event of $j$ completes as a failure without becoming ready
       for $j$;
     - $j$'s gross payoff is a fixed $a_j<L_j$, independent of every value,
       record and later result;
     - every other player $i$ continues, and receives $u_i$ evaluated on the
       public results, with the excluded players' results failed.

     The forfeit $L_j-a_j>0$ need not exceed the payoff range. When every
     player has been excluded, or the program ends, the game settles.
   - *Audit.* A packet is the whole `WitnessedPacket`: call, evidence and
     readiness token. It is *well-formed* for event $e$ if all of the following
     hold:
     - its author owns $e$;
     - it carries a valid readiness token for $e$, which the runtime attaches
       only once $e$ is ready;
     - it is a correct call for $e$: for a reveal, the opening of the bound
       value with exactly the evidence that opening requires; for a commit, a
       binding with a fresh handle the author owns and **no evidence**.

     The verdict reads only signed content, tokens, per-author serials and the
     final record, never send times:
     - **free:** the author's first packet for $e$ (lowest serial) if it is
       well-formed, whether or not it is ever included;
     - **charged:** every other authentic packet. That includes:
       - a second or later packet for the same event, even an identical copy,
         and even if the event failed;
       - every packet that is not well-formed, including every disclosure of
         an unopened value;
       - every packet of a non-owner.

     Each charged packet costs $K_i$, capped once per player.
     - The audit sees every emitted packet, included or not.
     - At every history at which a charged packet is emitted, the charge is
       collected with conditional probability at least $\alpha>0$.
     - The collection law reads no unopened value.
     - Charges are burned: they enter no player's gross payoff.
   - *Deposit.* $\alpha K_i>\Delta_i$, where $\Delta_i$ is the spread of
     player $i$'s gross payoff over all compiled terminal histories: honest
     outcomes, its own exclusion payoff $a_i$, and $u_i$ on every history with
     excluded players.
4. **Runtime.** The bounded raw signed-message runtime with its full raw
   menus: silence, malformed calls, copies, extra identifiers, evidence
   attachments, messages at forbidden times, and unopenable bindings. The
   game is finite: finite menus and a finite horizon $H$.
5. **Builder.** A public chance process satisfying `AsyncContract`
   (opportunity within `delay`, protected inclusion within `bound`, complete
   play) and `AsyncTimely` (`delay + bound < deadline` for every owned event),
   all on every legal history.
   - It is **value-blind**: its scheduling, inclusion and leak laws read
     public data, packet identities, authors, and the value of the opening
     being delivered. They read no other unopened value. In particular they
     read no evidence that a charged packet carries about an unopened
     candidate. The runtime's scheduler view contains pending payloads, so this
     restricts the builder.
   - A well-formed binding carries no evidence, so it is opaque. The
     author-only observation rule gives the leak part.
   - Blindness to late packets is **not** assumed.
   - Players know the builder's law, not its realization.
6. **Preservation.** The native SE induces the honest SE's joint law of public
   results and realized net payoffs, and charges and forfeits nobody on its
   paths.

### Quantifier order

1. Fix the program and utilities.
2. Fix the exclusion payoffs $a$, the collection rate $\alpha$ and the
   deposits $K$, which depend only on the payoffs.
3. Fix an honest SE.
4. Fix any builder satisfying assumption 5.
5. Choose the native SE last. It may depend on all of the above, including the
   builder's law.

**The deposit does not depend on the builder**, so this is the deposit-first
order of the counterexample.

## 3. Theorem

Under the assumptions of Section 2, in this quantifier order, every SE of the
honest game has a native SE of the compiled program that preserves it.

## 4. Construction

**Regions.** A *charged action* emits a charged packet: a non-well-formed
packet, a packet of a non-owner, or an owner's second or later packet for an
event. Information sets fall into three regions:
- the *forced* region: sets containing a history with no charged action and
  no exclusion;
- the *excluded* region: sets after some exclusion. Exclusion is public,
  because the failure result is on the record, so these sets are disjoint from
  the forced ones;
- the *free* region: all other sets. They are reachable only through a charged
  action.

**Projection.** Call a binding *bad* if it is unopenable, wrongly typed or
rejected by its guard.
- A history with no exclusion, no charged action and no bad binding determines
  an honest history: its committed values, sample draws and publications.
- Let $I$ be a forced set of player $i$ that contains such a history and at
  which $i$ has an honest choice (choosing a binding value, or opening).
  Player $i$ knows the public results and their own commitments there. So $I$
  projects to an honest information set $\pi(I)$.
- The native set refines $\pi(I)$ by operational data: activations, receipts,
  serials, handle slots, leaks and timing.
- Suppose $i$ itself holds a bad binding.
  - An unopenable or wrongly typed binding has no well-formed opening, so
    every reveal packet for it is charged. $\sigma^*$ prescribes silence at
    that reveal, which excludes $i$ with gross payoff $a_i$ at no charge.
  - A guard-violating binding has a well-formed opening. Sending it or staying
    silent both exclude $i$ with $a_i$, so $\sigma^*$ may send it.
  - At $i$'s other choices before that reveal, nobody else fails first under
    $\sigma^*$, so every uncharged action is optimal. $\sigma^*$ plays an
    arbitrary honest-looking one.

**The profile $\sigma^*$ on the forced region.** Fix an honest SE
$(\sigma^H,\mu^H)$.

- *First activation.* At the owner's first activation while its event is
  ready, the owner sends its one free packet:
  - for a binding, the value is drawn from $\sigma^H$ at $\pi(I)$, with a
    fresh owned handle chosen independently of the value, and no evidence;
  - for a reveal, the packet is the opening.
- *Late delivery.* Suppose the owner has sent nothing for its event, and the
  event is still unresolved. The owner then follows a fixed policy $\pi^*$,
  which decides at each activation whether to send the free packet now. It
  maximizes the conditional probability that the event succeeds.
  - Section 5 shows that $\pi^*$ can be chosen to depend only on the owner's
    operational record, the public data and the value being opened, never on
    other unopened values.
  - For a late binding the value is again drawn from $\sigma^H$ at $\pi(I)$.
- *Everything else.* Silence. In particular, once the free packet is sent, the
  owner sends nothing more for that event.

**Trembles.** Take the honest tremble sequence $\sigma^H_n\to\sigma^H$ with
beliefs $\mu^H_n\to\mu^H$. Forced actions tremble in three tiers:

- honest choices at native histories follow $\sigma^H_n$ at the projection;
- *native-only uncharged* actions get probability $\eta_n$:
  - silence at the first activation;
  - a send time that $\pi^*$ does not choose;
  - a binding outside the honest values, or a bad binding;
  - each handle slot other than the one $\sigma^*$ picks;
- charged actions get probability $\eta_n^M$.

$\eta_n$ is the same at every information set, so it never depends on a value
the actor holds. Write $\rho_n$ for the smallest positive probability that
$\sigma^H_n$ or Nature gives to any action. Two requirements fix the
sequence:
- $\eta_n=o(\rho_n)$;
- $M>H$ and $\eta_n^{M-H}=o(\rho_n^{H})$.

The second makes a history with a charged action, of weight at most
$\eta_n^M$, negligible against any history without one, which has weight at
least $\eta_n^H\rho_n^H$.

**Excluded and free regions.** For each $n$, take an equilibrium of the
agent-form game in which:
- forced sets play the perturbed $\sigma^*$;
- excluded and free sets choose freely, subject to the minimum probability
  $\eta_n^M$ on every action.

It exists by Kakutani's theorem on the finitely many unconstrained agents.
Pass to a convergent subsequence of profiles and Bayes beliefs; the limit is
the assessment.

## 5. Proof

**Lemma A (beliefs in the forced region).** At every forced information set,
the limit belief puts zero weight on histories with a charged action or with
another player's bad binding. At a forced set $I$ that projects, the limit
belief over $\pi(I)$ is $\mu^H(\pi(I))$.

*Proof.* We bound the weight of each kind of history in turn.
- *Charged actions.* A forced set contains a history with no charged action,
  of weight at least $\eta_n^H\rho_n^H$. Histories with a charged action have
  weight at most $\eta_n^M$, which is negligible by the choice of $M$.
- *Bad bindings.* A bad binding has an extra factor $\eta_n$ compared with the
  honest alternative that has the same public record. That alternative's
  operational record has the same law, since a well-formed binding is opaque.
  So the bad binding's limit weight is zero.
- *The remaining histories* (no charged action, no bad binding) factor as
$$
\Pr_n(h)=\Pr{}^H_n(\pi(h))\cdot N_n(h),
$$
where $\Pr^H_n$ is the honest probability under $\sigma^H_n$ and the source
chance, and $N_n$ collects the builder's draws, the leaks, the collection and
every native-only choice.

The law of the operational record given the honest history depends on that
history only through its public data and the opened values. This follows from
value-blindness and from how the trembles and $\pi^*$ are built. No packet in
such a history carries evidence about an unopened value: well-formed bindings
carry none, and every other packet is charged. All earlier events have
completed, so the opened values are public at $I$. Hence
$\sum_{h\in I,\,\pi(h)=x}N_n(h)$ is the same for every $x\in\pi(I)$, and
the posterior over $\pi(I)$ equals $\mu^H_n(\pi(I))\to\mu^H(\pi(I))$.
$\square$

The evidence clause of the audit is essential. Take Battle of the Sexes, in
which both players commit and then both reveal. If evidence were not charged,
Alice could attach checkable evidence of her value to her free binding. Bob's
records would show it, and Alice would gain by effectively committing first.

**Lemma B (delivery is one-dimensional).** Fix a forced history at which
player $j$'s event is still unresolved and $j$ has sent nothing for it.
Suppose every later choice in the forced region follows $\sigma^*$. Consider
any type of $j$ with no bad binding (its commitments and private
observations; the latter carry no unopened value of anyone else). For that
type, every policy that sends at most the one free packet yields
$$
q_s\,V+(1-q_s)\,a_j ,
$$
where $q_s$ is the policy's success probability and $V\ge L_j$ is $j$'s honest
continuation value at the projected information set. So every type ranks these
policies by $q_s$ alone, and a policy maximizing $q_s$ is optimal for all of
them.

*Proof.* The free packet is never charged, whether or not it is included.
Failure excludes $j$ with payoff $a_j$, whatever the route and whatever the
others do afterwards.

After success, $\sigma^*$ plays the projection of $\sigma^H$, and by Lemma A
the other players hold honest beliefs, whatever the delivery route and the
record it left. So the continuation is the honest continuation of the
published value. Its value $V$ is at least $L_j$, which exceeds $a_j$. Since
$V-a_j>0$, the payoff increases strictly in $q_s$.

The success probability $q_s$ depends only on the builder and the policy.
- They may read the value being opened, so $q_s$ and $\pi^*$ may depend on it.
  That value is public after success, and after failure it reaches no payoff
  of $j$.
- They read no other unopened value. So $\arg\max_s q_s$ is the same set for
  every type that delivers the same opened value, and $\pi^*$ selects from it
  using operational data and that value only.
- For a late binding, $q_s$ does not depend on the value (value-blindness), so
  the value choice is the honest one scaled by $q_s$.

A type whose binding violates its guard ends with $a_j$ whatever it does, so it
is indifferent and may follow $\pi^*$ too. A type with an unopenable or
wrongly typed binding has no free packet for this reveal and stays silent.

Before success the value being opened is not public, and $\pi^*$ may depend
on it. That is harmless: while the reveal is pending, every other player's
only uncharged action is silence, so their beliefs do not matter yet. The
handle slot is a cheap-talk channel that the audit cannot charge; its
trembles are value-independent, so by Lemma A observers ignore it. $\square$

**Lemma C (charged one-shot deviations do not pay).** At a forced information
set of player $j$, any one-shot deviation to a charged action is strictly worse
for $j$ than following $\sigma^*$. This holds whatever any player does
afterwards, including in the excluded and free regions.

*Proof.* At a forced set, $j$ has not yet been charged. A charge needs $j$'s
own charged packet, which is in $j$'s recall, and the set contains a history
with no charged action.
- The deviation makes $j$ pay $K_j$ with conditional probability at least
  $\alpha$. So it yields at most $\max(\text{gross}_j)-\alpha K_j$.
- Following $\sigma^*$ takes no charged action on any path, since others'
  charged actions never charge $j$. So it yields at least $\min(\text{gross}_j)$.

The difference is at most $\Delta_j-\alpha K_j<0$.

A further packet for an event is charged on every path on which it is sent,
whether the event then succeeds or fails, so multi-packet delivery needs no
separate treatment.

The statement is one-shot on purpose. Because the charge is capped once per
player, removing one charged action from a strategy that takes another one
later need not save anything. $\square$

**Sequential rationality, forced region.** By the one-shot deviation principle
for consistent assessments in finite games (Hendon, Jacobsen and Sloth 1996),
it suffices to check single deviations.

Under the limit profile, play from a history with no charged action and no
exclusion leaves the forced region in only two ways: through the deviator's
own charged action, or through the deviator's own exclusion. No one else fails
on such paths, because protected inclusion holds on every legal history and
others' packets cannot void it. By Lemma A, forced sets put zero limit weight
on any other histories.

- *Honest choice at a first activation.* By Lemma A the beliefs are
  $\mu^H(\pi(I))$.
  - An honest action followed by the immediate free packet succeeds surely. By
    `Opportunity`, protected inclusion and `AsyncTimely`, the sole identifier
    is included before the deadline. Expiry cannot come first, because both
    clocks count from readiness.
  - Inclusion means acceptance. A binding with a fresh owned handle, or the
    verified opening of the stored value, is accepted when it is included
    while ready. A guard rejection is accepted with a failure result, but
    honest values pass their guards.
  - So the honest action's value is the honest continuation value, and
    $\sigma^H$ is optimal among honest actions by honest sequential
    rationality.

  The native alternatives are no better:
  - silence followed by late delivery yields $q_sV+(1-q_s)a_j\le V$ (Lemma B);
  - an unopenable or guard-violating binding ends in $j$'s exclusion, with
    $a_j<V$;
  - charged actions are strictly worse (Lemma C).
- *Late delivery.* $\pi^*$ is optimal by Lemma B, and Lemma C excludes further
  packets and all other charged actions. A late binding value follows
  $\sigma^H$. That is optimal because $q_s$ does not depend on the value.
- *After the free packet is sent, and non-owners.* Silence is optimal. Every
  alternative is a charged action (Lemma C).

**Sequential rationality, excluded and free regions.** Each unconstrained
agent plays, in the perturbed game, a constrained best response to Bayes
beliefs under a fully mixed profile. The standard limit argument (Selten's
perfect equilibrium in agent form implies sequential optimality) gives
optimality at the limit assessment. The forced agents are fixed throughout and
do not affect this argument.

An excluded player's *gross* payoff is constant. The audit still charges its
further packets and its packets for events that never become ready for it, so
with the deposit, silence is optimal for it.

**Consistency.** The assessment is the limit of the Bayes beliefs of the fully
mixed profiles of the construction, with Nature and the builder fixed. This is
Kreps–Wilson consistency.

**Preservation.** On the limit path, every owner sends its free packet at its
first activation, and it is accepted before the deadline. So nobody is
excluded and nobody is charged. Bindings follow $\sigma^H$, samples follow
their source law, and the builder's randomness affects no public result. So
the joint law of public results and net payoffs is the honest one. $\square$

## 6. Why each change is needed

- **The failing player's payoff must not depend on how others continue.**
  This is the counterexample's mechanism. There, after a failed reveal of $b$:
  - Alice stays in play;
  - her later reveal of $t$ publishes $h$, which is correlated with $b$;
  - her payoff depends on Bob's guess;
  - Bob's guess depends on whether he saw the omitted opening.

  So the payoff after failure depends on both the type and the route, and
  Lemma B fails. Section 7 considers which weaker versions of exclusion would
  still do.
- **The first packet is never charged for not being included.** Suppose a
  dead first packet costs an expected $\alpha K(1-q)$. Then against silence, a
  late send is worth
  $$
  q\,(V-a_j)-\alpha K(1-q).
  $$
  The builder is chosen after the deposit, so it can pick $q$ with
  $\alpha K(1-q)/q$ strictly between $L_j-a_j$ and $U_j-a_j$. Types with a high
  continuation value $V$ then send late, and types with a low $V$ stay silent.
  Delivery behaviour reveals the type, and Lemma A fails.

  The current audit charges exactly this, since it charges authentic packets
  that are never included. Whether that charge alone yields a full
  counterexample is **not settled here**. It breaks this proof.

  Charging every *further* packet on every path is harmless (Lemma C). The
  charge falls on every path where the packet was sent, so it exceeds any gain
  that packet can produce.
- **Deposit $\alpha K_i>\Delta_i$.** Lemma C needs it. It depends only on
  payoffs and on the audit, never on the builder.
- **Charging every disclosure.** Without it, a free binding with attached
  evidence discloses a value verifiably, and the honest game's commitment
  order is lost (the Battle of the Sexes example after Lemma A).
- **Value-blind builder.** Lemma A needs the operational law to read no
  unopened value. A builder that reads commitment contents can correlate its
  records with hidden types.

`AsyncContract` is per event and holds on every legal history, so one player's
late success cannot shorten the next owner's window. That is why the
"failure shifted to another stage" negative of the
[whole-game delivery note](commit-reveal-research/whole-game-delivery-preservation.md#the-knowledge-and-realism-boundaries)
does not apply. In that negative, a player delays its own success so that the
next stage fails.

## 7. Must the game end at a failure?

No. What the proof needs is narrower than ending the game:

> After its own failure, the failing player's payoff depends neither on its
> type nor on the delivery route.

A fixed gross payoff $a_j<L_j$ is the simplest way to get that. Given it,
everything else about the continuation can be relaxed.

1. **The others continue under the program's failure semantics.** This is
   allowed, and the theorem proves it. Any continuation payoff of the others
   that is a function of public results works, as long as $\Delta_i$ covers
   it. Fail-stop (constants for everyone) is the special case.
2. **The excluded player's later actions.** With a fixed $a_j$, they need not
   be removed.
   - If $j$ keeps revealing or committing, that affects only the excluded
     region, which the construction leaves unconstrained.
   - Lemma B still holds, since failure gives $j$ exactly $a_j$.
   - Everyone else's forced-region incentives are unaffected. They reach that
     region only through their own charged action (Lemma C) or their own
     exclusion ($a_i$).

   Recording $j$'s later events as failures is a simplification, not a
   requirement. It becomes a requirement only if item 3 is relaxed.
3. **The failing player's payoff after failure.** This is the part that
   cannot simply be dropped.
   - The counterexample's compiler keeps it equal to the forfeit plus the
     program utility. Bob's later guess reads the failed opening he saw, so
     that payoff depends on both the type and the route.
   - Two things must then hold together, or some substitute for them:
     - the failing player takes no further action whose result becomes
       public. Otherwise, as with $t$ in the counterexample, a new or later
       publication can correlate with the leaked value;
     - the others' continuation does not read the route.

   A plausible but **unreviewed** version keeps the program utility. The
   excluded player gets its program utility (on public results, with its own
   results failed) minus a forfeit $D_j$. The sketch:
   - $j$ takes no further action; its later events are recorded as failures.
   - With an empty context and a value-blind runtime, every player's unopened
     values are conditionally independent of the others' given the public
     history. Each player's choices read only public data and its own
     commitments. So after exclusion, the excluded player's leaked values say
     nothing about the others' unopened values. They are also
     payoff-irrelevant, since they never become public.
   - The continuation can therefore be a lift, by this same construction, of
     an SE of the *residual* honest game (the program with $j$'s results
     failed). That works by induction on the number of active players.
   - The residual SE must be chosen as a function of the public *results*
     only, not of operational data. The failure record (expiry time, receipts,
     serials) depends on the delivery route, and the excluded player's
     continuation value $W$ must not.
   - $D_j$ must exceed $\sup u_j - L_j$, taking the supremum over histories in
     which $j$'s results failed. Then $W<L_j$, so $j$ still ranks delivery by
     $q_s$ alone.

   Three things remain to check:
   - the induction;
   - the route-independence of the selection;
   - that the excluded player's own further packets, which the audit charges,
     leave the lift sequentially rational.

## 8. Scope, relation to earlier notes, and what remains

- **Owner decisions.** Two changes depart from the adopted semantics.
  - *Exclusion* replaces the forfeit pass's continuation, in which the failing
    player keeps playing and its payoff keeps reading results. Nothing of the
    honest game is lost, since it has no failures.
  - *The free first packet* changes one clause of the adopted audit: a
    well-formed first packet that is never included is not charged. Everything
    else the audit charges stays charged, and it adds charges for disclosures
    and for further copies.

  The
  [delivery-control note](commit-reveal-research/delivery-control-preservation.md)
  describes a related variation (fail-stop with free retransmission) as "a
  different utility/accountability interface, not an authorized change to
  adopted semantics".
- **Realism of the audit.** The verdict reads content, tokens, per-author
  serials and the final record, as box A1 already requires of packet verdicts.
  It needs no send times. Counting "first packet per event" needs per-author
  serials, which the runtime allocates at emission. Seeing packets that are
  never included needs the watcher of box W.
- **Relation to the delivery-control note.** That note proves preservation for
  an abstract delivery interface: fixed-value send, wait and retry menus, with
  one controller per opening and the first failure ending play. This note
  specializes to the raw runtime of empty-context programs. That adds:
  - raw charged traffic (Lemma C, which needs the deposit);
  - unopenable and guard-violating bindings, late bindings and samples;
  - the `AsyncContract` builder class;
  - continuation after exclusion.
- **What exclusion enforces.** Whether a later event of $j$ succeeds is
  decided by the contract, which accepts no packet from an excluded player. So
  "the excluded player takes no further action whose result becomes public"
  is a contract rule, not a behavioural assumption. The theorem with a fixed
  $a_j$ does not even need that rule (Section 7, item 2).
- **Off-ledger disclosure.** A player can still hand its opening to someone
  else off the ledger. The audit sees only packets, so it cannot charge this,
  and verifiable evidence is exactly the Battle of the Sexes channel.
  Unverifiable claims are cheap talk, which the babbling construction already
  handles, and they are a stated limitation.

  A **proposed, unproved** deterrent is a disclosure bounty. Anyone who
  submits a valid opening of $j$'s commitment before $j$'s reveal has been
  accepted (or after $j$'s exclusion) triggers $j$'s charge and receives a
  bounty $b$ from it.
  - Reporting reveals the value to everyone, which can cost the recipient at
    most $\Delta_{\text{recipient}}$. So a bounty $b>\Delta_i$ for every
    potential recipient $i$ makes reporting dominant.
  - The sender is then charged surely: $K_j\ge\max_i b$ and $K_j>\Delta_j$.
  - Charges are then transfers, not burned, so every $\Delta_i$ must include
    bounty receipts.
  - Side payments between sender and recipient (collusion) are out of scope.
  - Adding the report action to the native game, and re-checking Lemmas A
    and C with it, is not done.
- **Concurrency.** Stage S only. With concurrent events, a player can see
  another's pending opening before making its own choice. Exclusion does not
  remove that front-running channel, so the concurrent stage needs its own
  analysis.
- **Mechanization must check.**
  - The projection $\pi$ on raw native information sets.
  - Value-blindness of the runtime's scheduler view, of the leak rule and of
    audit collection.
  - That `ProtectedInclusion` with a sole identifier, plus `AsyncTimely`,
    gives sure acceptance at the first activation. The property gives a
    receipt. Acceptance follows from the handle checks and from opening
    verification. Expiry cannot come first, because both clocks count from
    readiness. Precisely: expiry must not fire before clock
    `entered + delay + bound + 1`, which `AsyncTimely` gives.
  - That failure and expiry results are in every player's view at its next
    activation. Player views are the leaked packets plus the ledger, so check
    where expiry is recorded. Region disjointness needs this.
  - "First packet for $e$" means the lowest per-author serial among packets
    whose `payload.call.event?` is $e$ (`MessageNetwork.submit` allocates
    serials per author). Packets with no event address are not well-formed.
  - The audit verdict: the first well-formed packet per author and event is
    free; everything else is charged, including evidence about unopened
    candidates.
  - A builder that reads no such evidence.
  - Exclusion: later events of an excluded player complete as failures without
    becoming ready for it.
  - The coupling of Lemma C under the capped audit, with collection bounded
    below conditionally on every history.
  - The agent-form fixed point for the excluded and free regions.
  - Finite menus (serials and raw values bounded) and a finite horizon.
  - Finite payload types (assumption 1), which finiteness needs. The auction
    examples, with infinite payload types, are outside the theorem.
- **Builder-first.** Implied for this compiler: the deposit already does not
  depend on the builder.
