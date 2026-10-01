# Generalizing the sequential-equilibrium schedule

## Status

This is a design note; nothing in it is checked in Lean except the library
lemmas it cites. It describes which scheduling restrictions
`Vegas.Paper.source_audited_raw_sequential_equilibrium` imposes, compares
contract designs for ordering concurrent events, and lists the obligations of a
general theorem. Finite probes support the argument that preservation survives
adaptive orders. Design D1, open at readiness, is chosen (below).

## What the library no longer requires

The pinned GameTheory library defines sequential rationality on terminal play,
so a decision site no longer carries a remaining step count, and the pinned
theorem states standard sequential equilibrium of complete play. The following
results remove the equilibrium-theoretic reasons for a common decision clock:

- the one-shot deviation principle at consistent assessments,
  `BehavioralAssessment.IsSequentiallyConsistent.continuation_value_le_of_locallyOptimal`
  in [SequentialOneShot.lean](../GameTheory/GameTheory/Analysis/Protocol/SequentialOneShot.lean),
  assumes finitely many histories and decision recall but no clock;
- a site's mass is the probability that terminal play passes through it
  (`informationMass_eq_passage`), and Bayes beliefs transport along any history
  map whose reach weights sum exactly over its fibers
  (`bayesBelief_projection_of_reach`), both in
  [BeliefTransport.lean](../GameTheory/GameTheory/Analysis/Protocol/BeliefTransport.lean);
- Bayes beliefs also transport when the fiber sums are only a fixed positive
  finite multiple of the target weights
  (`bayesBelief_projection_of_proportional_reach` in
  [ProportionalBeliefTransport.lean](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean));
- extension across an action restriction needs no common decision depth
  (`ActionRestriction.sequentialEquilibrium_extends_of_continuation_unclocked`
  in
  [PassageRestrictionExtension.lean](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)).
  The library version in
  [RestrictionExtension.lean](../GameTheory/GameTheory/Analysis/Protocol/RestrictionExtension.lean)
  takes one at every retained site, only to read the site's Bayes belief off
  the prefix law of that length. The depth-free version reads it off terminal
  play: the belief in a site history is the probability that play passes
  through it, divided by the probability that play passes through the site.
  The history embedding preserves and reflects reachability, so passage
  through a retained site and through its image agree, and domination of
  terminal laws at the global horizon replaces domination at the common
  depth.

The full-language proof still uses a common depth in two places: the
fixed-depth Bayes projections of `Vegas/Game/SourceServiceBayes.lean` and
`Vegas/Game/RevealServiceRosterBayes.lean`, and the restriction extensions of
`Vegas/Game/SourceServiceRestrictionExtension.lean` and
`Vegas/Game/RevealServiceRosterAudit.lean`. The lemmas above can replace both,
but the continuation comparisons those extensions call
(`Vegas/Game/SourceServiceContinuationComparison.lean`) also derive their fuel
from the rank, so retargeting belongs with replacing the calendar (below).

## What the theorem fixes

The service of `SourceServiceSpec` is a fixed calendar:

- `SourceServiceSpec.scheduler` is `rosterScheduler`, which plays `rosterPlan`
  (`Vegas/Game/ServiceRoster.lean`). The plan visits every event in numeric
  order. Each event gets a fixed block: the roster activations,
  include-latest or sample, `event.val + 1` clock ticks, and expiry. The block
  issues no grant.
- The next instruction is selected by the length of the history. Only
  delivery, through the network policy, is randomized.
- The graph is `EventGraph.sequentialize` of the compiled graph
  (`Vegas/Game/RevealService.lean`), so every source-earlier event is a
  predecessor of every later one.

The pending-message theorems instead take an adaptive
`EventGraphRuntime.ServiceOrderPolicy`, which chooses each epoch's order from
the public pool, receipts, application projection, and environment history, and
work in either dependency mode.

In sequential mode a fixed order costs nothing: only one event is ever ready.
The restrictions that matter are:

- **Concurrent dependency mode.** Different players' bindings between two
  public events have no fixed relative order. Concurrent mode uses the compiled
  `barrierOrder` (`Vegas/EventGraph/Barriers.lean`): a public event depends on
  every earlier event and every later event depends on it, so only
  different-owner bindings between consecutive public events are concurrent.
- **An adaptive order.** Which concurrent binding is served first, and when,
  cannot depend on the history.

## Three layers of assumptions

The runtime model mixes assumptions about the chain, choices about the
contract the compiler emits, and assumptions about off-chain services. Only the
first layer is imposed on us; the other two are design choices, constrained by
what a contract can enforce. Fewer services are better: a service is another
party that must be live, and possibly one that must not be strategic.

| Model element | Realization | Layer |
| --- | --- | --- |
| Atomic inclusion with public accept/reject receipts (`Interaction.MessageApplication`) | Transactions and receipts; `none` from `handle` is a revert | Chain |
| `MessageApplication.submitStep`: a packet enters the observable pool | Broadcast to the public mempool | Chain |
| Wire policy: adaptive ordering and inclusion from the public pool | Block builder or sequencer | Chain |
| Reserved inclusion within the service's reaction rounds | Inclusion within a bound Δ (liveness, no censorship beyond Δ) | Chain |
| `clock`, `.advanceClock` | Block time | Chain |
| `handle`: readiness, deadline, owner and handle checks | Contract code | Contract |
| `State.activatedAt`, `deadline` (`Vegas/Pending/EventApplication.lean`) | Contract state and parameters | Contract |
| `.expire`, `.executeSample` | Anyone-can-call contract functions, applied lazily | Contract (effect), service (caller) |
| The order policy and the service calendar | Not enforced by `handle`. Prescribed clients, response menus and the audit read readiness: clients act at `PublicView.ownTurn?`, the least ready event the player owns (`no_turn_no_transmission` in `Vegas/Pending/ReactiveConformance.lean`), and the audit's conformance check requires readiness and ownership (`freshServiceEnvelope` in `Vegas/Pending/ReactiveServiceConformance.lean`) | Service |
| Disclosure reports feeding the audit | The watcher | Service |

The runtime used to carry a public service grant (a state field, set by a
grant environment command) naming the current event. It was a coordination
service the fixed-calendar proof depended on: prescribed owners transmitted only
when granted and the audit classified a fresh packet as conforming only for the
granted event. Since step 3 below, both use readiness instead, so a prescribed
owner acts exactly when a deviator could, and the calendar proofs identify the
event a decision belongs to by readiness or by the player's own response count.
The field, the command and the service instruction are deleted.

### Modeling priorities

Chain realism comes first; contract mechanisms are largely optimizations on top
of it. The target chain model is as asynchronous as the guarantees allow:

- every player may broadcast at every tick, reacting to everything public,
  including the mempool;
- the builder includes pending packets in any order and at any time, adaptively
  and exogenously (see strategic ordering below), subject only to a delivery
  bound: a packet broadcast at tick `t` is included by tick `t + Δ`;
- a prescribed client broadcasts within `r` ticks of its event becoming ready.

Bounded inclusion delay is the only synchrony assumption, and deadline
enforcement rests on it. It is Δ-censorship-resilience in the sense of
Wahrstätter et al.
([Blockchain Censorship](https://doi.org/10.1145/3589334.3645431), WWW 2024,
Definition 6): a transaction given to the honest validators is committed within
Δ except with negligible probability. Their measurements support it for
censorship by omission. After the Merge, 46% of Ethereum blocks were built by
actors censoring Tornado Cash transactions, yet those transactions were still
included, with a mean delay of 29.3 ± 23.9 seconds against 8.7 ± 8.3 seconds
for comparable uncensored ones. When a fraction p of proposers omit a
transaction, its wait exceeds k slots with probability pᵏ. Two conditions
remain:

- **A censoring minority.** Their Theorem 7 shows that no proof-of-stake
  protocol is censorship-resilient once more than half of the validators
  censor, including by refusing to attest to blocks that contain the
  transaction.
- **Deadlines sized against targeted censorship.** Their data concern blanket
  compliance censorship. The threat to a game is an opponent paying proposers
  to exclude one move until its deadline passes, which must succeed in every
  slot of the window (Winzer, Herd and Faust, "Temporary Censorship Attacks in
  the Presence of Rational Miners", IEEE EuroS&PW 2019, analyze such bribes).
  Each deadline should span enough slots that this costs more than the game's
  stakes.

The current service is more synchronous than this:
epochs visit events in an order, activate owners from a roster, and reserve
inclusion at the visit. Replacing that service by the Δ-bounded builder is part
of the work for D1 (below).

## Design alternatives for concurrent events

Four designs are realistic. All keep the barrier order, the owner and handle
checks, lazy expiry, and the disclosure audit.

**D1. Open at readiness.** The contract accepts a move for every ready,
unresolved event from its owner, and each event's timeout runs from readiness,
as `handle` and `State.refreshActivated` do today. There are no grants.
Prescribed owners submit as soon as their event is ready, and the builder
orders concurrent inclusions.

**D2. Self-granting contract.** The contract computes a current event from its
own state by a fixed public rule (for example, the least ready unresolved
event, or any rule over inclusions so far). It accepts moves only for the
current event, and the event's timeout runs from when it became current.
Concurrent events are served one at a time.

**D3. Service-issued grants, enforced.** A keeper issues grants and the
contract stores them. The first grant of a ready event starts its timeout;
later grants preserve it, since a service that revisits unfinished events
could otherwise postpone expiry indefinitely, and grants of unready events
start nothing. The contract accepts moves only for the currently granted event.

**D4. Service-issued grants, advisory, with long deadlines.** The current
model: grants are advisory and timers start at readiness. Each deadline is
sized to cover the longest delay the service can impose before the grant, for
example the number of concurrent bindings times the block length.

| | D1 | D2 | D3 | D4 |
| --- | --- | --- | --- | --- |
| Services beyond the watcher | none | none | a keeper | a keeper |
| Who orders concurrent events | builder | contract rule | keeper | keeper and builder |
| What the orderer can read | mempool, including pending certificates | contract state only | mempool | mempool |
| Can a player control the order | yes, as or by paying a builder | no | if a player can be keeper | yes |
| Timeliness from | `r + Δ < deadline` from readiness | `r + Δ < deadline` from becoming current | `r + Δ < deadline` from the first grant, and keeper liveness | deadline exceeds grant delay plus `r + Δ`, and keeper liveness |
| Latency of k concurrent bindings | one timeout | up to k timeouts | up to k timeouts | one long timeout |
| Out-of-order inclusion | is the adaptive order | impossible | impossible | possible (not enforced) |
| Change from today's model | honest owners submit at readiness; service no longer grants; audit authorizes by readiness | new contract state and gate | new contract state and gate, first-grant timer | deadline formula only |

The timeliness bounds are strict because `State.WithinDeadline` accepts a
packet only while the time since activation is strictly less than the
deadline: with deadline 1, a packet included one tick after readiness is
rejected. `r` is the client's reaction time and Δ the broadcast-to-inclusion
bound.

### Considerations

- **Services.** D1 and D2 need no service beyond the watcher and whoever calls
  `settle`/`expire`, which anyone may do. D3 and D4 add a keeper that must be
  live, and its order policy is modeled as non-strategic environment; if a
  player can act as keeper, that assumption fails.
- **Who can read what.** Only D2's order cannot depend on the mempool. The
  builder in D1 and the keeper in D3 and D4 can read pending packets,
  including certificates attached at emission. Under the barrier order the
  only concurrent packets are commitments, whose certificates are forbidden
  and charged (probe C3), so this matters only through the charge.
- **Strategic ordering.** In D1 and D4 a player can influence the order by
  building blocks or paying a builder. In the concurrent window the order can
  only change which of two hidden commitments is included first, and when; it
  can reveal who has already committed, never what. The target theorem keeps
  ordering exogenous: it has the shape "for every order, some sequential
  equilibrium", and the equilibria may differ between orders. It therefore
  says nothing about a player who deviates jointly in transmission and
  ordering, even when utilities depend only on the source outcome. Covering
  that needs a separate theorem in which the order is part of the player's
  deviation. What is uniform across orders is the retained behavior: every
  extension plays the compiled source profile at retained sites
  (`ActionRestriction.ExtendsProfile`), so only off-path completion and beliefs
  can depend on the order.
- **Timeliness.** Probe C1 shows the failure of today's model: prescribed
  owners wait for grants while timers run from readiness, so a third
  concurrent binding expires before its grant. D1 removes the wait. D2 and D3
  start the timer when the event is served. D4 enlarges the deadline instead.
- **Latency.** D2 and D3 serialize concurrent owners, so the worst case grows
  with the number of concurrent bindings. D1 does not.
- **What the proof must cover.** D2 fixes the order, but an adaptive public
  rule still makes it adaptive, so the general theorem is needed in all four
  designs unless the rule is a fixed permutation, which reduces to the
  existing theorem (see the narrower reductions). D1 and D4 additionally allow
  inclusion in any order the builder chooses; D2 and D3 exclude it.

### Decision

D1. It adds no service and no contract mechanism, has the least latency, and
matches the asynchronous chain model directly; the barrier order already
limits what an adaptive order can exploit to charged certificates and cheap
talk. Its costs are the inclusion assumption `r + Δ < deadline`, stated as a
chain assumption, a readiness-based audit, and a theorem that must cover every
builder order. D2 is the fallback if some adaptive order proves harmful: it
takes ordering away from anyone who can read the mempool, at the price of
serializing concurrent owners.

## Why preservation should survive

The theorem asserts that *some* target sequential equilibrium has the source
law. Off-path observations that carry no verifiable evidence can therefore be
neutralized through beliefs. Observations that do carry verified evidence
cannot, and the pending pool can contain such evidence (below). Here "the
order" means whoever orders concurrent inclusions: the builder in D1, the
contract rule in D2, the keeper in D3 and D4.

### A candidate counterexample and why it fails

A and B commit concurrently in a coordination game: each commits a bit, and
both receive one when the bits agree. At the source, B commits without learning
A's bit, and uniform mixing by both is an equilibrium. Suppose an adaptive
order serves B's event first exactly when the pool contains a replay broadcast
by A. Replays of published messages are permitted, so the audit never charges
them. A can replay when its bit is zero and stay quiet otherwise, and B can
read A's bit from the order.

This does not break existence. Choose trembles for A's replay that do not
depend on A's bit. B's beliefs after an off-path replay then stay at the source
beliefs, B ignores the signal, and A gains nothing by sending it. This is the
babbling equilibrium of cheap talk.

### What an adaptive order can and cannot read

The pending pool holds two kinds of content. A raw claim, such as an unwitnessed
opening, is unverified; an order that reacts only to such claims transmits
cheap talk, which beliefs can neutralize. A packet can also carry a sound
certificate, issued at emission rather than at inclusion
(`WitnessedSubmission.emit` in `Vegas/Pending/OpeningEvidence.lean`): a single
response can fix a fresh commitment and put its authentic opening into the
pool before any inclusion (`reactive_commitment_disclosure` in
`Vegas/Pending/ReactivePacketEvidence.lean`). An order that reads certificates
in the pool can therefore reveal verified values, and trembles that ignore
hidden values do not neutralize that.

The following effects cannot be neutralized through beliefs:

- **Hard evidence reaching a player before the source allows it.** Two cases
  differ.
  - *Forbidden certificates.* A fresh commitment is permitted only without
    evidence (`freshServiceEnvelope` in
    `Vegas/Pending/ReactiveServiceConformance.lean`), so a commitment that
    carries its own opening is charged. The extension bound for a forbidden
    action, payoff range minus the expected charge, holds under every
    continuation, including one in which the order reveals the certificate to
    others. The existing deposit therefore deters it; beliefs need not
    neutralize anything (probe C3).
  - *Permitted openings.* An opening is permitted during its own resolve event
    and carries a certificate. If it could sit in the pool while another
    player's binding is ready and unserved, an order reading its value would
    leak verified information on path, uncharged, and no assessment with the
    source law would be sequentially rational (probe C4). The barrier order
    rules this out: when an opening can be sent, every earlier binding has
    completed, and no later binding is ready until the resolution completes
    and the source publishes the value anyway. The case matters only for a
    dependency policy that lets a public event overlap a binding.
- **Changes to opportunities.** An order changes the relative order of
  different-owner bindings that are hidden from one another and, depending on
  the design, whether each owner still has a timely opportunity.

### The ordering contract

Whatever the design, a valid order for this purpose:

- is exogenous: chosen by no player, though it may adapt to the public
  history;
- serves only ready events, and reads only data public at that point (the
  mempool is public; under the barrier order this excludes early verified
  values other than charged ones);
- gives every ready event's owner a timely opportunity, whose source depends
  on the design (see the table);
- lets the audit record the actual service history as each message's phase;
- has bounded length, so the deposit and horizon remain finite.

An order that starves an event, or runs without bound, is outside the claim.

## Target: the general theorem

The goal is the strongest statement, not the reuse of the existing proof: for
the barrier-ordered concurrent runtime of the chosen design, every source
sequential equilibrium has an audited native sequential equilibrium with the
source law, under every exogenous order satisfying the contract. The fixed calendar, a
fixed permutation of concurrent bindings, and a public random order drawn up
front are special cases, so they need no separate theorems.

Design-dependent obligations:

- **Asynchronous chain model.** D1: replace the epoch service by the model of
  the modeling priorities above: every player may act at every tick, and an
  exogenous builder includes adaptively within Δ. The handler and timers are
  unchanged, and the service stops granting.
- **Timely opportunities.** D1: prescribed owners broadcast within `r` of
  readiness, and `r + Δ < deadline` for every event, strictly. D2 and D3:
  first-service timers and the current-event gate in `handle`. D4: deadlines
  exceeding the grant delay plus `r + Δ`.
- **Readiness-based audit.** D1 only. Both branches of `freshServiceEnvelope`
  require `serviceGrant = some event`, so without grants every fresh honest
  packet would count as nonconforming and be charged. Replace the grant
  condition by readiness and timeliness of the addressed event (the opening
  branch already checks both), then re-prove that the prescribed profile incurs
  no charge on path and that the extension bounds for forbidden actions still
  hold.
- **Out-of-order inclusion.** D1 and D4: the theorem covers it as part of the
  adaptive order. D2 and D3: `handle` excludes it.

Obligations common to all designs:

- **Phase from public history.** Replace the rank-indexed calendar,
  `DecisionPhase.position` together with `rosterPlanPrefix` and
  `rosterPlanSuffix`, by a phase read from the public service or inclusion
  history. About 94 files under `Vegas` refer to the roster plan. The
  replacement concerns the operational invariants, including the continuation
  comparisons that now derive their fuel from the rank.
- **Order-invariant continuations.** Prove that the compiled continuation law
  of the typed source readout is the same under every valid order, from any
  reachable public history. The pending-message laws prove this from the
  start of play; the general theorem needs it from arbitrary reachable states.
- **Proportional belief transport.** At information sets created by order
  choices, build beliefs from trembles that do not depend on hidden values, so
  that observers keep their source beliefs. Along a tremble sequence the fiber
  sums are only proportional: in probe C2 a source history of Bob has weight
  1/2 while the corresponding signal history has weight ε/4.
  `bayesBelief_projection_of_proportional_reach` covers this.
- **Retained-site depth.** An adaptive order breaks common decision depths
  without changing any player's information: an order that inserts zero or one
  wait before the same service step reaches the same information at different
  depths, because a wait updates only the environment's recall (probe C5 shows
  this is no obstruction to equilibrium). The depth-free extension covers
  this, so the contract need not make service steps public; the Vegas
  extensions still have to be retargeted onto it.

## Narrower reductions

Two reductions to the existing theorem remain available as intermediate
results, with narrower scope than the target.

- **A fixed permutation, by sequentializing along it.** Let π be a linear
  extension of the barrier order. It only permutes different-owner bindings
  between consecutive public events, which leaves each player's information
  unchanged; source sequential equilibrium is invariant under this interchange,
  unlike coalescing. Among the perfect-recall transformations of Thompson
  (1952), Dalkey (1953) and Elmes and Reny (1994), sequential equilibrium is
  invariant only to interchanging essentially simultaneous moves (Battigalli
  and Dufwenberg,
  [extra section 10 to "Belief-Dependent Motivations and Psychological Game Theory"](https://bpb-us-e2.wpmucdn.com/sites.arizona.edu/dist/3/21/files/2023/05/extra-section10-for-JEL-article_2022-09-01.pdf#page=2),
  2022, p. 2; Bonanno (1992) characterizes that invariance).
  If π is compiled into the dependency order, the runtime is the sequentialized
  graph of the permuted program, and the existing theorem applies to it
  directly; this is D2 with a fixed rule. A gated concurrent runtime with
  adjusted timers is a different protocol: its activation metadata, menus and
  audit observations differ, so reusing the theorem there needs an equivalence
  of the complete native protocols and information models. Equality of
  terminal store laws, as in `Vegas/EventGraph/Commutation.lean` and
  `Vegas/EventGraph/PolicyCommutation.lean`, does not transport sequential
  equilibrium.
- **A public random order drawn up front.** The draw is a public chance move at
  the root; every information set refines its outcome, so an assessment is a
  sequential equilibrium exactly when it is one on each branch, and the
  previous reduction applies branch by branch. This needs one generic lemma
  about public chance at the root.

Adaptive orders do not reduce to these: an adaptive policy is a mixture of
contingent plans only if the drawn plan stays hidden, and hidden chance merges
information sets across plans.

## Finite probes

`python scripts/experiments/adaptive_schedules.py` checks sequential
equilibrium in a concurrent coordination game whose source equilibrium mixes
uniformly. Beliefs are exact limits of an explicit tremble sequence, and every
whole replacement policy is compared at every information set; negative
controls confirm the checker rejects non-equilibria. Results:

| Probe | Target | Result |
| --- | --- | --- |
| C1 | Three concurrent bindings, deadline `event.val + 1`, blocks of `event.val + 1` ticks, owners waiting for grants | Timers from readiness expire the third binding; timers from the grant do not. |
| C2 | Order reacts to an unverified pool signal | An equilibrium with the source law exists (babbling). |
| C3 | Order reads a certificate on a forbidden commitment | An equilibrium with the source law exists exactly when the expected charge is at least the gain from revealing (here 1/2). |
| C4 | Order reads a permitted opening while the other binding is unserved (excluded by the barrier order) | No assessment with the source law is sequentially rational; an order blind to opening contents restores one. |
| C5 | An unobserved wait before the other player's service step | The translated profile is an equilibrium although its information set spans two depths: the depth requirement is a proof requirement, not an obstruction. |

C1 compares D4 without enlarged deadlines against D3's timers; D1, where owners
do not wait, is not probed. Under the barrier order C4 cannot arise, so the
probes support preservation in every design once timeliness holds. They are
design evidence, not proofs.

## Suggested order of work

1. **Finite probes**: done, above.
2. **Library lemmas**: done. The proportional-reach Bayes transport and the
   depth-free restriction extension are in `GameTheoryExtensions`. The
   contract need not make service steps public.
3. **D1 runtime.** The asynchronous chain model with a Δ-bounded exogenous
   builder, prescribed owners broadcasting at readiness with
   `r + Δ < deadline`, and the readiness-based audit with its zero-charge and
   deviation-bound proofs. Partly done: prescribed clients, response menus and
   the audit read readiness (`PublicView.ownTurn?`, `freshServiceEnvelope`),
   and `Vegas.Paper.source_audited_raw_sequential_equilibrium` is proved
   against them under the fixed calendar. The exogenous builder is not yet
   modeled.
4. **Phase from public history and order-invariant continuations.** Started:
   the roster calendar issues no grant, and a phase start is identified by its
   plan position (`sourceService_phase_boundary`). The watcher calendar issues
   no grant either; its decision depths are read from the public clock
   (`Vegas.decisionDepth` in `Vegas/Game/RevealServiceClock.lean`). The
   event-service stack serves owners at their turn, and the grant field and
   command are deleted.
5. **The general theorem**, with the fixed calendar recovered as an instance.
6. **Joint transmission-and-ordering deviations**, a separate theorem beyond
   the target, if players that can buy the order are to be covered.
