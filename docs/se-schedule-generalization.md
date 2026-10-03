# Generalizing the sequential-equilibrium schedule

## Status

This note separates the checked implementation kernels from the remaining
proof obligations. It describes which scheduling restrictions
`Vegas.Paper.source_audited_raw_sequential_equilibrium` imposes, compares
contract designs for ordering concurrent events, and lists the obligations of a
general theorem. Finite probes support the argument that preservation survives
adaptive orders. Design D1, open at readiness, is chosen (below). The
[completion plan](#completion-plan) records where the work stands and the
remaining milestones.

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

The full-language calendar proof still uses a common depth in two places: the
fixed-depth Bayes projections of `Vegas/Game/SourceServiceBayes.lean` and
the restriction extension of
`Vegas/Game/SourceServiceRestrictionExtension.lean`. The lemmas above can replace both,
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
  (`Vegas/Game/SourceServiceRuntime.lean`), so every source-earlier event is a
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
| Reports of observed signed packets, judged at settlement | The watcher, in its own transaction | Service |
| Settlement waits `W` slots after the report cutoff; the backend supplies positive conditional report-inclusion coverage | Inclusion of the watcher's transaction | Chain |

Readiness is the runtime gate. Prescribed owners and deviators can act when
their event is ready; the calendar proofs identify the event at a decision by
readiness or by the player's own response count. The runtime has no separate
grant command or grant cursor.

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
enforcement rests on it. The model assumes it exactly: every protected packet
is included within Δ, on every history. This is stronger than what a chain
offers. The closest chain property is Δ-censorship-resilience in the sense of
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

Even then the chain guarantee is probabilistic, and any positive probability of
a missed deadline breaks the exact claims: the native law would differ from the
source law, and a reached history could carry a charge. The exact theorem is
therefore stated for the bounded-delivery model. Transferring it to the
probabilistic guarantee is a separate, approximate result (see the completion
plan's other tracks). If each protected inclusion misses its bound with
probability at most ε, the native law should lie within total variation ε times
the number of protected inclusions of the source law, with the expected charge
bounded similarly.

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
order serves B's event first exactly when A's canonical commitment has already
arrived. Its public envelope carries the same handle for either bit. A could
send early when its bit is zero and defer otherwise, letting B infer the bit
from the order.

This timing signal does not by itself break existence. Choose A's timing and
its trembles independently of the bit. B's beliefs after an off-path timing
choice can then remain the source beliefs, B ignores the signal, and A gains
nothing by changing its timing. This is the babbling-equilibrium argument for
cheap talk; verifiable content needs a separate analysis.

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
  unchanged, and the service no longer grants (done). The completion plan
  states the model as a contract on schedulers.
- **Timely opportunities.** D1: prescribed owners broadcast within `r` of
  readiness, and `r + Δ < deadline` for every event, strictly. D2 and D3:
  first-service timers and the current-event gate in `handle`. D4: deadlines
  exceeding the grant delay plus `r + Δ`.
- **Readiness-based audit.** D1 only. Done: `freshServiceEnvelope` authorizes
  a fresh packet by readiness and ownership of the addressed event, with no
  service cursor. Still to re-prove for a general scheduler: no charge on path
  for the prescribed profile, and the extension bounds for forbidden actions.
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
| C6 | One guaranteed turn, deferral with weight ε, a late turn granted with probability p, a public charged miss (`deferral_miss_probe.py`) | The compiled image of the penalized-miss extended source is an equilibrium with the source law exactly when the deposit is at least Alice's gain from a miss (here 1/2), for p in {0, 1/2, 1}. A grant probability that depends on the owner's value breaks the route at the turn-2 acceptance, not only after a miss. |
| C7 | One escrow, private attempted-choice recall, raw play at late first binding opportunities and after public misses (`raw_continuation_probe.py`) | Rational raw completion preserves protected source play in the checked coordination games. Opening raw play only after an attempt is too late: a content-dependent builder can make an evidence-bearing first packet cheaper than a public miss. Collection and private recall controls are checked separately. |

C1 compares D4 without enlarged deadlines against D3's timers; D1, where owners
do not wait, is not probed. Under the barrier order C4 cannot arise, so the
probes support preservation in every design once timeliness holds. They are
design evidence, not proofs.

C6 tests the penalized-miss route below. Alice's private value v is uniform;
she commits a = v, and Bob, without seeing it, plays matching pennies or a
coordination game. After a public miss Bob aborts (worth 1/3 to him) or
proceeds (worth v), so his post-miss play depends on his belief about v;
Alice gains 1 if he proceeds, minus the deposit D. The extended source's
equilibrium supplies post-miss play (proceed, under the prior belief); its
compiled image, in which a late turn repeats the source action and Bob ignores
timing, has Bob's limit beliefs equal to the extended source's at every
information set and is a target equilibrium exactly when D >= 1/2. Deferring
and then playing x is worth exactly the mixture of a miss and x to Alice.
Controls fail as expected: with D = 0 deferring and staying silent pays; a
Bob who aborts after a miss violates sequential rationality there. When p
depends on v (1/4 and 3/4), the post-miss belief moves off the prior, and
even with the extended source's miss trembles set to match it, acceptance at
turn 2 reveals v and Bob's timing-blind play fails there. So the mixture
condition must exclude the owner's own private values: the grant probability
must not vary across the histories inside any other player's information set,
which a function of public data satisfies. Existence itself survived that
control, through profiles the route does not construct. The deposit
threshold is sufficient, not necessary: with 1/2 <= p < 1 there are equilibria with the source law for every D <= 1/2 in
which value 0 stays silent at a late turn just often enough that Bob is
indifferent after a miss. With p = 0 or p = 1 the searched family has none
below the threshold. Timing works as cheap talk only with a free late turn
and common interest (coordination, p = 1), where a separating equilibrium
exists alongside the source-law one; the source-law equilibrium exists in
every case probed. The probe has one binding, one other player and a binary
value; it does not test several pending bindings or a builder whose grant
depends on other players' actions.

## Completion plan

This section is the plan for finishing the work. Like the rest of the note it
is a design, not a checked result.

### Where the work stands

| Step | State |
| --- | --- |
| Finite probes | Done (above). Design evidence, not proofs. |
| Library lemmas | Done: proportional Bayes transport and the depth-free restriction extension in `GameTheoryExtensions`. |
| Readiness instead of announcements | Done. Prescribed clients, response menus and the audit read readiness (`PublicView.ownTurn?`, `freshServiceEnvelope`); the service grant is deleted from the runtime. The calendar menu's required decision at the owner's last visit (`decisionRequired`) still reads the roster. `Vegas.Paper.source_audited_raw_sequential_equilibrium` is proved against this, still under the fixed calendar. |
| Asynchronous chain model | The contract is `AsyncContract` with per-event bounds and `AsyncTimely` (`Vegas/Pending/ReactiveAsyncContract.lean`); `rosterScheduler_asyncContract` proves the fixed calendar an instance with reaction bounds `event.val` and inclusion bound 0 (`Vegas/Game/ServiceRosterAsync.lean`). `prescribed_packet_settles` proves timely acceptance for the turn-counted policy (`Vegas/Game/SourceServiceAsyncTimeliness.lean`). |
| Phase from public history | Started: `sourceService_phase_boundary` identifies a phase start by plan position, and the calendar reads decision depths from its fixed roster. `DecisionPhase.position` and the roster plan prefix and suffix still index the calendar. |
| Completion-stopped phase law (milestone 2a) | Done. `Interaction/ReactiveStopping.lean` splits a scheduler run at a stopping predicate. `SourceServiceSiteBridge.lean` uses the position-free `ReadySite` to derive completion boundaries and exact or `WithinTV` response bridges for any scheduler that completes play. The bridge applies to responses supported from initialization, and to every legal response under a fully mixed admissible menu assessment. `sourceServiceTurnPolicy_initialized_lawError` bounds the initialized outcome error by total deferral weight. `SourceServiceContinuationBridge.lean` separately instantiates the exact boundary law for the calendar. |
| Turn-counted policy and approximate continuation (milestone 2b) | Done for every contract scheduler. `sourceServiceTurnPolicy_boundaryContinuationWithin` bounds the distance from the source continuation by the sum of the remaining events' deferral weights, and `sourceServiceTurnPolicy_firstTurnCompletes` discharges its hypothesis from `AsyncContract` and `AsyncTimely` alone (`Vegas/Game/SourceServiceFirstTurnCompletes.lean`). The calendar keeps its timed policy. |
| Audit serial clause | Done. The audit's per-packet rule counts distinct identifiers per author (`Interaction.Message.distinctAuthoredCount`), so repeated evidence of one envelope does not shift serials, and the contract rejects a re-inclusion (`EventGraphRuntime.handle_eq_none_after_accepted_run`). Under `AsyncContract` alone, every fresh call of a player following the turn-counted policy, trembles included and whatever others do, carries the audit's serial and passes the full rule (`Vegas.sourceServiceTurnPolicy_serial`, `Vegas.sourceServiceTurnPolicy_permittedServiceEnvelope` in `Vegas/Game/SourceServiceCanonicalSerial.lean`). |
| Explicit decision packets | A selected false disclosure sends authenticated evidence-free withholding; silence remains deferral. The runtime completion, packet/audit laws, general first-turn safety, timing posteriors, calendar prefix factorization and calendar Bayes kernels pass strict checks. Every actually recorded prescribed decision completes with an accepting receipt for its original packet under the asynchronous contract. The full fixed-calendar composition, including actual final-miss repair and the capstone axiom pins, passes the warning-strict project build. The arbitrary-builder equilibrium proof remains open. |
| Source-conditioned traffic | Actual canonical binding and effective disclosure responses, and actual public sampling, have joint source-successor/traffic factorization laws. Recorded resolution continuations preserve the carried source-conditioned full traffic law through actual stopping. Exact clean-prefix probabilities survive arbitrary completion away from source-compatible information. Source-state agreement at stopped completion, relative escape bounds and native source-belief transport remain separate obligations. |
| Owner-local prescribed safety | Exact first-turn play keeps the owner's full `serviceRisk` flag clear at every supported control (`Vegas/Game/SourceServiceFirstTurnSafe.lean`). For any turn timing, every authored packet is permitted by the actual settled record (`Vegas/Game/SourceServiceOwnerSettled.lean`). Combining packet soundness with first-turn absence of public misses gives zero owner charge under authentic sampling, against arbitrary foreign raw policies. `AsyncServiceSpec.normalizedFirstTurn_joint_law` preserves the complete typed source outcome and actual sampled payoff vector jointly for every source profile, after disclosure normalization. Initial private parameters remain correlated with public outcomes. These execution laws do not prove sequential rationality. |
| Canonical retained menu | `MessageBounds.canonicalMenu` retains silence and bounded first canonical decisions under `WithinDeadline`, with no roster obligation. Local source-choice coverage and no second submission are proved in `Vegas/Pending/ReactiveCanonicalMenu.lean`. Used-slot and own-submission invariants hold on every legal retained history (`retainedCanonicalSlots_history`), including after misses. The prescribed policy is admitted at every such history (`sourceServiceTurnPolicy_retained` in `Vegas/Game/SourceServiceRetainedPolicy.lean`), including arbitrary turn timing. Equilibrium after misses remains open. |
| Continuation after risk | The candidate `MessageBounds.riskMenu` opens an owner's bounded raw menu at a ready, unrecorded owned decision outside protected inclusion, or after its public miss or own recalled unprotected attempt. Any own response recalls that unprotected opportunity, including silence; protected recorded decisions, including explicit withholding, stay clear. Slot invariants use persistent risk separately from the current opportunity. Prescribed transmissions add no submission risk for any turn timing; silently deferring into a late owned opportunity may add opportunity risk. Actual post-miss rationality equals base-payoff rationality (`serviceAudit_rationalAt_iff_of_miss`). `LocalizedEnforcement` separates charged exclusions from private continuation comparisons, including retained charges. Source embedding, general command closure, beliefs and concrete comparisons remain open. |
| General theorem | `AsyncServiceSpec`, the fixed deposit, geometric deferral bounds, the local retained menu and a fixed clean comparator are present. The initialized joint execution/settlement law is checked. Conditional enforcement of the classified auditable packets extends an actual audited risk-menu SE to the complete effective menu; exact alias transport supplies the bounded raw-runtime stage. Source SE embedding into that auxiliary game, joint native beliefs, the other comparisons and general repair remain open. |

The pending-message stack (`Vegas/Pending/EventService*.lean`,
`EventPrescribed*.lean`) separately proves exact honest and deviation laws and
ε-Nash preservation under an adaptive `ServiceOrderPolicy`, but not sequential
equilibrium. Its epochs still stage resolutions over three owner calls.

### End state

One theorem replaces the fixed-calendar capstone. Roughly:

> For every `SourceServiceSpec` whose scheduler satisfies the asynchronous
> contract below with reaction bounds `r` and inclusion bounds `Δ`, and whose
> owned events satisfy `r event + Δ event < deadline event`, every source
> sequential equilibrium
> has an audited native sequential equilibrium with the source joint law of
> the typed terminal state and payoff, and no player is charged on any history
> the native equilibrium reaches.

Since the scheduler is part of the spec, it is fixed before the source
equilibrium is chosen: this is the "for every order, some equilibrium" shape
of the decision above. The deposit and the horizon are computed from the spec,
so they may depend on the scheduler. The fixed calendar becomes one instance:
a lemma shows that `rosterScheduler` satisfies the contract with
`r event = event.val` and `Δ event = 0`. The delays must be per event. When an
event completes at its inclusion, the rest of its block, `event.val + 1`
ticks, runs before the next event's owner is activated. So event `e` waits
`e.val` slots after becoming ready. That fits its deadline `e.val + 1`, but no
single bound fits every event: event 0 has deadline 1.

### The asynchronous model is a scheduler contract

The runtime needs no new semantics. `ReactiveApplication.protocol` already
lets an environment scheduler choose each command from the public environment
history and view: whom to activate, which packet to include, when to advance
the clock, when to expire or sample. The rows of the modeling priorities above
become properties of that scheduler. A *slot* is the stretch of environment
history between two consecutive clock advances.

A scheduler satisfies the asynchronous contract (`AsyncContract` in
`Vegas/Pending/ReactiveAsyncContract.lean`) when, at every legal history of the
raw protocol, including off-path ones:

1. **Opportunity within `r event`** (`Opportunity`). Once an owned event has
   been ready for more than `r event` slots, its owner has been activated since
   it became ready. Further activations of anyone are allowed.
2. **Protected inclusion within `Δ event`** (`ProtectedInclusion`). When the
   owner has authored a packet addressed to its event while the event was
   ready in slot `t`, and every packet of its own that the owner ever emits
   for that event carries the same identifier, that packet has a receipt by
   the end of slot `t + Δ event` unless the event has completed. Including any
   other packet, in any order, is allowed. This is today's reserved
   `ServiceInstruction.includeLatest`, stated as a deadline instead of a
   calendar position. Only the sole identifier is protected, and only the
   owner's own other identifiers void the protection (`EmitsOtherFor` counts
   only packets authored by the owner). A fresh call by another player, even
   one addressed to the owner's event, does not void protection: the builder
   tells authors apart by signature, and the calendar's selector never picks
   a foreign packet. A prescribed owner submits one packet of its own per
   event. Packets with several identifiers
   from one owner for one event are deviations, whose law the scheduler may
   shape (milestone 5).
3. **Complete play** (`CompletesPlay`). Every legal terminal state has
   completed every event. This replaces lazy settlement and a per-slot bound
   in the formal contract: the horizon is fixed, and the scheduler must sample,
   include or expire every event within it.

Finite branching is the separate `FiniteNature` instance, as for the network
policy today. The horizon is part of the service; today it is the calendar's
`planLength`, and the general spec must carry it as a field.

Requirement 1 asks only for the first opportunity. Repeated activations are
realistic and allowed, but the theorem needs only that a prescribed owner can
act in time. Together 1 and 2 give a prescribed packet's inclusion within
`r event + Δ event` slots of readiness, so `r event + Δ event < deadline event`
makes it timely. This is the timeliness row of the D1 column, now a lemma
rather than a property of a plan. The chain model of the modeling priorities
is the special case of constant bounds.
The contract is exogenous: it constrains the scheduler and nothing else, and
the scheduler reads only public data, including the mempool, as the D1 column
says.

Every player may still act at every slot: a scheduler that activates everyone
in every slot satisfies the contract. The theorem quantifies over all such
schedulers, including the fully asynchronous builder of the modeling
priorities.

### What the fixed calendar supplies today, and its replacement

The proof uses the calendar through the plan position of a decision
(`DecisionPhase.position`, `rosterPlanPrefix`, `rosterPlanSuffix`). Position
does four jobs. Each gets a schedule-independent replacement.

1. **Which event a decision belongs to.** On the sequentialized graph exactly
   one event is ready, so the decision's event is the sole ready event of the
   public view (`soleReady_of_ready`). `DecisionPhase` keeps its event and
   readiness fields, and drops `slot` and `position`.
2. **The continuation law from a decision.** Today the continuation is the
   rest of the plan, evaluated block by block. The replacement is a
   *completion-stopped phase law*: run the scheduler until the current event
   completes, a stopping time. Where the run starts matters.
   - At a stopping point every next event is *untouched*: completion happens
     only through inclusion, sampling or expiry, which have no actor, so no
     player has yet responded while the next event was ready. From an
     untouched boundary the typed source readout at the next completion has
     the source step law under every contract scheduler: a sample for an
     actorless event, the owner's value for a binding, the publication for a
     resolve.
   - Inside a phase there are three cases: the owner is undecided (the source
     kernel), the owner decided and has a pending sole packet (a point mass at
     its value, given timely acceptance), or the owner decided to stay silent
     (expiry: failure for a binding, withholding for a resolve). For example,
     a pending commitment to `0` makes the completion law a point mass at `0`
     even though the source decision mixes.
   - The readout does not change after completion, because completed fields
     are preserved (`EventStore`). Chaining the step law over the remaining
     events gives the source continuation law by induction on the number of
     unfinished events, not on plan length. Fuel comes from the rank, which
     every scheduler decreases, so the `2 * horizon + 1` bounds carry over.
   - At the calendar, the stopped law equals today's block law only on
     configurations: the block keeps ticking and expiring after completion,
     which changes only the clock. And calendar completion boundaries lie
     inside the predecessor's block, not at block starts.
   - The bridge needs only the marginal law of the readout. The joint
     factorization with the focal player's traffic noise is for beliefs
     (milestone 4).
3. **Deviations.** Under the limit policy the phase law is the same for every
   scheduler; the fully mixed approximants match it only up to their deferral
   weight. A deviating owner can emit several packets for its event, and
   then the builder's choice among them makes the resulting value a lottery
   that depends on the scheduler. The required fact is that this lottery is a
   mixture of source actions of the same player: the builder reads only the
   public pool, where commitment payloads are handles and certificates are
   charged. This is the analogue of the pending-message stack's
   "source-policy mixture" deviation law, at phase granularity.
4. **Decision depth for beliefs and extension.** Replaced by the depth-free
   extension (`ActionRestriction.sequentialEquilibrium_extends_of_continuation_unclocked`)
   and proportional belief transport
   (`bayesBelief_projection_of_proportional_reach`). Information sets created
   by the scheduler's choices, such as an extra wait, a non-owner activation or
   inclusion timing, get beliefs from trembles that ignore hidden values (the
   babbling argument above). The fixed-depth Bayes projections and restriction
   extensions listed under "What the library no longer requires" are
   retargeted here.

The audit needs no new idea: `freshServiceEnvelope` already authorizes by
readiness and ownership. What must be re-proved is zero charge on path, which
follows from timeliness, and the extension bound for forbidden actions under
every contract scheduler. The bound already holds under every continuation.
The deposit formula `rosterAuditDeposit` is re-derived from the contract's
length bound instead of the roster plan.

### Stage A and stage B

**Stage A: sequentialized graph, every contract scheduler.** This removes the
fixed calendar. With one ready event at a time, the scheduler can change only
timing: when owners are activated, when packets are included, and which of a
deviator's packets wins. It cannot change which event is decided next.
Everything above is stage A.

**Stage B: barrier order, concurrent bindings.** Different owners' bindings
between two public events are then ready together, and the builder orders
their completion. The additional obligations are:

- **Commutation.** Completing two concurrent bindings in either order gives
  the same source readout. They are different events with hidden values, and
  each value depends only on its owner's packet.
- **Timing information.** A player may see that another concurrent binding
  has completed, through its accepted handle, before acting. The source stage
  does not reveal this. The compiled profile ignores it, and native sites that
  see it are extended by the depth-free extension with beliefs from
  value-independent trembles. The order reveals *who* committed, never
  *what*.
- **Certificates in the pool.** Only commitments are concurrent under the
  barrier order, and a commitment carrying evidence is forbidden and charged
  (probe C3). The extension bound covers this. Permitted openings never sit
  in the pool beside an unserved binding (probe C4 cannot arise).

Stage B reuses stage A's phase law with a set of ready bindings in place of a
single ready event. The phase completes when every binding between the two
public events has completed.

### Other tracks

- **Pending-message stack and staging.** After the general theorem lands,
  decide per theorem whether to retarget its honest law, deviation law and
  ε-Nash results onto the contract or to retire them as subsumed. Before that,
  collapse the three-call resolution staging to one activation per event, as
  the reactive policy already does, and recheck the per-event block and epoch
  layout against the contract: an epoch service should become one contract
  scheduler, not a separate model.
- **Source-side service cursor.** The selective-association source fixture
  (`SourceService.lean`) keeps a `visit` cursor that makes its actions
  stage-local. Removing it changes that source contract, so it is a separate
  design decision.
- **Probabilistic delivery.** The exact theorem assumes bounded delivery on
  every history. A separate result should bound the distance to the source law
  and the expected charge when each protected inclusion can miss its bound
  with small probability, matching the chain guarantee cited above.
- **Joint transmission-and-ordering deviations.** A separate theorem in which
  the order is part of a player's deviation. Not part of this plan.
- **Fresh envelope identifiers.** Responses are silence or fresh submissions.
  A submission allocates a sender-owned identifier, and inclusion consumes it
  whether the call succeeds or fails. Repeating a payload uses a fresh
  identifier; forwarding a known certificate retains the authentic fact
  without copying its envelope. The handle-owner check rejects a fresh call
  that claims another player's handle. Backend propagation and replacement
  behavior need a separate refinement; they are not packet-copy actions in
  this model. The distinct-identifier audit count detects extra signed calls.
- **Packets are judged against the settled record (decided).** The
  per-packet check (`EventGraphRuntime.permittedServiceEnvelope`) judges a
  packet against the public view at the moment it was sent, but an auditor
  cannot prove send time. Two changes replace that.
  - *Readiness tokens.* Once an event's direct prerequisites have completed,
    packets for it carry a token naming the event. The sender never writes
    it: it is attached at emission from the contract state the sender sees,
    so a packet made before readiness has none, exactly. The token carries
    no creation time and is valid only for its own event, so pretending a
    packet is older is not expressible. On EVM it is a hash of the
    completing block.
  - *Settled-record verdicts.* "Too late" cannot be a token property, and it
    matters: an opening sent after its owner withheld is verifiable
    disclosure, not cheap talk, and would let a withholding owner reveal
    for free. So a packet's verdict is a function of its content and the
    contract's final record: for example, an opening for an event settled
    without that disclosure is a violation, whenever it was sent. A
    prescribed owner whose opening misses inclusion is charged, as for a
    missed binding. The remaining send-time reads (accepted handle, guards,
    canonical slot) are reconstructed from the record; the serial gives way
    to equivocation evidence (two signed packets of one author for one
    event).

  The audit theorem is the strongest we can prove; the watcher is the
  weakest, most realistic design that still supplies the evidence the audit
  needs, and may be split into several watchers if that is easier to prove,
  since only the semantics matters. It reports with its own transaction
  carrying the signed offending packets, and the contract decides at
  settlement. Observation continues after the gameplay deadlines, through a
  monitoring phase before the report cutoff. The challenge-window hypothesis
  sets a `W`-slot delivery window for reports submitted by that cutoff, and
  settlement waits until that window ends. The backend supplies a positive
  conditional probability of timely inclusion. This is
  distinct from a gameplay packet's inclusion bound. The watcher need not see
  every offense. Its conditional probability of actual collection, including
  observation and report delivery, must have the positive lower bound used
  to size the deposit. Deriving that bound from the pending-message runtime is
  a backend obligation; `AsyncContract` alone does not supply it.
- **Off-chain and covert-channel talk is a stated limitation**, verifiable or
  not. A withholding owner can always prove its value off-chain by showing
  the commitment's opening; no on-chain mechanism can catch that, so it is
  hard evidence outside the model, unlike cheap talk.

### Milestones

Each milestone ends with the full build, the checkers and the paper pins green,
and is committed separately.

1. **Contract.** Done: the contract with per-event bounds, and the instance
   `rosterScheduler` with `r event = event.val` and `Δ event = 0`. The
   timeliness lemma for prescribed play moves to milestone 2b, with the
   prescribed policy it is about.
2. **Completion-stopped phase law.** The bridge
   `TimedApproximant.response_continuation_law` is tied to the calendar
   through more than `DecisionPhase.tail`: the two lemmas it calls state
   support and continuation under plan prefixes, and the prescribed policy's
   `timing` (which of the owner's visits in a block makes the source decision)
   is a calendar lottery. Split in two.
   - **2a, on the calendar.** A stopping-time runner in `Interaction` (run
     until a predicate, the decomposition of a full run at the stopping time,
     fuel monotonicity, trace and support lemmas); the generic local law and
     full-mixing reachability for any scheduler; the completion law and
     untouched boundaries; the generic bridge under an explicit hypothesis
     that the continuation from every untouched boundary is the source
     continuation; and the calendar instance of that hypothesis, from which
     today's bridge is re-derived. The pinned theorem is unchanged.
   - **2b, the prescribed policy.** Under the contract only the first
     activation is guaranteed. The limit policy therefore decides once, at
     the first activation where the event is the player's turn. The retained
     menu cannot follow it. The extension lemma
     (`ActionRestriction.sequentialEquilibrium_extends_of_continuation`)
     quantifies over every target profile that extends the source, so a
     removed action must be dominated however opponents play off the retained
     sites. Silence itself is uncharged but can lead to a charged public miss.
     Deferral is visible: staying silent
     at the first turn and acting at a later one is visible through leaks,
     inclusion timing and the scheduler's view of the pool. So deferral stays
     retained, and the fully mixed approximants must give it positive weight.
     Under a scheduler that activates the owner only once, deferral ends in
     expiry, so the approximants' laws differ from the source law by the
     deferral weight. Exact approximants survive only on the calendar, where
     every visit is realized. The design is therefore:
     - the limit policy decides at the first turn, and approximants defer
       with weight `ε n` tending to 0, indexed by the owner's own turn count;
     - the retained menu keeps every timing: today's menu without the
       requirement to bind at the last visit, whose repair is then deleted;
     - the equilibrium limit lemma takes a vanishing total-variation error
       instead of an exact initialized law, with the exact version derived;
     - the boundary-continuation hypothesis carries an error, bounded by the
       sum of deferral weights over the remaining events.

     Done: the library limit lemma with vanishing error, and a turn-counted
     variant of `scheduledPolicy`. The calendar keeps today's offset-keyed
     timed policy: moving it onto the turn-counted policy first would need a
     new per-block recall invariant and patches to about 60 calendar proof
     sites, all of which the general theorem supersedes, since the calendar
     becomes one of its instances. So the turn-counted policy, the timeliness
     lemma and the approximate step law are built in new modules for every
     contract scheduler, and the calendar-specific chain is retired at
     milestone 6 rather than ported. The same argument applies to milestone
     3, which is reconsidered once the general step law exists.

     Also done: event-wise total variation (`PMF.WithinTV`), the mixture
     disintegration of scheduler runs, the turn-counted policy
     (`sourceServiceTurnPolicy`), and the timeliness lemma
     (`prescribed_packet_settles`: an owner's sole fresh conforming packet is
     accepted in time and the event completes only through it).

     The step law is milestone-sized. Deferral is the only error, but showing
     that the first turn completes the event with the drawn value needs
     scheduler-generic versions of what the calendar proves along its plan:
     admissibility of the turn policy; decoding every reached configuration
     to a source checkpoint; realizing the first-turn draw as a mixture over
     values; and the decision resources (fresh candidate slots, serials) that
     make an accepted binding carry exactly the drawn value. These hold on
     the support of the turn policy, trembles included, not under arbitrary
     deviations. The step law and its chaining are proved first under a named
     hypothesis that the first turn completes the event, then the hypothesis
     is discharged. Both are done: the discharge needs no condition on
     payload values, catalogue capacity or admission, only effective
     disclosures of the source profile. Timeliness must prove acceptance and the
     absence of early expiry, not only a receipt. The step law's invariant
     keeps the pool for the current event to one owner identifier and makes
     deferral the only error.
3. **Phase without position.** Dropped. The calendar chain is retired at
   milestone 6 rather than ported, and the position-free site datum (event,
   readiness, sole readiness) is a small definition inside the generic bridge
   of step 6 below.
4. **Depth-free extension and proportional beliefs.** Retarget the
   fixed-depth Bayes projections and restriction extensions, including the
   joint factorization with traffic noise; build beliefs at scheduler-created
   sites.
5. **Deviation lottery.** A second own identifier for an event is
   nonconforming whether or not the first was published. At a clear,
   protected history, collection coverage and a clean legal continuation can
   deter it. A charged history needs a separate comparison: a one-time
   deposit does not pay again for each nonconforming packet. The builder's
   response to public packet contents also matters at a late first binding
   opportunity, before any attempt or public miss. Probe C7 checks both
   obstructions and rational raw continuations in finite games (see
   "Monitoring and punishment").
6. **General theorem, stage A.** Prove the capstone for `AsyncServiceSpec`,
   with its arbitrary contract scheduler and horizon, and pin it in `Paper.lean`. The
   fixed-calendar theorem becomes a corollary through milestone 1's instance.
   The proof chain is:
   1. `AsyncServiceSpec` (scheduler, horizon, delay, bound, contract, finite
      nature) and the calendar instance.
   2. The deposit over `(horizon, scheduler)` and its gain bound.
   3. The public deadline gate for prescribed calls and the final-record audit.
      The audit cannot reconstruct send time or reject an accepted canonical
      call solely because its guaranteed delivery bound would have been too late.
   4. Geometric deferral and source trembles must have compatible relative
      rates at every prescribed site. Every selected owned decision sends a
      packet, including false disclosure. Protected silence therefore excludes
      that timing index independently of the source value. A closed unrecorded
      owned opportunity opens the risk menu; its continuation is completed as
      a free site. Joint source-relative beliefs and prescribed-site rationality
      still need proofs.
   5. The canonical retained menu and its lemma suite. Retain silence and
      canonical calls that can still be accepted, including calls outside
      the prescribed policy's protected-inclusion gate. Delete the roster
      rule `decisionRequired` when its calendar callers are replaced.
   6. Use `ReadySite.response_completion_within` and its completion-boundary
      theorem for any scheduler. Actual policy-supported responses supply
      the needed support through `sourceResponse_roundSupported`; legal
      one-shot deviations need a fully mixed menu or changed-profile witness.
   7. Embed each source equilibrium into the actual audited risk-menu game.
      Retained deferrals can miss and be charged; zero charge is required on
      final equilibrium-supported play. Identify source-compatible information
      sites, including protected deferrals, and supply rational completion at
      the other sites. Carry the source-view traffic factorization through
      decisions and disclosures as well as silent binding rounds.
   8. Milestone 4's beliefs.
   9. Generic local comparisons for every site kind, each bound with
      `BoundaryContinuationWithin`.
   10. Generic source-to-compiled step through
       `exists_sequentialEquilibrium_limit_of_local_comparisons_of_lawError`.
   11. Generic repair coupling (same public state, different private
       catalogue, round by round), the second-identifier lemma, and the
       compiled-to-native step through the depth-free extension.
   12. The new capstone, the calendar corollary, and retirement of the
       calendar chain.

   Steps 1, 3, 4 and 6 are independent. After step 5, steps 7 and 11 run
   alongside steps 8, 9 and 10.
7. **Stage B.** Barrier-order graph: commutation, timing information,
   concurrent phase law.
8. **Pending-message stack.** Collapse staging, express the epoch service as
   a contract scheduler, and retarget or retire.

Milestones 2, 4 and 5 also apply to the fixed calendar. Shared runtime changes
require its callers to be checked again; milestone 6 generalizes the capstone.

### Waiting, misses and the charge

The source is an idealization; the target must be realistic and the source
must compile to it. In the target, waiting is a real option: an owner who
waits gives up inclusion probability in exchange for a later, possibly better
informed decision. Within one game the builder is fixed, so that price is a
well-defined probability, and a builder that grants no second turn makes
waiting expensive.

What waiting buys depends on the graph and the actual information history.
On the sequentialized graph no other source event completes while an owner's
event is ready. Passive packet observations can nevertheless reveal a
certificate from another owner's risky response. Local comparisons must use
these actual beliefs; the event order alone does not prove waiting uninformative.
Under the barrier order (stage B), waiting also reveals who has committed,
and the barrier order must keep that from changing source incentives.

A missed owned decision is charged. The contract cannot distinguish an owner who
chose not to send from one who was censored, so it charges both alike: it
plays along with censorship. Protected inclusion is exactly the assumption
that a timely sole packet is never censored, so a prescribed owner is charged
only after waiting past its guarantee. A miss differs from a source forfeit:
the forfeit stays hidden until the reveal (it compiles to a handle with no
opening), while a miss is public at the deadline. The auxiliary game is the
actual audited risk-menu game, retaining native pending state and attempted
choices. Its rational continuation must be supplied both after misses and at
late unrecorded owned opportunities, before the acceptance/miss lottery.

Open obligations this creates:

- **Charges on retained histories.** Retained deferral can miss and be charged,
  so the auxiliary payoff includes actual retained charges. Zero charge is
  required on final equilibrium-supported play. A comparison at a deferral
  information set must account for both its conditional miss probability and
  any information it can receive.
- **Rational continuation.** Public misses and native certificate observations
  create information absent from protected source execution. Simultaneous free
  agent completion can supply consistent rational play there, once the
  prescribed site set and its initialized support property are proved.
- **Late sends.** The policy stops fresh calls once protected inclusion can
  no longer land before the deadline. A fast actual inclusion may still
  accept a canonical call sent before expiry; the final record permits that
  call and the audit cannot charge it merely for missing the protection gate.
  Retain these attempts and admit rational continuation at that opportunity.
  A builder may condition inclusion on public packet content, so the lottery
  need not equal sending no packet and paying a public-miss charge. Packets
  forbidden by the final record remain auditable.
  For example, with deadline 2 and inclusion bound 1, an owner turn at clock
  0 is protected. After waiting, a turn at clock 1 is still timely but loses
  protection: `1 + 1 < 2` fails. An immediately included canonical decision
  can succeed without a charge. The contract also permits a builder to accept
  late FALSE while leaving late TRUE pending until expiry, so accepted and
  missed branches need separate continuation comparisons.
- **Source embedding and beliefs.** The current candidate prescribed site set
  includes benign earlier deferrals. A clean-prefix law stops at the first
  risk; arbitrary deferral timing is not closed through termination. This
  source-belief route needs the relative escaped mass to vanish at prescribed
  information, including where passage tends to zero. Global outcome error
  alone does not prove that statement. Canceling the focal owner's likelihood
  still leaves foreign waiting probabilities in the clean denominator.
  Restricting prescriptions to first-turn-compatible information would avoid
  those waiting factors in its witness, but also needs an upper payoff bound
  for a retained wait into free continuation. Rational completion alone gives
  no such bound. Probe C6's penalized public-miss source omits the native
  attempted-choice recall and certificate observations needed here.

### Monitoring and punishment

The design must admit a concrete watcher and contract implementation. A
watcher reports signed packets it actually observed or read from the ledger;
it has no access to the complete network input history. Its observation is
private and probabilistic. Reports use the pending-message mechanism, and
punishment is decided after gameplay and the monitoring and report-delivery
phases. The observation period, report cutoff, delivery bound `W`, and
settlement time must be specified together. Evidence acquired after a
gameplay deadline remains reportable before the cutoff. Reports accepted only
at final settlement cannot change gameplay that has already occurred.

[ChallengeWindow](../Interaction/ChallengeWindow.lean) makes this backend
boundary explicit. `EvidenceReportService` separates authentic partial
observations from reports carrying actual inclusion times. Its audit sample
uses only evidence included by settlement. `EvidenceReportService.sample_coverage`
proves that observation coverage times conditional timely-delivery coverage
lower-bounds actual collection; the delivery bound is conditional on the
whole observed record, so independence is unnecessary. This sample supplies
the authenticity and coverage premises of the terminal-audit theorem. A
concrete pending-message reporting implementation must establish these
premises; the owner service contract alone does not.

[ReactiveSignedEvidence](../Vegas/Pending/ReactiveSignedEvidence.lean)
proves concrete collection for malformed packets, withholding carrying evidence,
commitments carrying opening evidence, and uncertified openings. A named
packet is forbidden once its event completes. Complete play supplies that
final-record premise; actual emitted traffic persists under arbitrary later
policies. [SourceServiceSignedCollection](../Vegas/Game/SourceServiceSignedCollection.lean)
derives conditional expected collection after committing such a response at
an actual information site, including the remaining horizon budget. Its lower
bound is observation coverage times delivery coverage conditional on the
whole observed record. The backend hypotheses allow genuine observation and
report failure.

[SourceServiceSignedInformation](../Vegas/Game/SourceServiceSignedInformation.lean)
proves that the owner's actual recall and view determine the whole emitted
signed envelope. A breach witnessed at one hidden history therefore supplies
the same classification at every history of that information site. Uniformity
does not require an additional scheduler or observation hypothesis.

The monitored guessing fixture instantiates this boundary with its actual
private observation record and the final public ledger. `nativeCollectionLaw`
has a fixed conditional delivery rate, including genuine delivery failure;
`compiled_source_equilibrium` proves SE and the realized joint payoff law for
that physical settlement, with `2 ≤ rate * deposit`. Challenge time starts
after gameplay, and terminal payoff equality transfers incentives at every
legal information site. This is a checked fixture with a narrow packet audit,
not the general asynchronous theorem or a concrete pending-message reporter.

Retain one deposit per player as the starting enforcement design. The goal
is preservation of the source equilibrium with rational continuations after
every departure; continued compliance after a sunk penalty is not required.
The penalty scheme may change if the proof needs it, but complexity must earn
its place through a concrete missing incentive comparison.

Public decision misses and packet evidence are separate cases. A public miss
currently causes certain collection. Packet collection may remain uncertain
to the author because the watcher's sample is private. After an earlier
packet offense, a further offense is deterred only by its additional
conditional collection probability. Positive coverage for each packet does
not establish that increase: observation and delivery may be correlated.
No independence premise or uniform increase is assumed.

A common delivery coin can deliver all observed reports together, so a
second observed offense need not increase expected collection even when the
collection rate is below one. After a public decision miss, the current OR audit
collects with certainty at every continuation; its payoff is the base payoff
minus a constant deposit. A complete extension must either admit rational raw
continuation there or supply fresh reserves. Additive charges also need control
of changes to collection of earlier offenses; per-new-packet coverage alone
does not provide that control.

The proposed source miss extension has several distinct cases. A silent
binding miss fails the binding and announces its owner and source name. A
late binding attempt additionally leaves the attempted choice in private
recall. A late opening can fail while leaving probabilistically collected
signed evidence. Public miss successors alone do not yet represent attempted
private choices or later collected evidence. These are part of the open extension and incentive
obligations, not consequences of the local retained-menu proofs.

[PublicMiss](../Vegas/Source/PublicMiss.lean) supplies commitment and disclosure
miss successors. They store a failed typed binding or publication, retain the
ordinary source guard bookkeeping, and append an owner/decision-name
announcement visible to every player. A commitment miss differs from hidden
forfeiture; a disclosure miss differs from deliberate false disclosure even
though its typed result is identical. The full execution protocol, no-miss
embedding, SE extension, attempted-choice memory, and opening-evidence
lotteries are not yet supplied. The runtime audit reads strategic misses
from the public contract marker for every owned decision.

[EventApplication](../Vegas/Pending/EventApplication.lean) records strategic
expiry in the public `EventGraphRuntime.State.missedEvents` set. Initial play
has no markers. Accepted
player packets, including false disclosure, preserve the set; chance execution
also preserves it. A ready, activated, due strategic expiry inserts exactly
its event. Other expiry commands leave the set unchanged. This is contract
state, independent of a watcher's partial packet sample. Explicit false
responses use authenticated withholding without opening evidence. The calendar
restriction requires an actual decision by the last owner visit; the general
canonical and risk menus retain deferral. Marker preservation and accepted
packet completion are proved separately from the source miss game's still-open
execution and equilibrium embedding.

The candidate one-escrow menu is implemented in
[ReactiveRiskMenu](../Vegas/Pending/ReactiveRiskMenu.lean). An owner's public
miss or its own recalled unprotected attempt opens every bounded raw response
for that owner. It also opens at a ready owned decision with no recorded own call
once protected inclusion no longer fits, including when the deadline is due
but expiry has not been commanded. Any own response there records the risky
opportunity, even silence or a foreign-event packet. The scan tests each
before-view against the preceding own recall prefix. It reads no hidden
network state or watcher verdict. Already-recorded protected packets and
explicit protected resolution withholding do not trigger it.

Persistent public/recall risk is separate from the current opportunity, which
can change under scheduler commands. [SourceServiceRiskSlots](../Vegas/Game/SourceServiceRiskSlots.lean)
proves owner-local slot and freshness invariants for persistently clear
owners, allowing foreign raw actions. Prescribed transmissions never add
submission risk, for any turn timing, scheduler or chance steps. Silent
deferral can reach a late owned decision and add opportunity risk; that broader
no-risk conclusion is not claimed for approximants.
[SourceServiceFirstTurnOpportunity](../Vegas/Game/SourceServiceFirstTurnOpportunity.lean)
proves that the owner's actual first ready turn has a protected inclusion
window, using answered activations and the reaction budget.
[SourceServiceFirstTurnCalls](../Vegas/Game/SourceServiceFirstTurnCalls.lean)
then supplies and records every actual protected canonical decision. The
binding specialization also identifies its prepared handle, including when
the source binding has no private opening material.
[SourceServiceFirstTurnRisk](../Vegas/Game/SourceServiceFirstTurnRisk.lean)
proves that exact first-turn play never recalls an unprotected owned
opportunity and records every earlier own turn. These are owner-local
results under `AsyncContract` and `AsyncTimely`, with arbitrary foreign raw
policies and an explicit bound on rounds.
[SourceServiceProtectedBinding](../Vegas/Game/SourceServiceProtectedBinding.lean)
isolates the event-level part: a protected fresh commitment with a sole own
identifier cannot become a public binding miss under arbitrary foreign raw
play. Its accepting receipt fixes the public handle throughout every legal
continuation (`bindingReceipts_history`), even for an unusable private binding.
This needs protected inclusion and the actual call/sole-identifier premises;
it needs no watcher hypothesis.
[SourceServiceFirstTurnNoMiss](../Vegas/Game/SourceServiceFirstTurnNoMiss.lean)
discharges the operational coverage obligation for exact first-turn play:
every owned event's public marker, and the owner's entire
`missedDecisionBy` detector, stay clear at every supported round and pending
activation within the horizon. A new strategic miss would require due expiry;
the opportunity contract supplies an earlier answered owner turn, which has
already recorded the protected call. Silent approximant deferrals remain
outside this no-miss conclusion.
[SourceServiceFirstTurnSafe](../Vegas/Game/SourceServiceFirstTurnSafe.lean)
combines these results with submission recall and the current opportunity:
the owner's entire `serviceRisk` flag is false at every supported control.
These results apply to the sequentialized graph and prescribed owner play
from initialization. They do not assert completion at every prefix, usable
private openings, or safety after that owner's own raw deviations.

[SourceServiceRiskPolicy](../Vegas/Game/SourceServiceRiskPolicy.lean)
supplies a distinct local fact: at any legal risk-menu history where this
owner's full flag is clear, its prescribed responses are admitted for every
turn timing. Foreign owners may already have used their raw branches. The
proof derives bounded record and canonical-slot resources from that history;
it does not prescribe source responses at a risky site or prove rationality.

[SourceServiceResponseCompletion](../Vegas/Game/SourceServiceResponseCompletion.lean)
derives the post-response support and horizon budget from an actual active
control and a response in the current players' policy support. The existing
generic stopping bridge then yields a completion boundary and a continuation
error equal to the remaining events' deferral-weight sum. This covers actual
prescribed responses; an excluded one-shot response requires its own support
witness under the changed profile or a fully mixed menu assessment.

[SourceServiceOwnerSettled](../Vegas/Game/SourceServiceOwnerSettled.lean)
proves that every actual authored packet is permitted by the actual settled
record, for any turn timing and arbitrary foreign raw policies. A protected
sole packet either remains unsettled or completes its event by acceptance;
its checked content persists under later commands.
[SourceServiceFirstTurnAudit](../Vegas/Game/SourceServiceFirstTurnAudit.lean)
combines this packet soundness with first-turn absence of public misses to
derive zero owner charge at every supported control. Evidence sampling must
be authentic; no positive observation or report-delivery bound is needed.
When all owners follow the policy, the entire realized payoff-vector law is
exactly the base payoff. This supplies prescribed-play soundness, while clean
continuation comparators under the local deviation beliefs and the strategic
source embedding remain open.

[AsyncServiceFirstTurnLaw](../Vegas/Game/AsyncServiceFirstTurnLaw.lean)
combines initialized source-outcome preservation with that same actual audit
draw. The joint law retains the typed terminal source state and the whole
payoff vector; its parameter/public-outcome projection retains their original
correlations. Disclosure normalization supplies this execution law for every
source profile. Behavioral strategy embedding and sequential rationality are
separate requirements.

[AsyncServiceFirstTurnProfile](../Vegas/Game/AsyncServiceFirstTurnProfile.lean)
represents exact first-turn play as a behavioral profile of the actual finite
risk-menu game, for source profiles admitted by the value commitment interface.
Its initialized control laws retain the application, network, receipts and
private recall. The same joint source-outcome/settlement law holds there.
Admission is required only along physically supported legal histories;
the total policy's fallback at other inputs carries no rationality claim.

The prescribed limit at an earlier-deferral site must come from the timing
approximants. Pure first-turn policy itself is silent after its selected turn
has passed. At a protected owned site reached after an earlier silent turn,
geometric timing can instead have a limiting decision probability of one.
The same selected-decision distinction applies to resolutions: false is an
actual withholding packet, while silence is deferral.

[SourceServiceDecisionTimingPosterior](../Vegas/Game/SourceServiceDecisionTimingPosterior.lean)
derives the actual timing posterior after one silent response at a legal,
protected first owned turn. Silence rules out timing index zero because every
selected decision sends a packet, including a failed binding value or false
disclosure. With geometric timing, the next counted turn decides with
probability `1 - weight`, or surely at the final index. The response error is
bounded by the actual posterior waiting probability. The lemma supplies the
next view explicitly; it does not assume the scheduler provides or protects
that later turn. Source-relative beliefs remain a separate obligation.
The initialized first-turn execution law does not settle these off-path laws.

[SourceServiceDecisionRecallPosterior](../Vegas/Game/SourceServiceDecisionRecallPosterior.lean)
extends the timing calculation to every earlier silent turn at the same
owned event in an actual clean legal prefix. Unrecordedness rules out earlier
transmissions, and recalled opportunity protection supplies the likelihoods.
The posterior is exactly the timing law restricted to indices at least the
actual turn count. Geometric response error is at most the deferral weight,
uniformly over varying admitted source profiles. The current response keeps
its deadline gate; the proof supplies no later protected turn or source
belief projection. For that projection, the comparison between clean and
escaped histories must retain full own recall and cancel its common response
likelihoods, including earlier deferrals. An unconditional bound on escaped
traffic cannot by itself control a rare information-set posterior.

[SourceServiceResolutionLikelihood](../Vegas/Game/SourceServiceResolutionLikelihood.lean)
derives zero silence mass for the selected source law at a protected,
unrecorded resolution. Both source booleans emit an actual decision. A closed
inclusion gate defers the selected decision; the generic owned-opportunity
scan opens the risk menu at that input. This removes the need to balance
source false trembles against timing deferrals merely to distinguish their
packets. The generalized timing posterior supplies a response limit; the joint
source beliefs and their incentive comparison remain unproved.

[SourceServiceResolutionRecallWindows](../Vegas/Game/SourceServiceResolutionRecallWindows.lean)
derives protection at every earlier recalled turn from actual protection at
the current same-event turn. The original activation persists until
completion, and the clock is monotone under arbitrary raw play. No source
policy, clean-history or scheduler-contract premise is needed for this window
fact; it does not identify the earlier source choices.

[SourceServiceTimingRates](../Vegas/Game/SourceServiceTimingRates.lean)
constructs compatible numerical rates for any finite family of vanishing
source errors. A strictly increasing source subsequence makes each error
negligible relative to every resolution reach mass up to the horizon; binding
deferral independently vanishes faster than a positive source passage scale.
This preserves existing source limits. Supplying the operational errors and
proving joint belief transport remain separate obligations.

Downstream beliefs must distinguish an accepted false decision from a
public miss. The authenticated `.withhold event` call carries no opening
evidence; a strategic expiry adds its event to
`EventGraphRuntime.State.missedEvents`. Both may have the same failed typed
publication, but their public contract records differ. Partial watcher
sampling cannot recover that distinction from a false output alone.

The miss extension must carry that record through its execution protocol,
attempted-choice memory, source beliefs and incentive comparisons. The runtime
marker and source miss successors supply operational foundations; they do not
prove the original source equilibrium embedding. Unconditional continuation
error still does not bound conditional belief error at a rare information set.

[SourceServiceAsyncFactorization](../Vegas/Game/SourceServiceAsyncFactorization.lean)
preserves source-view traffic factorization through an actual silent round
while a binding is the only ready event. The arbitrary public scheduler may
activate any player, include any pending packet, wait, advance the clock,
expire an event, or request a sample. The proof retains actual network state,
receipts, scheduler recall and focal private recall; it needs no independent
grant-probability assumption. Stopped completion and beliefs at all native
information sites still need their corresponding laws.

[SourceServiceBindingDecisionFactorization](../Vegas/Game/SourceServiceBindingDecisionFactorization.lean)
proves the binding decision kernel for the actual canonical commitment
response at a fresh counted slot. It retains both original and effective
source memories, and derives a joint traffic kernel conditional only on the
focal source successor view. No scheduler command or independent traffic
assumption enters this response step. Acceptance, source/runtime alignment,
completion and the full source-information belief projection remain separate.

[SourceServiceResolutionDecisionFactorization](../Vegas/Game/SourceServiceResolutionDecisionFactorization.lean)
supplies the corresponding response kernel for effective false and true
disclosure choices. Store alignment, binding provenance and actual input
recall determine their authenticated withholding or opening packets. The
joint source-successor and full traffic law factors through the focal source
successor view. This is a response law; it assumes no scheduler opportunity
or source equilibrium and asserts no packet acceptance or stopped completion.

[SourceServiceResolutionIntentionFactorization](../Vegas/Game/SourceServiceResolutionIntentionFactorization.lean)
retains both the original disclosure intention and its effective transmitted
choice in that response law. A failed TRUE intention advances the original
source history with TRUE while its actual packet and effective history use
FALSE. The joint traffic channel depends on the effective successor view;
it does not identify the original intention from the packet or assume a
normalized-source equilibrium.

[SourceServiceResolutionInclusionFactorization](../Vegas/Game/SourceServiceResolutionInclusionFactorization.lean)
identifies actual fresh canonical inclusion, its accepting receipt and the
source disclosure result for either Boolean choice. Initialized raw trace
invariants supply the serial, evidence provenance and empty intention cache.
It is a local accepted-inclusion law; stopped traffic and source alignment
are proved separately below.

[SourceServiceResolutionPhaseTraffic](../Vegas/Game/SourceServiceResolutionPhaseTraffic.lean)
proves equal full traffic laws through an actual silent resolution round from
initialized raw traces and the owner's actual conforming recalled calls. This
covers earlier deferrals, arbitrary public commands, clock advancement and
expiry. Actual conformance persists through supported silent rounds. Once a
decision is recorded, the decided policy's whole round is the silent round,
and an existing carried source/traffic factorization survives it. The carried
source need not agree with the runtime after expiry; protected completion and
the stopped source law remain separate obligations.

[SourceServiceStoppedResolutionTraffic](../Vegas/Game/SourceServiceStoppedResolutionTraffic.lean)
iterates the conforming silent-round law through the actual `runUntilHorizon`
evaluator, stopped at current-event completion. Actual initialized traces
derive the remaining budgets, public completion test, recalled conformance
and readiness before completion. The carried source/traffic channel is
preserved even after earlier deferrals. The horizon may exhaust unfinished;
this traffic law does not itself establish protected completion or agreement
between the carried source successor and the final runtime configuration.

[SourceServiceStoppedBindingTraffic](../Vegas/Game/SourceServiceStoppedBindingTraffic.lean)
proves the corresponding stopped binding law and its composition with the
recorded turn policy. Equal complete traffic determines both the public stop
test and the remaining horizon. The binding law needs no packet-conformance
or calendar hypothesis. It preserves a carried source-conditioned channel;
identifying that carrier with the actual source successor is still necessary.

[SourceServiceRecordedResolutionTraffic](../Vegas/Game/SourceServiceRecordedResolutionTraffic.lean)
connects that stopped law to the actual turn-counted policy for any timing.
Once the owned resolution is recorded, its whole execution law through
stopping equals silent continuation. The equality retains earlier deferrals,
actual own recall and every scheduler observation. It does not identify the
source successor or prove a belief comparison.

[SourceServiceRecordedDecisionCompletion](../Vegas/Game/SourceServiceRecordedDecisionCompletion.lean)
proves completion for any actually recorded owned decision under the
asynchronous contract. Every supported stopped endpoint retains the original
recalled call, accepts that exact packet identifier, completes the event and
has no public miss marker. Only the owner's policy is prescribed; foreign
policies and the owner's timing are arbitrary. The source-alignment laws below
identify the endpoint's actual typed successor.

[SourceServiceRecordedSourceChoice](../Vegas/Game/SourceServiceRecordedSourceChoice.lean)
derives the original recalled resolution response's supported source Boolean
from the actual initialized policy execution. Typed source observations remain
fixed while the event is ready, so earlier deferrals need no original-execution
oracle or assumed source-draw support. This is a support result, rather than
an identification of the marginal probability of a source draw.

[SourceServiceRecordedBindingCompletion](../Vegas/Game/SourceServiceRecordedBindingCompletion.lean)
and [SourceServiceRecordedResolutionAlignment](../Vegas/Game/SourceServiceRecordedResolutionAlignment.lean)
connect those actual draws to their original accepting packets and every
supported stopped endpoint. They derive the exact compiled successor
configuration, full typed source-store agreement and decoded source history.
Binding candidate meanings persist from their original fresh submission;
resolution provenance and current source alignment determine FALSE withholding
or effective TRUE opening. The owner may have deferred earlier, and foreign
policies remain arbitrary. These alignment kernels do not establish source
draw probabilities or native source-relative beliefs.

[SourceServiceProtectedDecisionLaw](../Vegas/Game/SourceServiceProtectedDecisionLaw.lean)
identifies the actual response law at a clear protected unrecorded turn as
geometric waiting mixed with the typed compiler choice kernel. The timing
hazard is derived from the owner's full actual recall, including earlier
protected deferrals. This response marginal does not supply the joint
source-prefix law or the conditional source assessment at a native site.

[SourceServiceBindingResponseFactorization](../Vegas/Game/SourceServiceBindingResponseFactorization.lean)
reads the chosen typed value from the actual submitted candidate and couples
it with that same response's complete traffic. Waiting retains the original
and effective source states; transmission advances both carried states with
the chosen commitment. The prior source-pair channel is the induction
hypothesis. The actual compiler kernel, counted-slot freshness and geometric
response law follow from aligned configurations and clear protected traces.
The native configuration advances later, at acceptance.

[SourceServiceBindingResponseCompletion](../Vegas/Game/SourceServiceBindingResponseCompletion.lean)
joins this transmitting draw to its actual protected completion. The newly
submitted packet fixes the exact typed successor, source store, decoded
history and accepting receipt at every supported stopped endpoint. Its joint
law keeps the waiting branch with weight `w` and the transmitting branch with
weight `1 - w`, including the same response's full stopped traffic. Packet
completion allows arbitrary foreign policies; traffic factorization uses
prescribed foreign continuations. It does not identify a native posterior.

[SourceServiceBindingPrefixCompletion](../Vegas/Game/SourceServiceBindingPrefixCompletion.lean)
derives the whole-program source residual from the actual legal ready history.
Its current `sourceServicePrefix?` readout has the residual commitment kernel
as its whole behavioral source step. Every supported protected transmitting
completion decodes to that same drawn successor through the residual's real
transport map. Only the owner follows the prescribed policy. This identifies
the compiler profile's source prefix; for a normalized profile it does not
restore erased original disclosure intentions or supply a source prior.
Its probability theorem keeps the same actual response and stopping draws
joint with full traffic. The normalized transmitting prefix marginal equals
that whole behavioral source step. Waiting uses the actual next-prefix
decoder; [SourceServiceUnfinishedPrefix](../Vegas/Game/SourceServiceUnfinishedPrefix.lean)
proves its result is `none` because the ready event's typed output is still
unwritten.
The residual also carries a partial recovery of each owner's source view,
proved directly for its actual transport map. Recovery uses the source
constructors rather than a default private value.
[SourceServiceDecoderSlice](../Vegas/Game/SourceServiceDecoderSlice.lean)
fixes one typed tail, behavioral profile, compiler embedding, reference-order
certificate, decoder lift and partial view recovery from the source syntax
and rank. The actual compiled policy is aligned at that rank, and whole-profile
effective disclosures imply tail effectiveness through the same syntax
recursion. Its decoder splitting holds for
every store, history and additional count, and its behavioral step commutes
with that same lift. These witnesses are therefore shared across a prior;
they are not selected from each hidden execution independently. An actual
source-prefix likelihood is still needed before Bayes transport.

[SourceServiceResolutionResponseLaw](../Vegas/Game/SourceServiceResolutionResponseLaw.lean)
derives the corresponding physical FALSE/TRUE packet marginal for effective
profiles. [SourceServiceResolutionMemoryLaw](../Vegas/Game/SourceServiceResolutionMemoryLaw.lean)
uses the source policy's actual disclosure normalizer to retain original
intention memory jointly with the native response. Waiting preserves that
memory; transmission carries the original intended successor through the
normalizer's conditional memory law. Its native marginal is the actual
protected geometric policy after earlier deferrals. The joint native
information-site law and source-relative assessment still need transport.

[SourceServiceResolutionMemoryFactorization](../Vegas/Game/SourceServiceResolutionMemoryFactorization.lean)
joins that actual response to its full traffic channel. The source normalizer's
memory lottery restores the current owner's original history; other histories
remain as carried by the prior configuration. Waiting preserves this pair,
and transmission advances its intended and effective successors. The same
joint law has the actual protected native policy's traffic marginal. The prior
channel is supplied only for the effective source configuration. This local
memory lift does not assemble all owners' original histories or identify the
source assessment at a native information site.

[SourceServiceResolutionMemoryCompletion](../Vegas/Game/SourceServiceResolutionMemoryCompletion.lean)
extends this same joint law through actual stopped execution. Waiting stays
at its post-response native boundary; transmitting branches retain the
effective successor, the current owner's restored intended successor and
full stopped traffic. The native execution marginal is the actual response
followed by the same own-record-dependent stopping kernel. Supported
transmitting endpoints agree with both successors' typed states and decode
the effective history. This proves neither a whole original-source history
law nor a native source-assessment equation.

[DisclosureProfilePrefix](../Vegas/Game/DisclosureProfilePrefix.lean)
supplies a common original-source carrier at every finite normalized source
prefix. It composes the actual owner memory lotteries, retaining histories
restored earlier, and recovers the complete original protocol-state law.
The joint version preserves correlated initial parameters. The proof
telescopes one-owner prefix realization against arbitrary opponents and
assumes no independence of the restored memories. Applying it to native
information still requires the effective-source conditional-prefix bridge.

[DisclosureProfileRetraction](../Vegas/Game/DisclosureProfileRetraction.lean)
proves that every supported restored original state compresses back to that
same effective source prefix. The full compression acts on each player's view
through its existing own-recall compression. Consequently, a channel reading
the effective source view can accompany the restored original source law with
its weight read from the compressed original view. The support identity comes
from the actual intermediate prefix laws; it is not an assumed information
fiber equation. Identifying that channel with native traffic remains separate.

[DisclosureProfileJointChannel](../Vegas/Game/DisclosureProfileJointChannel.lean)
keeps correlated initial parameters in this same joint original-state and
channel law. The common restoration lottery and the channel draw are retained
together. The noise kernel reads only the focal effective source view; it
does not supply a native-input likelihood or a source posterior.

[SourceServiceFirstActivation](../Vegas/Game/SourceServiceFirstActivation.lean)
derives the first ready owner input from an actual untouched completion
boundary and exact owner first-turn policy. Other policies may be arbitrary.
The stop is reached within the asynchronous contract's horizon, retains the
boundary configuration, and has protected inclusion. The actual own recall
recovers the passive before-response input; integrating the response lottery
preserves that same input sample. Equal complete owner traffic gives equal
activation-input laws.

[SourceServiceFirstActivationFactorization](../Vegas/Game/SourceServiceFirstActivationFactorization.lean)
factors the whole preceding public-scheduler wait at any owned binding or
resolution to that actual first owner input. It replaces pre-hit rounds with
the actual silent kernel
inside the stopped-input continuation; the stopping response lottery
integrates out. A legitimate prior source-view/full-traffic factorization
therefore retains its complete source carrier and yields an input channel.
Complete play gives total mass on real inputs at every supported source view.
The prior source marginal is preserved; the initialized rank law below derives
it separately. Post-response
full traffic is not identified with pre-response input noise.

[SourceServiceFirstTurnCompletes](../Vegas/Game/SourceServiceFirstTurnCompletes.lean)
proves the actual next-prefix decoder law of the local first-turn completion
phase equals the whole source behavioral step. The residual head-action
kernel reads that prefix before applying a continuation; samples, bindings
and explicit withholding are included. Its profile is the compiler's profile,
with effective disclosures.

[SourceServiceFirstTurnPrefix](../Vegas/Game/SourceServiceFirstTurnPrefix.lean)
derives this local law for the actual global first-turn policy. Its pure
timing posterior stays at the first index on every recall.
[SourceServiceFirstTurnRanks](../Vegas/Game/SourceServiceFirstTurnRanks.lean)
then composes actual event-rank stops from the same initialized execution.
At every rank, the whole effective prefix decoder has the source behavioral
iteration law, jointly with any reading of the same initial source draw.
Supported endpoints retain the actual completion boundary and horizon
budget. The composition uses the ordered stopping identity in
[ReactiveStopping](../Interaction/ReactiveStopping.lean); neither a stopping
oracle nor a source marginal is supplied.

[SourceServiceFirstTurnInformation](../Vegas/Game/SourceServiceFirstTurnInformation.lean)
proves that equal current physical observations at two actual first-turn
completion-rank endpoints give equal whole effective source views. The
initial draws may differ. Actual support supplies successful decoding and
completed-prefix checkpoints; current observation already contains the
focal graph observation and own completed-action history, so a separate
native recall equality is unnecessary. This is effective-view refinement,
without recovering original erased intentions or supplying a posterior law.

[SourceServiceOriginalPrefix](../Vegas/Game/SourceServiceOriginalPrefix.lean)
binds all owners' actual memory kernels to that same normalized native rank
decoder. One common restoration draw has the complete original source-prefix
law, jointly with correlated initial parameters. Normalized effectiveness is
derived internally. This is an auxiliary source carrier: physical own recall
need not retain a failed TRUE intention, and native information posteriors
still need the joint actual likelihood law.

[SourceServiceOriginalPrefixRetraction](../Vegas/Game/SourceServiceOriginalPrefixRetraction.lean)
derives effective source support from that actual rank law. Every supported
common original carrier compresses to the same native Option decoder.
Compressing its joint law with full stopped traffic, or with physical own
recall and observation, leaves the corresponding actual native joint law
unchanged. This retraction assumes no traffic noise or posterior equation.

[SourceServiceFirstBindingTraffic](../Vegas/Game/SourceServiceFirstBindingTraffic.lean)
proves the actual first-turn binding phase's whole next-prefix and full stopped
traffic law using the same source draw. Its fixed-draw traffic coupling
retains both original and effective typed successors and an unchanged parameter
from a prior source-view/traffic factorization, including a foreign focal player
for whom
different hidden binding draws have the same view. The actual first-owner
input, fresh protected packet and completed checkpoint decoder are derived
from initialized support. No separate source-draw or endpoint-agreement
premise substitutes for that joint law. Whole-prefix traffic induction and
native assessment transport remain open.

[SourceServiceFirstTurnBindingFactorization](../Vegas/Game/SourceServiceFirstTurnBindingFactorization.lean)
lifts the actual commitment phase through one fixed compiler-aligned slice.
Its compiler choice, protected first-turn mixture and whole next-prefix
decoder follow from actual policy alignment and checkpoints. It then reuses
the fixed-draw traffic factor, retaining the same parameter and full traffic
through the whole source behavioral step. Only the prior source-view/traffic
factor is a probability induction hypothesis.

[SourceServiceFirstResolutionTraffic](../Vegas/Game/SourceServiceFirstResolutionTraffic.lean)
joins the actual global first-turn resolution draw, whole source successor
and same full stopped traffic. The boundary derives its aligned reveal site
and source kernel; effective disclosures prove supported TRUE draws can
really open, and the actual accepted endpoint supplies its checkpoint decoder.
The global policy's whole stopped execution law equals the event-local phase
by `sourceServiceTurnPolicy_firstTurn_phase`, preserving full traffic and
private recall before any projection. The complete phase includes the
untouched wait to the first owner input, which must retain actual trace and
conforming-call resources; the recorded silent suffix alone does not
establish this preceding channel.

[SourceServiceFirstResolutionCoupling](../Vegas/Game/SourceServiceFirstResolutionCoupling.lean)
proves that entire actual first-response/stopped traffic coupling. Before the
first owner input, configuration stutter follows from actual initialized
support and absence of that input. At activation, the protected canonical
response, recorded call, new packet conformance and post-response trace are
derived. Existing recorded silence then carries the same traffic to event
completion. Its factorization retains an original intention, its effective
decision and an unchanged parameter through the same typed successor pair
and stopped traffic; the
only probability premise is the preceding pair-view/traffic induction
hypothesis. Actual compiler code and typed store agreement connect the pair
to the event. This is a latent original/effective pair law. The whole-view
consumer below identifies the actual global effective choice; common original
memory and whole-prefix composition remain separate.

[SourceServiceFirstTurnResolutionFactorization](../Vegas/Game/SourceServiceFirstTurnResolutionFactorization.lean)
joins that coupling to the actual global source choice in one fixed aligned
slice. Tail effectiveness derives supported normalization and realizability;
canonical policy alignment and protected completion derive the whole successor
decoder. The existing coupled factor retains the same parameter and full
traffic through the whole effective source step. Compiler code and node
agreement are required only on actual prior support; off-support source states
do not supply proof resources. Whole-prefix composition remains separate.

[SourceServiceFirstActivationResources](../Vegas/Game/SourceServiceFirstActivationResources.lean)
derives first-input turn zero, actual trace, protected inclusion, unused
canonical slot and prior-call conformance for either owned decision kind.
Binding traffic consumes these shared resources.
[SourceServiceResolutionPhaseTraffic](../Vegas/Game/SourceServiceResolutionPhaseTraffic.lean)
proves silent coupling per actual scheduler command and then integrates the
scheduler lottery in its round theorem. Its traces remain tied to the actual
scheduler when splitting off an owner activation; substituting a constant
scheduler would not establish those trace premises. The first-resolution
coupling consumes these resources in its actual pre-first-owner induction.

The shared [decoder slice](../Vegas/Game/SourceServiceDecoderSlice.lean)
also derives the actual forward source-view map alongside partial recovery.
Both follow the same source syntax: the state lift's observation equals the
view lift applied to the tail observation. A whole-view prior noise kernel
can therefore be restricted to the fixed typed tail by composition, and a
typed successor channel can be lifted back using recovery. Actual aligned
[source residuals](../Vegas/Game/SourceServiceReachedDecoding.lean) carry the
same forward view map through initialization and every real graph step.

[SourceServiceFirstTurnSharedCheckpoint](../Vegas/Game/SourceServiceFirstTurnSharedCheckpoint.lean)
derives typed checkpoints in this one aligned slice at every actual initialized
first-turn rank endpoint. Rank support supplies the completion boundary and
horizon bound. The whole decoder's actual totality and universal slice
transport imply a successful tail-state read. Its typed source state and
action history come from the real completed store and history, yielding
checkpoint agreement and the whole-prefix decoder identity. No endpoint,
source marginal, traffic noise or posterior equation is assumed.

The whole-prefix likelihood induction should carry the effective complete
source state with actual traffic first. At each rank, choose the shared
decoder slice before integrating the histories, apply the actual sample,
binding or resolution phase law, and lift its typed-tail view channel to the
whole source view.
[SourceServiceFirstTurnRankFactorization](../Vegas/Game/SourceServiceFirstTurnRankFactorization.lean)
proves this actual initialized pure-first-turn composition at every rank.
Ordered stopping composes the real executions at the same horizon; shared
typed checkpoints supply the three constructor cases. The resulting joint
law equals the true whole source behavioral iteration with the same initial
parameter and full stopped traffic. Its channel reads only the whole effective
source view; no phase, source-marginal, endpoint or likelihood law is supplied.
[SourceServiceInitialTraffic](../Vegas/Game/SourceServiceInitialTraffic.lean)
starts that induction from the actual setup law, retaining any parameter from
the same initial draw beside the whole source entry and full traffic. The
owned initial candidate catalogue is determined by the focal source view.
[SourceServiceOriginalRankTraffic](../Vegas/Game/SourceServiceOriginalRankTraffic.lean)
restores all owners' original histories once at the requested rank through
the common memory lottery, retaining the same initial parameter and full
traffic. Its channel reads the compressed original focal view. Supported
actual decoders remove the fallback branch; no marginal or channel equation
is supplied.
[SourceServiceOriginalFirstInput](../Vegas/Game/SourceServiceOriginalFirstInput.lean)
carries that joint law to the actual first binding or resolution owner input,
before the response draw. The channel has total mass on real inputs at every
supported original source prefix. These are pure-first-turn laws; conditional
assessment beliefs and nonpure timing remain separate.
[SourceServiceOriginalFirstInputPosterior](../Vegas/Game/SourceServiceOriginalFirstInputPosterior.lean)
derives actual supported-input recovery from the shared typed checkpoint,
unchanged configuration at the first activation, and common-memory retraction.
The conditional whole original source-prefix/initial-parameter law equals the
true source posterior on the compressed observation. This does not recover
uncompressed original intentions or identify the stopped readout with native
assessment history beliefs. Nonpure timing still needs actual miss decompositions
and conditional passage/escape bounds.
[PassageBayes](../GameTheoryExtensions/Analysis/Protocol/PassageBayes.lean) derives
the actual terminal-history ancestor law at any information antichain. Each
ancestor has its true reach weight; conditioning on passage gives the standard
Bayes belief even at variable depths. A stochastic readout commutes with that
conditioning, so the same memory lottery can be sampled from the actual earlier
history.
[ReactivePassageBayes](../Interaction/ReactivePassageBayes.lean) projects this law
to native state beliefs, retaining the earlier observed control instead of
the final control. Its positive-mass and Bayes-consistency hypotheses are the
ordinary assessment conditions.
[SourceServiceFirstInputPassage](../Vegas/Game/SourceServiceFirstInputPassage.lean)
reads the chronological first event input from actual own recall and identifies
it exactly with passage through a first-event information site. The input
persists through later responses, and its terminal passage probability equals
the site's actual information mass even at variable depths.
[AsyncServiceFirstInputPassage](../Vegas/Game/AsyncServiceFirstInputPassage.lean)
identifies the normalized first-turn profile's complete input law with actual
initialization, rank stopping and first-activation stopping. This is the input
marginal. The terminal and native posterior laws below supply joint restoration
through the actual ancestor belief; perturbed timing remains separate.
[SourceServiceInitialReadout](../Vegas/Game/SourceServiceInitialReadout.lean)
recovers the same initial source state from persistent graph inputs, before
completion and under arbitrary native policies and scheduler commands.
Injectivity rules out a second compatible initialization; terminal source
readout retains this same environment. An ancestor parameter can be read from
it without resampling or adding a player observation.
[SourceServiceFirstInputSourceLaw](../Vegas/Game/SourceServiceFirstInputSourceLaw.lean)
joins that decoded initial draw, the real stopped prefix and actual input through
one common all-owner restoration lottery.
[SourceServiceFirstInputReadoutPosterior](../Vegas/Game/SourceServiceFirstInputReadoutPosterior.lean)
conditions this physical stopped readout to obtain the true original source
prefix/parameter posterior on the recovered compressed view.
[SourceServicePastPrefix](../Vegas/Game/SourceServicePastPrefix.lean) reconstructs
the earlier prefix from persistent fields and completions below its rank. It
agrees with the prefix decoder at the rank seed and survives arbitrary legal
native continuations. Extending the source posterior to perturbed waiting
remains a separate obligation.
[SourceServiceFirstInputAncestor](../Vegas/Game/SourceServiceFirstInputAncestor.lean)
derives the before-event prefix directly from an actual owned information
history's ready input and sequential graph order. Every native descendant
retains that same ancestor readout, at any decision depth and under arbitrary
raw responses. No separate clean-prefix premise is needed.
[SourceServiceFirstInputTerminalLaw](../Vegas/Game/SourceServiceFirstInputTerminalLaw.lean)
identifies the represented normalized first-turn terminal law jointly with
the earlier prefix restoration, same initial parameter and chronological first
input. Its restoration kernel is preserved along actual native descendants.
This supplies the full terminal joint law for ancestor conditioning.
[SourceServiceFirstInputNativePosterior](../Vegas/Game/SourceServiceFirstInputNativePosterior.lean)
proves that the actual Bayes-consistent native ancestor belief, followed by its
common original-memory draw, equals the true original source-prefix and
same-initial-parameter posterior on the recovered compressed view. One recovery
function serves every positive-mass first owned site and every such assessment.
Native decision recall supplies the information antichain; actual passage gives
input support. No stopping-likelihood, clean-history or common-depth premise is
supplied.
[AsyncServiceFirstTurnBeliefResources](../Vegas/Game/AsyncServiceFirstTurnBeliefResources.lean)
derives actual initialized physical support and clear owner risk for each
history in the first-turn Bayes belief. Both results concern pure first-turn
play. Perturbed waiting beliefs and sequential rationality remain open.
[SourceServiceWaitRiskConfounding](../Vegas/Game/SourceServiceWaitRiskConfounding.lean)
checks that protected and unprotected timely binding responses can emit the
same typed-success packet, receive acceptance at the same clock, and give a
foreign owner the same full input. Only the sender's private risk recall
differs. A separate geometric two-branch calculation gives conditional risk
one half at every positive waiting weight below one. This is a local runtime
pair and a finite path law; certification as an initialized asynchronous
service and identification with native Bayes likelihoods remain separate.
[SourceServiceLateTurnCompletion](../Vegas/Game/SourceServiceLateTurnCompletion.lean)
uses real recorded recall to transfer the timely call's chosen-step/public-miss
dichotomy to the actual turn-counted continuation. Its law stops at the current
event's completion, preserving the owner's later-event policy. It does not
supply acceptance probabilities or a waiting comparison.
[LateResolutionService](../Vegas/Examples/LateResolutionService.lean)
certifies a concrete public scheduler over all raw histories. An authentic
opening on the first opportunity is included; on a later timely opportunity,
only FALSE withholding is included before expiry. The inclusion bound for the
late packet ends at the deadline, so the contract permits this censorship.
[LateResolutionContinuation](../Vegas/Examples/LateResolutionContinuation.lean)
reaches an initialized legal second turn and computes its actual terminal
typed payoff and collected audit. TRUE opening and silence both yield `−D`;
accepted FALSE withholding yields `0`, for every authentic partial audit.
The current policy is silent at that input for every timing lottery because
its protected inclusion gate is closed. A proposed prescription of TRUE at
every merely timely resolution would fail there too. Rational free completion
is necessary; source SE and the native information-site comparison remain
separate. This does not disprove equilibrium preservation.

[SourceServiceSampleCompletion](../Vegas/Game/SourceServiceSampleCompletion.lean)
derives actual silence, whole stopped-run equality with silent play, and the
exact sampled value/configuration law from a real completion boundary and
complete play. It applies to any turn timing.
[ReactiveSamplePhase](../Vegas/Pending/ReactiveSamplePhase.lean) couples
full focal traffic through a real silent round at the sole-ready sample,
including rejected inclusions and all public scheduler commands.
[SourceServiceStoppedSampleTraffic](../Vegas/Game/SourceServiceStoppedSampleTraffic.lean)
extends this coupling through the whole stopped sample run, retaining the
public sampled value with the same full traffic. It derives the stop and
remaining horizon from that traffic, without a supplied sample-time law.

[SourceServiceStoppedSampleFactorization](../Vegas/Game/SourceServiceStoppedSampleFactorization.lean)
composes the actual stopped sample marginal with the prior source-view/full
traffic factorization. It disintegrates the real public-value and traffic law
using its own conditional kernel. Both carried source configurations advance
by the same actual sampled value, retaining an unchanged parameter, and the
complete stopped traffic factors
through the effective successor view. The boundary and complete play derive
the sample marginal; no sample-time or completed-endpoint premise is supplied.
Whole-prefix induction and native information-site assembly remain separate.

[SourceServiceFirstTurnSampleFactorization](../Vegas/Game/SourceServiceFirstTurnSampleFactorization.lean)
lifts this actual law through a fixed compiler-aligned sample slice. The
prior whole-source-view factor restricts to its typed tail by the forward
view map. Actual completion and the checkpoint derive the whole next-prefix
decoder; recovery lifts the successor traffic channel back to the whole
source view. The same parameter is retained through the actual whole source
behavioral step. The slice and prior checkpoint are induction resources,
not supplied endpoint or source-marginal laws.

[SourceServiceResolutionResponseCompletion](../Vegas/Game/SourceServiceResolutionResponseCompletion.lean)
connects a supported original intention from that memory lottery to the actual
normalized response and its initialized continuation. Protected stopping
accepts the newly submitted packet's exact identifier and leaves no miss.
The endpoint agrees with both the effective successor's typed state and the
restored intended successor's typed state; its decoded history is the
effective one. Foreign policies may be arbitrary. The whole original history
and stopped response probabilities still need their joint transport.

[SourceServiceLateDecisionCompletion](../Vegas/Game/SourceServiceLateDecisionCompletion.lean)
handles an actual timely effective canonical transmission outside protected
inclusion as well. If the owner is silent afterward, every supported stopped
endpoint completes the event either with that chosen typed action or with
its real public expiry marker. Foreign policies are arbitrary, and the
horizon comes from the initialized trace and service contract. The result
gives no acceptance probability or independence, and no payoff comparison.

The [late-decision signaling probe](../scripts/experiments/late_decision_signaling_probe.py)
isolates the waiting comparison in a finite tree. Good and Bad sender types
both disclose in the source equilibrium, earning respectively `3` and `1`.
Off-path withholding is answered Good, consistently with withholding trembles
of orders `epsilon` and `epsilon²`. After waiting, the builder accepts Good's
disclosure and either type's withholding, but lets Bad's disclosure expire.
Every miss pays the actual default FALSE utility minus deposit `10`.
With equal waiting probabilities `epsilon`, late withholding is attributed to
Bad in the limit. Rational late play then gives Bad `2`, so its earlier wait
is profitable despite the miss penalty. Waiting probabilities `epsilon` for
Good and `epsilon³` for Bad instead make the same late withholding attributed
to Good. The resulting consistent limit is rational at every information set,
including after a public miss, and preserves the source terminal law.
The probe checks full support, exact Bayes limits and whole replacement
policies. It shows why the event-only geometric construction needs further
work; extending the successful view-dependent construction to all native
information sets still requires a joint likelihood and incentive argument.
This finite tree supplies no certified asynchronous scheduler or reporting
backend.
The completion interface permits a separate waiting rate at each prescribed
native information site. Free sites share a reference-tremble floor `lambda`,
so the probe requires `wBad / (wGood * lambda)` to vanish. A further full-support
tremble at prescribed sites must respect those relative rates. Choosing these
rates simultaneously across all native histories remains open. Private-view
dependent waits can also convey timing information about hidden types, even
when the completed binding value is constant. Their ordinary source/traffic
law therefore cannot reuse a source-view-only noise factorization simply by
discarding the waiting tags.

[SourceServiceSampleEnvironmentFactorization](../Vegas/Game/SourceServiceSampleEnvironmentFactorization.lean)
proves the real public sampling command's joint law. The sampled value is read
from the actual typed output and advances both carried source states. The
traffic includes the appended scheduler observation and unchanged own recall.
Its hypotheses are prior source-view factorization and supported readiness
and store alignment, without a roster or independent-noise premise. Joining
these kernels across delayed inclusion and stopping remains necessary before
the source-state posterior can be transported to native decision sites.

The auxiliary game carries actual native pending
state and attempted-choice recall. Its no-risk source embedding, consistency
and earlier incentive comparisons remain unproved; finite-game equilibrium
existence alone does not discharge them. Fresh reserves remain an alternative
if that hybrid proof fails.

[TerminalAuditContinuation](../GameTheoryExtensions/Analysis/Protocol/TerminalAuditContinuation.lean)
proves the exact comparison: the increase in expected collection times the
deposit must cover the increase in base payoff. Constant expected collection
leaves all whole-policy rationality comparisons unchanged, even when collection
is uncertain. [ReactiveServiceAuditContinuation](../Vegas/Pending/ReactiveServiceAuditContinuation.lean)
derives the certain-collection case from a publicly observed binding miss under
arbitrary future policies and scheduler commands. The candidate menu continues
to admit every effective response of that owner after the miss. Private
aliases are handled by the final normalization stage.

Probe C7 also checks a late canonical packet whose inclusion is still
unobserved when the owner chooses whether to send a second certificate-bearing
call. With acceptance probability `s = 1/4`, observation and conditional report
delivery probabilities `p = q = 1/2`, and deposit `D = 2`, baseline collection is
`3/4` and collection after the second call is `13/16`. The extra expected fine
is only `1/8`; sending the certificate gains `1/2`, so fixed silence is worse
by `3/8`. Rational raw continuation preserves the protected source law in this
finite game. This is design evidence, not a proof for every builder.

The probe also checks the first late binding opportunity, before any packet
has been attempted. A builder can include a certificate-bearing first packet
and expire a bare one, using only public packet contents. With deadline `3`,
reaction delay `0`, inclusion bound `1`, and a late turn at clock `2`, expiry
at clock `3` precedes any overdue protected-inclusion obligation. Bare play
then pays the certain public-miss charge `D`, whereas the included evidence
packet pays expected charge `rho * D`. Even with rational raw play after the
miss, the extra packet gains `(1 - rho) * D`; increasing the deposit increases
this gap. Opening raw play before that unrecorded binding opportunity supplies
a rational completion in the checked game when `rho * D >= 1/2`, preserving
the protected source law. This schedule is a contract blueprint, not a native
Lean instance over all raw histories. A recorded protected packet and lawful
resolution withholding must not trigger that expansion.

The same boundary includes overdue but unexpired bindings. A scheduler can
activate the owner at the deadline, include and reject a certificate-bearing
packet, expire the binding, then activate the next player without another
owner turn. Silence and transmission both incur the certain public-miss
charge, but only transmission communicates before the next decision. No
deposit increase deters that communication. The actual acceptance deadline
therefore cannot be an additional gate on binding-opportunity risk.

[LocalizedEnforcement](../GameTheoryExtensions/Analysis/Protocol/LocalizedEnforcement.lean)
provides the depth-free restriction-extension step with retained charges in the
source utility. Only excluded actions designated as auditable need a collection
bound and a clean legal comparator; other exclusions need a direct continuation
comparison. Those runtime premises remain to be proved. Unusable private opening
material alone is not an auditable offense: the source's value-plus-withholding
repair preserves the joint parameter and public-outcome law for arbitrary
allowed payoffs and guards. [BindingSubmissionCoupling](../Vegas/Game/BindingSubmissionCoupling.lean)
couples its actual mixed native transmission and implementation memory before
inclusion, without a calendar assumption.
[ReactiveBindingFrameCommands](../Vegas/Pending/ReactiveBindingFrameCommands.lean)
couples the actual clock, sample and expiry commands when the shadow's
remembered outcomes belong to completed events. The law includes service
recall and audit data. Packet inclusion and general pending private overrides
remain separate.
[ReactiveBindingPendingExpiry](../Vegas/Pending/ReactiveBindingPendingExpiry.lean)
proves the actual due-expiry joint law for a pending unusable binding: private
repair remembers the original failure, and both executions complete with that
same failure and public miss marker. The frame retains service recall, traffic,
receipts and reconstructed owner input. This supplies no additional fine or
whole-policy settlement comparison; generic continuation closure, retained
admission and consistent beliefs remain open.
[ReactiveBindingRiskResolve](../Vegas/Pending/ReactiveBindingRiskResolve.lean)
derives first timely FALSE admission in the actual repaired risk menu, without
a protected-delivery or full-menu-coverage premise. Any actual waiting/FALSE
response mixture has a joint law through the retained implementation, with
full frame and private memory preserved and no fallback on support. This
closes that response step; later inclusion and raw certificate responses remain
separate continuation obligations.

[BindingFrameSettlement](../Vegas/Game/BindingFrameSettlement.lean) proves
that every preserved frame gives exactly the same actual traffic, final
record, audit kernel, expected utility vector and realized payoff-vector law.
Earlier charges and correlated partial collection are allowed. The open
continuation proof must preserve that frame, including the correct original
candidate selected by the accepted handle when attempts overlap.
[ReactiveBindingCertificateRepair](../Vegas/Pending/ReactiveBindingCertificateRepair.lean)
proves a concrete capability distinction. The actual bare response fixes its
fresh owned candidate to arbitrary raw material without checking the source
payload type. A mistyped owned certificate then resolves in the original
execution and fails in the typed-default replacement, although their networks
are equal. This obstructs copying every future raw response and supplies no
profitable-deviation or equilibrium counterexample.
A stopped comparison would need one legal continuation shared across hidden
histories. After a public miss the one-time deposit is already sunk; another
packet's total collection bound supplies no incremental fine. An environment
expiry can occur without an owner turn, so repair cannot insert a decision
there. A late canonical call can also be accepted without a miss or charge;
stopping earlier at a protected wait needs the actual waiting comparison.
[ReactiveMissingBindingTransport](../Vegas/Pending/ReactiveMissingBindingTransport.lean)
isolates the absent-opening case. Its actual candidate is blocked, so a
replacement removes no original owned certificate capability. Every subsequent
effective owner response remains available and emits the same packet; an
arbitrary bounded raw response must first be normalized at the original input
to avoid acquiring newly available evidence. The proof derives actual candidate
tables, known-envelope equality and normalization from the real transitions.
It does not preserve later handler acceptance: an uncertified opening claim
may fail against the original candidate and succeed against the replacement.
Those static packet breaches retain their collection comparison, with no new
fine after an earlier public miss. Whole-policy repair remains open.
[ReactiveMissingOpeningEvidence](../Vegas/Pending/ReactiveMissingOpeningEvidence.lean)
derives this classification from an actual missing commitment and arbitrary
subsequent native rounds. Its handle remains blocked; authentic owned or
forwarded evidence cannot certify any later claimed opening of that handle.
The emitted packet is therefore an existing signed-content breach, with the
same final-record verdict and partial collection bounds. No payoff dominance
or additional collection after an earlier charge is inferred.
[ReactiveBindingAcceptedOpening](../Vegas/Pending/ReactiveBindingAcceptedOpening.lean)
derives typed binding provenance and the actual guard result from handler
acceptance. Original acceptance preserves the full repair frame, including
publication failure. A matching authentic certificate also transfers repaired
acceptance back to the original state. Acceptance created only by repair
therefore identifies a signed-content breach in the actual pending envelope.
The stopped whole-policy comparison remains to be proved.
[ReactiveBindingInertWindow](../Vegas/Pending/ReactiveBindingInertWindow.lean)
supplies an actual finite coupling through waiting and activation commands.
It preserves the full frame, both input recalls and original opening
capabilities, using original-input normalization and the retained
implementation's actual private memory. Owner responses emit no new
commitment; foreign raw responses and the adaptive public scheduler keep
their joint law. These operational restrictions define the proved window,
not a general repair theorem. Inclusion, first-breach stopping and the
terminal payoff comparison remain separate.
[ReactiveBindingOpeningStep](../Vegas/Pending/ReactiveBindingOpeningStep.lean)
classifies actual pending opening inclusion, covering invalid tokens and
paired rejections. It preserves the full frame or identifies an owner-authored
signed breach in that same envelope. Unchanged foreign catalogues derive the
author of repaired-only acceptance.
[SourceServicePastCommitmentTraffic](../Vegas/Game/SourceServicePastCommitmentTraffic.lean)
supplies actual old-commitment provenance for the stopped repair. Issued tokens
at a ready sequential event cannot name a later rank. Sending no further owner
commitments preserves this bound under every foreign response and scheduler
command; after the current event completes, old token-valid owner commitments
can only address completed events. The whole stopped evaluator and terminal
comparison remain open.
[ReactiveBindingCommitmentStep](../Vegas/Pending/ReactiveBindingCommitmentStep.lean)
uses completed addressed events to couple old owner commitment inclusions.
Foreign commitments use their actual immutable candidate meaning; invalid
tokens and public rejections retain the same false receipt and full frame.

### Deviation proof boundaries

Each excluded action needs one legal continuation comparison, shared across
the hidden histories of its information set and valid against whole future
policies. The comparisons can be proved separately and combined by
`sequential_equilibrium_extends_of_local_collection`. Retained actions need
their own rationality proof; an exclusion theorem cannot supply it.

| Behavior | Separate proof obligation | Checked boundary and open edge |
| --- | --- | --- |
| Protected fresh binding call | Show that completion records its actual handle and cannot be an omission. | Exact first-turn play supplies the protected call and keeps the owner's omission detector and full risk flag clear against arbitrary foreign raw policies. Its packets pass the actual final-record verdict, so authentic sampling collects zero owner charge. The strategic source embedding and local continuation comparisons remain separate. |
| Normalization-equivalent responses | Preserve the actual response transition and emitted packet. | Reactive normalization supplies the exact local equality. This does not erase a distinct fresh identifier or authentic extra evidence. |
| Canonical binding with unusable private opening | Repair private candidate capability while preserving the full typed source readout and actual settlement. | Actual accepted unusable bindings have a constructed frame and exact common completion; due expiry also preserves the pending-failure frame. Later claims for a genuinely blocked handle are signed breaches. Mistyped material has an owned certificate capability absent from a typed-default replacement. Later raw closure and the whole-policy equilibrium comparison remain open. |
| Forbidden signed packets at a clear protected history | Bound base gain and actual collection, and exhibit one clean legal continuation under the same belief. | Constructor breaches, invalid-token or foreign-actor packets, wrong node kinds, fresh packets addressed to completed events, wrong current-event handles, public guard failures and wrong opening ownership or public binding association have derived conditional collection. The information-local classifier supplies the actual risk-to-effective-to-raw extension with the fixed deposit and comparator. Other exclusions and the source equilibrium embedding remain open. |
| Two packets for one event before completion | Select a forbidden actual envelope from the pair and derive its collection bound. | Actual initialized settlement accepts at most one identifier for the event. A clear recorded prefix plus another same-event response reconstructs the pair; at least one packet is forbidden, even if the builder accepts the newer one. The actual committed-choice collection and risk-extension comparison are checked. This is a total-charge bound at a clear site, without renewed deterrence after a fine. |
| Late unrecorded first binding opportunity | Admit rational native continuation before a content-dependent acceptance/miss lottery. | Probe C7 demonstrates why excluding the evidence packet can fail for every positive deposit. The auxiliary source/native embedding and its earlier incentive comparisons remain open. |
| Public binding miss | Admit rational continuation with the deposit already certain. | Actual post-miss whole-policy rationality equals base-payoff rationality. Joint beliefs and equilibrium completion of the auxiliary game remain open. |
| Earlier packet offense with uncertain collection | Use the change in conditional expected collection, or admit rational raw continuation. | The exact incremental-charge identity is checked. Coverage of another packet alone supplies no positive increment; no independence premise is implicit. |

Monitoring assumptions belong to the collection branch: the challenge-window
backend must prove authentic observation and timely report delivery. They are
not needed for normalization or for equality of settlement along a preserved
frame. Scheduler assumptions belong to protected source play and the generic
continuation coupling. Keeping these premises explicit isolates unresolved
cases without weakening the capstone or duplicating the proof machinery.

The initialized-play audit theorem does not supply a clean comparator from
every clear prefix. A false risk flag alone says nothing about an earlier
packet's extra evidence. At a legal risk-menu prefix, however,
`riskPacketFacts_history` derives protected conforming unique owner calls and
their good actual settled content from persistent clarity. Other players may
have taken expanded effective actions. Earlier silent binding turns are allowed.

`sourceServiceImmediatePolicy` uses actual local recall and decides at the
current protected unrecorded opportunity, without an earlier turn-index test.
It is admitted at every legal risk-menu history. At an active clear owner
site, its response supplies `BindingTurnsRecorded` for every earlier binding
turn: a completed binding has accepted-call provenance, and an unfinished
earlier turn still names the current ready event. Recorded pending calls are
preserved. These are checked in
[SourceServiceRiskPrefix](../Vegas/Game/SourceServiceRiskPrefix.lean),
[SourceServiceImmediatePolicy](../Vegas/Game/SourceServiceImmediatePolicy.lean)
and [SourceServiceImmediateRecall](../Vegas/Game/SourceServiceImmediateRecall.lean).
`sourceServiceImmediatePolicy_clean_continuation` derives those prefix
resources and preserves full clear risk and good owner packets through every
supported raw suffix within the remaining horizon. No foreign source policy
is assumed. `sourceServiceImmediatePolicy_audit_clear_after_prefix_response`
then proves zero actual owner charge for every authentic sampling kernel,
including at the final remaining-round boundary. Positive observation or
report coverage is unnecessary for this soundness direction. The suffix and
audit are checked in
[SourceServiceCleanContinuation](../Vegas/Game/SourceServiceCleanContinuation.lean)
and [SourceServiceImmediateAudit](../Vegas/Game/SourceServiceImmediateAudit.lean).
The same policy is a fixed function of the owner's actual recall and current
view. In [SourceServiceImmediateComparator](../Vegas/Game/SourceServiceImmediateComparator.lean),
`sourceServiceImmediateComparator_terminal_law` identifies whole-policy
replacement in the finite risk-menu game with that physical continuation,
against arbitrary opponent behavioral policies. Admission is required only
at actual legal histories. `sourceServiceImmediateComparator_clean_lower`
uses this one fixed policy across every hidden history of a clear information
site and every belief there: a terminal base-payoff lower bound gives that
lower bound together with zero owner charge. This supplies the clean
comparator branch. Concrete collection bounds for the other excluded actions,
comparisons for uncharged exclusions, and the source equilibrium embedding
remain separate obligations.

[SourceServiceRiskExtension](../Vegas/Game/SourceServiceRiskExtension.lean)
constructs the actual risk-menu restriction of the complete effective runtime.
Every excluded choice lies at a locally clear site, since risky sites already
admit all effective responses. Its SE extension theorem derives the collection
bound for classified auditable packets from the challenge-report contract, uses the fixed clean
comparator, and sizes the deposit with the existing payoff extrema.
Retained payoffs are the actual net utility, including prior charges. The
conclusion preserves retained beliefs, complete history laws and the joint
realized settlement law. Actual legal-prefix classification confines the
separate shared continuation comparison, `riskOtherExclusionComparisons`, to
a canonical binding with absent or mistyped private opening material.
The predicate compares actual audited
continuations and requires one legal policy across the hidden histories of
the information site.

The extension uses authentic observation and conditional report-delivery
coverage for packets forbidden by the final record. This includes auditable
departures beyond constructor breaches: a bare commitment using a
noncanonical prepared handle, or a certified opening that fails its guards,
can fail the final settled verdict. Collection for such a packet still needs
a proof of its actual final forbiddenness. Correct canonical bindings with
unusable private opening material can pass that verdict; their
capability-repair obligation remains distinct even with broader coverage.

[SourceServiceNoncanonicalBinding](../Vegas/Game/SourceServiceNoncanonicalBinding.lean)
proves final forbiddenness for a wrong prepared handle under every actual
complete continuation. Readiness fixes the binding ordinal until the event
completes, and later completions preserve its count in the final record.
Acceptance of the wrong handle does not change this verdict. Complete play
and final-record coverage give the observation-times-delivery collection
bound under arbitrary subsequent behavioral policies. This does not classify
correct-handle private capability defects.

[SourceServiceGuardFailure](../Vegas/Game/SourceServiceGuardFailure.lean)
proves that an opening's false public guard verdict persists from actual
readiness through every later raw continuation. Predecessor fields are already
stored and cannot change. Even a certified opening therefore fails the final
content check and gets the same conditional collection bound under complete
play and final-record coverage.

[BindingCapabilityReadout](../Vegas/Game/BindingCapabilityReadout.lean)
proves that a candidate-only repair frame with no typed value overrides
preserves the entire graph store and the full typed terminal source readout.
It consequently preserves arbitrary typed source utility and the joint
readout/actual audited payoff-vector law, including prior charges and
correlated sampling. Constructing and preserving that frame along an actual
raw continuation up to a capability-exposing violation or public miss remains
open.

[BindingCapabilitySubmission](../Vegas/Game/BindingCapabilitySubmission.lean)
constructs that candidate-only frame for an actual accepted canonical binding
whose absent or mistyped opening material decodes to failure. Replacing the
material with no opening gives the exact same completed configuration and
accepting receipt. Own input reconstructs the original private candidate and
response; the inclusion step preserves the derived frame. Its joint full
typed readout and actual audited payoff-vector law is exact. Arbitrary later
raw-continuation closure and the equilibrium comparison remain open.

The source embedding must retain the original payoff domain. The capstone in
[SourceServiceCompilation](../Vegas/Game/SourceServiceCompilation.lean) reads
a fixed initial parameter and the public outcome. Its prescribed execution
preserves the full typed readout, but this does not make every arbitrary
utility of hidden terminal bindings compatible with the value-only source
game. An accepted unusable binding stores failure without a public miss;
the source's value-only admission excludes that action. A utility rewarding
that private failure would therefore require a different source admission or
runtime enforcement. Replacing unusable material with no opening still
produces failure, so the candidate-only kernel alone supplies no admitted
value-only source replacement. The existing parameter/public repair and
the private-capability continuation argument address separate parts of this
obligation.

[SourceServiceAuditableCollection](../Vegas/Game/SourceServiceAuditableCollection.lean)
combines constructor breaches, authorization breaches, wrong node kinds,
fresh packets addressed to completed events, wrong current-event handles,
public guard failures and wrong opening ownership or public binding association
in an information-local predicate.
Own recall and current view reconstruct the entire actual emitted envelope,
including its serial, evidence and readiness token. Committing a classified
choice derives traffic persistence and the final forbidden verdict under
arbitrary later policies, then supplies its expected collection bound.
`auditableBreachAtSite` uses this predicate directly in the enforcement
extension, together with recalled same-event responses as a separate pair
class. Wrong current-event handles and public guard failures therefore
need no separate comparison hypothesis. Neither do the invalid-token and
foreign-actor classes in
[SourceServiceAuthorizationBreach](../Vegas/Game/SourceServiceAuthorizationBreach.lean).
For these classes, receipt soundness uses the actual emitted envelope:
identifier equality alone could refer to a different hypothetical packet.
The collection continuation derives final emission from the chosen response
and traffic persistence. A premature call without a readiness token is
covered; valid-token off-turn calls are not automatically forbidden.

[SourceServiceNodeKindBreach](../Vegas/Game/SourceServiceNodeKindBreach.lean)
adds commitments addressed to a non-binding node and openings or withholding
addressed to a non-resolution node. The public graph check is immutable.
Actual handler acceptance certifies it, and initialized receipt soundness
and emitted-envelope identity derive the final forbidden verdict. Thus even
a valid-token, evidence-free withholding packet addressed to its sender's
binding is classified. This class uses the same partial-evidence collection
bound. Other packet classes retain their own obligations.

[SourceServiceCompletedPacket](../Vegas/Game/SourceServiceCompletedPacket.lean)
proves that a fresh identifier allocated after its named event completed
never acquires an accepting receipt under arbitrary subsequent responses and
scheduler commands. Complete play supplies the actual final forbidden
verdict. The auditable classifier reads completion from the current public
view, and its committed-response caller derives the next serial directly.
No fresh-identifier assumption is added to the backend. An original accepted
envelope remains permitted; two calls before completion instead use the
distinct pair argument below.

[SourceServiceDuplicatePackets](../Vegas/Game/SourceServiceDuplicatePackets.lean)
proves that two genuinely emitted distinct identifiers for the same event
cannot both have accepting receipts. At complete settlement at least one
exact envelope is forbidden. Actual traffic persistence and bounded terminal
evaluation give the existing partial-observation/conditional-delivery
collection bound under arbitrary later behavioral policies. The forbidden
packet is selected separately at each final history, so the builder may
accept the newer packet without invalidating the argument. At a clear legal
risk-menu prefix, own recorded-event recall and another same-event response
derive the earlier actual record and the fresh second record directly;
serial bounds distinguish their identifiers.

[SourceServiceRecordedCollection](../Vegas/Game/SourceServiceRecordedCollection.lean)
classifies a response naming an event already submitted in own recall. At a
clear input it is excluded by the risk menu. Committing that information-local
choice reconstructs the actual packet pair, and one-step terminal evaluation
composes with its arbitrary-continuation collection law. The risk extension
derives the clear legal prefix from the restriction history and combines
this collection with the same clean comparator and deposit. The class is
removed from `riskOtherExclusionComparisons` without a stronger backend
coverage premise. This is a bound on total one-time charge, not a positive
incremental collection probability after an earlier offense.

[SourceServiceResolutionComplement](../Vegas/Game/SourceServiceResolutionComplement.lean)
proves that, at a clear actual legal resolution prefix, a bounded effective
response outside the packet and recorded-response classifiers is retained.
The actual minted token and public completion record locate its ready owned
event. Classifier complements derive the public guard, ownership, association
and content checks; actual soundness, binding and input-recall invariants then
derive the fresh envelope and retained TRUE or FALSE response. Silence is
retained directly. No fresh-envelope, source-policy or backend premise is
added.

[SourceServiceUnusableBinding](../Vegas/Game/SourceServiceUnusableBinding.lean)
completes the actual clear-prefix partition. A remaining binding uses the
current canonical counted handle with evidence-free content. Well-typed
private opening material gives a retained response; absent or mistyped
material is the exact remaining uncharged class. The information-site caller
derives that class from an actual history witness and the risk extension
narrows its upper comparison accordingly. The same arbitrary terminal
utility and evidence backend remain in scope. This class is not assumed
harmless; its shared whole-policy continuation comparison remains open.

[SourceServicePublicRejection](../Vegas/Game/SourceServicePublicRejection.lean)
derives persistent nonacceptance from an event's prior completion or failing
actual public handler conditions while it is ready. Sequential readiness
keeps those public conditions fixed until completion. The completed-event
class and openings with wrong candidate ownership or accepted public binding
association use this same operational argument. The latter checks are public
and are integrated into the actual auditable collection comparison; they
need no assumption that the watcher sees every packet.

For a current resolution, the actual bounded effective response law in
[ReactiveServiceOpening](../Vegas/Pending/ReactiveServiceOpening.lean)
reduces a fresh permitted envelope to the retained FALSE withholding or TRUE
opening. It uses actual certificate soundness, binding invariants and input
recall. Guard success alone does not establish those conditions; the wrong
public ownership and association cases use the derived rejection and
collection branch above. Unusable private material at a canonical binding remains a
distinct repair obligation.

[ReactiveSettledCollection](../Vegas/Pending/ReactiveSettledCollection.lean)
states that broader backend obligation as `FinalForbiddenEvidenceCoverage`.
For an actual persisted signed packet forbidden by the final record, the
expected one-time collected charge is at least observation rate times
conditional delivery rate. The continuation lemma derives traffic persistence
under arbitrary later policies; final forbiddenness is an explicit
operational premise. The classified-packet proofs derive it from the actual
complete record. Sampling may be partial and correlated, and no report must arrive
with certainty.

[SourceServiceRiskRawExtension](../Vegas/Game/SourceServiceRiskRawExtension.lean)
composes that conditional effective-menu extension with private-alias
transport. It uses the same backend and fixed deposit throughout, and
preserves the exact joint typed terminal source readout and sampled payoff
vector. Its input remains an audited risk-menu SE, with the explicit
other-exclusion comparison predicate.

The auxiliary equilibrium required there is an equilibrium of the actual
audited risk-menu game. Embedding each given source SE into that game remains
open. Local clarity alone cannot identify its source-compatible information
sites: another owner's risky packet can reveal a certificate to a still-clear
observer. Information absent from every protected source execution needs free
rational completion.

[AsyncServiceSourceSites](../Vegas/Game/AsyncServiceSourceSites.lean) defines
an information-local candidate classifier, independent of the given source
equilibrium. A witness is an actual initialized execution of some admitted,
effective source profile under arbitrary turn timing, with a legal risk-menu
prefix, every owner's persistent risk clear, and a clear current owner
opportunity. Earlier silent turns remain in recall. Exact first-turn behavioral
play visits only classified decision inputs. A history with hidden foreign
risk can share such an information value; the classifier does not erase that
history from the belief.

[AsyncServiceCounterfactualBeliefs](../Vegas/Game/AsyncServiceCounterfactualBeliefs.lean)
derives the common owner-reach factor from actual own recall throughout the
native information fiber. Every previous silence and its preceding view enter
that factor. At supported information it cancels exactly from Bayes
normalization, leaving opponent-and-nature reach mass. Clean and escaped
conditional probabilities are their respective counterfactual masses divided
by the sum. This identity does not bound their ratio or remove foreign
deferral probabilities from the clean denominator.
The same module proves that every hidden history at source-compatible
information has no owner's public miss, and that the counterfactual mass of
such misses is exactly zero. The public record excludes this branch even
when private foreign opportunity or submission risk is hidden.
[AsyncServiceForeignEscape](../Vegas/Game/AsyncServiceForeignEscape.lean)
derives that the focal owner's full risk is clear at every hidden compatible
history. Escape is exactly some foreign owner's private recalled submission or
opportunity risk. Its finite union bound and the actual clean witness yield

\[
\Pr(\text{escaped}\mid I) \le
\frac{\sum_{j\ne i}\mathrm{CF}_I(\text{private risk}_j)}
     {\mathrm{CF}_I(\text{clean})}.
\]

Full mixing makes the actual clean denominator positive. It does not supply a
rate or identify the numerical timing budgets with these counterfactual masses.
That ratio must vanish for one consistent native family, retaining foreign
waiting likelihoods and the same free continuation at all information sites.

[ReactiveCleanPrefix](../Vegas/Pending/ReactiveCleanPrefix.lean) proves that a
risk-menu prefix with every owner's persistent flag clear has a canonical
trace with identical state, actions and nature transitions. It may stop before
a late opportunity's response records risk. The classifier's witness therefore
supplies a legal canonical decision history. Source-relative posterior bounds
and local comparisons remain open.

[ReactiveCleanPrefixProbability](../Vegas/Pending/ReactiveCleanPrefixProbability.lean)
proves equal probabilities for every clean realized history, and every event
consisting of such histories, in the canonical and risk-menu representations
of the same physical policy. The event keeps its original probability mass
at each finite cutoff. A currently late endpoint is allowed before its
response records risk. [SourceServiceCleanPrefixLaw](../Vegas/Game/SourceServiceCleanPrefixLaw.lean)
derives canonical admission for every admitted source profile and arbitrary
turn timing, then identifies these clean-prefix masses with the actual
physical prescribed execution. Behavior after risk expansion is not
identified. Conditional escaped-branch bounds, source-information projection
and rationality still require their own proofs.

[AsyncServiceCleanCompletionLaw](../Vegas/Game/AsyncServiceCleanCompletionLaw.lean)
allows any risk-menu continuation agreeing with prescribed turn-counted play
at source-compatible information values. Its initialized probability for each
clean prefix, and each clean event at any finite cutoff, is unchanged and
matches the physical prescribed law. The proof handles zero-probability
predecessors without an agreement assumption there. Agreement is an explicit
premise; this does not construct a rational completion or establish a valid
prescription at resolution sites.

The source-compatible classifier retains actual own recall, including benign
protected deferrals. Its initialized source witness has clear persistent risk
for every owner and a clear current owner opportunity. Consequently, an
unrecorded owned decision at such information has a protected inclusion
window, for bindings and resolutions alike. Exact initialized first-turn play
visits only source-compatible information. This structural containment does
not establish rationality at those sites, their source-relative beliefs, or a
fully mixed native approximation with the required conditional limits.

[SourceServiceResidualSites](../Vegas/Game/SourceServiceResidualSites.lean)
supplies aligned source residuals at every legal native history for every
response menu and scheduler. Actual readiness identifies the residual rank;
the event's output type then identifies an aligned source commitment or
disclosure. Earlier arbitrary deviations require no source-strategy support
premise. This is an effective source-configuration decoder, not a joint
belief transport or a restoration of failed disclosure intentions.

[SourceServiceReadyObservation](../Vegas/Game/SourceServiceReadyObservation.lean)
derives the exact same full typed graph observation at every earlier recalled
own turn for the current event. Sequential readiness prevents another event
from completing while this one remains unfinished; responses preserve the
graph configuration. The actual compiled source choice law is consequently
identical across these inputs for every source profile. Network observations
and private candidate meanings are not equated. This discharges source-choice
stability during the event, while the joint source posterior remains open.

[PrescribedCompletion](../GameTheoryExtensions/Analysis/Protocol/PrescribedCompletion.lean)
proves that simultaneous consistent rational completion at free sites retains
the specified strategy limit at prescribed sites. It preserves the complete
initialized terminal history law if reference play only visits prescribed
decisions. The site classification and convergence remain premises; prescribed
site rationality and compatibility with the given source beliefs remain open.

[SourceServiceAliasEquilibrium](../Vegas/Game/SourceServiceAliasEquilibrium.lean)
supplies the final normalization stage: an audited SE of the complete
effective native menu lifts to its raw private-action aliases, with projected
consistent beliefs and the exact joint typed source-readout and sampled-payoff
law. Final traffic and the settled record are invariant, so correlated
collection and prior charges are preserved. The risk menu expands to all
effective actions once risk appears; alias transport then lifts the resulting
effective-menu equilibrium to the raw runtime. Harmless private aliases need
no additional collection premise or exclusion comparison. The original source
equilibrium embedding and the other effective-action comparisons remain open.

The comparator must start at an actual active owner site. A clear scheduler
boundary can follow a silent protected turn that already fulfilled the
builder's opportunity obligation; the builder need not give another turn
before expiry. Clarity at that boundary alone cannot guarantee a clean suffix.

Disqualification with default future actions is not the planned simplification.
An implementable trigger would require a public contract verdict, whose timing
depends on observation and report delivery. Disabling contract actions would
still leave the player able to send verifiable information through pending
packets or off-chain. Once collection is certain, the one-time deposit gives
no additional deterrence for that communication. Quitting therefore does not
remove the need for rational continuation play or solve the communication
obligation. The proof must account for permitted communication in those
continuations, with off-chain channels outside the model remaining an
explicit limitation.

Before proving the new retained menu's equilibrium, discharge the miss
continuation and enforcement obligations with the chosen scheme. In
particular, the calendar's zero-charge theorem cannot be generalized to every
retained history while retained deferral can reach a charged miss. Carry
those penalties in the retained utility, or supply a justified restriction
and extension that handles the miss histories. Zero charge is required on
the final equilibrium's supported play.

### Risks and open questions

- **Off-path contract obligations.** The contract must hold at histories
  where a deviator floods the pool. Requirement 2 protects only an owner's
  sole identifier, so a concrete builder needs only to reach that one packet
  in time, but it must be checked against flooding. The calendar instance
  already holds on every legal history.
- **Audit slot after a silent expiry.** When a deferred binding expires
  without a submission, the prescribed client's next fresh candidate slot
  (the lowest fresh slot) and the slot the audit expects (the count of
  completed bindings) diverge, so the audit would treat that owner's later
  prescribed commitments as nonconforming. This happens only on
  tremble-reached histories, but sequential rationality must hold there too.
  The turn-counted policy selects the audit's canonical slot and uses the
  protected inclusion gate. The retained menu now uses that slot too, with
  the weaker actual deadline gate so that late but accepted calls remain
  retained. The used-slot and recall invariants hold on every legal retained
  history (`retainedCanonicalSlots_history`), including after silent expiry.
  `retainedCanonicalSlot_resources` supplies capacity and freshness, and
  `sourceServiceTurnPolicy_retained` proves policy admission there. Rational
  continuation after a miss remains an open equilibrium obligation.
- **Removed actions must be framed or charged.** Every action outside the
  retained menu must be dominated under every extension of the source, which
  the repair argument achieves only by keeping play on retained histories or
  by authentic charged evidence. This rules out a decide-once menu (milestone
  2b) and is the check to apply to any future narrowing of the menu.
- **Redefining the prescribed policy** (milestone 2b) reaches many files: the
  timed policy and the timing law appear in tens of files. Site lemmas built
  on "silent now, submit at a later visit" persist in turn-counted form and
  become approximate off the calendar, with error the deferral weight.
- **The deviation lottery** (milestone 5) is the least understood obligation.
  If the builder's choice among a deviator's packets can depend on something
  that is not a function of public data and the deviator's own choices, the
  mixture argument fails. Today's selector (`reactiveLatest`) picks the
  latest packet, so the fixed calendar avoids the question.
  [ReactiveBindingPublicTraffic](../Vegas/Pending/ReactiveBindingPublicTraffic.lean)
  proves joint equality of the public network, receipts, scheduler input and
  recall, and all foreign inputs when private binding values differ. Canonical
  transmission, foreign raw responses and every inclusion at a sole-ready
  binding preserve it, including rejected and malformed packets. This is
  transition closure; the complete stopped scheduler law and value-independent
  miss probability remain separate.
- **Stage B beliefs.** Probe C5 suggests that depth differences are no
  obstruction, but the concurrent-window information sets are new. If they
  break the extension, D2's contract-ordered service is the fallback.
- **Deposit size.** A scheduler-uniform deposit may be large. The statement
  allows it to depend on the scheduler, which is enough for existence.
