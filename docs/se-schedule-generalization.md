# Generalizing the sequential-equilibrium schedule

## Status

This is a design note; nothing in it is checked in Lean except the library
lemmas it cites. It describes which scheduling restrictions
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

C1 compares D4 without enlarged deadlines against D3's timers; D1, where owners
do not wait, is not probed. Under the barrier order C4 cannot arise, so the
probes support preservation in every design once timeliness holds. They are
design evidence, not proofs.

## Completion plan

This section is the plan for finishing the work. Like the rest of the note it
is a design, not a checked result.

### Where the work stands

| Step | State |
| --- | --- |
| Finite probes | Done (above). Design evidence, not proofs. |
| Library lemmas | Done: proportional Bayes transport and the depth-free restriction extension in `GameTheoryExtensions`. |
| Readiness instead of announcements | Done. Prescribed clients, response menus and the audit read readiness (`PublicView.ownTurn?`, `freshServiceEnvelope`); the service grant is deleted from the runtime. The calendar menu's required binding at the owner's last visit (`bindingRequired`) still reads the roster. `Vegas.Paper.source_audited_raw_sequential_equilibrium` is proved against this, still under the fixed calendar. |
| Asynchronous chain model | Milestone 1 done: the contract is `AsyncContract` with per-event bounds and `AsyncTimely` (`Vegas/Pending/ReactiveAsyncContract.lean`); `rosterScheduler_asyncContract` proves the fixed calendar an instance with reaction bounds `event.val` and inclusion bound 0 (`Vegas/Game/ServiceRosterAsync.lean`). The timeliness lemma for prescribed play waits for milestone 2's prescribed policy. |
| Phase from public history | Started: `sourceService_phase_boundary` identifies a phase start by plan position, and the watcher calendar reads decision depths from the public clock. `DecisionPhase.position` and the roster plan prefix and suffix still index the calendar. |
| Completion-stopped phase law (milestone 2a) | Done. `Interaction/ReactiveStopping.lean` runs any scheduler until a stopping predicate and splits a full run there. `SourceServiceCompletion.lean` defines the completion law and completion boundaries and proves the bridge `TimedApproximant.response_completion_law` under a boundary-continuation hypothesis. Only `CompletionBoundary` and the continuation hypotheses are scheduler-generic: the bridge itself is still stated on `TimedApproximant`, `DecisionPhase`, the calendar menu and plan length, with an exact hypothesis, and needs a position-free `Within` restatement. `SourceServiceContinuationBridge.lean` proves that hypothesis for the fixed calendar and re-derives `response_continuation_law` from it. |
| Turn-counted policy and approximate continuation (milestone 2b) | Done for every contract scheduler. `sourceServiceTurnPolicy_boundaryContinuationWithin` bounds the distance from the source continuation by the sum of the remaining events' deferral weights, and `sourceServiceTurnPolicy_firstTurnCompletes` discharges its hypothesis from `AsyncContract` and `AsyncTimely` alone (`Vegas/Game/SourceServiceFirstTurnCompletes.lean`). The calendar keeps its timed policy. |
| Audit serial clause | Done. The audit's per-packet rule counts distinct identifiers per author (`Interaction.Message.distinctAuthoredCount`), so re-included copies do not shift serials, and the contract rejects a re-inclusion (`EventGraphRuntime.handle_eq_none_after_accepted_run`). Under `AsyncContract` alone, every fresh call of a player following the turn-counted policy, trembles included and whatever others do, carries the audit's serial and passes the full rule (`Vegas.sourceServiceTurnPolicy_serial`, `Vegas.sourceServiceTurnPolicy_permittedServiceEnvelope` in `Vegas/Game/SourceServiceCanonicalSerial.lean`). |
| General theorem | Not started. |

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
   only packets authored by the owner). Replays keep the original author and
   identifier, so a third party can re-queue an owner's older packet behind a
   newer one, and the calendar's latest-by-author selector then includes the
   stale copy. Relaying another player's packet, even one addressed to the
   owner's event, does not void protection: the builder tells authors apart
   by signature, and the calendar's selector never picks a foreign packet. A
   prescribed owner submits one packet of its own per event and may replay
   it, and every copy carries its identifier. Packets with several identifiers
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
- **Copies leave the model.** Replays (rebroadcasting a known envelope
  under its original author and identifier) were meant to model replay
  attacks, but they cannot: a copy stays the original author's message, and
  a fresh submission of another player's handle is rejected because
  `handle` requires the handle's owner to be the sender. That ownership check
  is the model's counterpart of binding the committer into a commitment, and
  an implementation that omits it cannot refine the model. With a builder
  that sees the whole pool at once, copies have no legitimate role. Their only
  uses were prescribed rebroadcasting (a full-support proof device),
  duplicate inclusions, packets kept alive past their deadline, and builder
  sensitivity to copies. Removing them makes off-turn sites single-action and
  needs no deduplication clause. The distinct-identifier audit count stays: it
  is what a contract keeps as a nonce if a chain does duplicate.
- **Send-time audit evidence (open).** The per-packet check
  (`EventGraphRuntime.permittedServiceEnvelope`) judges a packet against the
  public view at the moment it was sent: readiness, the deadline, and the
  serial against the sender's ledger. An auditor cannot prove send time; it
  sees a packet when it receives it, and a missed binding is attributable
  only after the deadline. An implementable variant would have each packet
  sign the block it was made against and check conformance relative to that
  block; what claiming an older block permits is not yet analysed. Late
  sends are not charged: they are deferral, and end in inclusion or a miss.

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
     sites. Deferral is neither charged by the audit nor hidden: staying silent
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
     keeps the pool for the current event to one owner identifier and its
     copies, and makes deferral the only error.
3. **Phase without position.** Dropped. The calendar chain is retired at
   milestone 6 rather than ported, and the position-free site datum (event,
   readiness, sole readiness) is a small definition inside the generic bridge
   of step 6 below.
4. **Depth-free extension and proportional beliefs.** Retarget the
   fixed-depth Bayes projections and restriction extensions, including the
   joint factorization with traffic noise; build beliefs at scheduler-created
   sites.
5. **Deviation lottery.** Mostly discharged by the serial audit: a second own
   identifier for an event is nonconforming whether or not the first was
   published, and the compiled menu never makes a second fresh call. The
   builder's choice among a deviator's packets therefore matters only on
   charged histories, where the extension bound holds whatever the builder
   does. What remains is the lemma that every second own identifier is a
   forbidden record. The obligation that the original wording missed is
   builder sensitivity to rebroadcasts (see "Waiting, misses and the
   charge").
6. **General theorem, stage A.** Generalize the scheduler parameter of
   `SourceServiceSpec` to any contract scheduler, with the horizon as a field,
   re-derive the deposit, and pin the new capstone in `Paper.lean`. The
   fixed-calendar theorem becomes a corollary through milestone 1's instance.
   The work, as new modules that leave the calendar chain green until the
   last step:
   1. `AsyncServiceSpec` (scheduler, horizon, delay, bound, contract, finite
      nature) and the calendar instance.
   2. The deposit over `(horizon, scheduler)` and its gain bound.
   3. The bound-aware audit gate, equal to today's rule at bound 0.
   4. Geometric deferral: a constant per-turn deferral probability that
      vanishes faster than the source's own trembles, so that beliefs after a
      withhold converge to the source's. The uniform split over later turns
      does not vanish at later turns.
   5. The canonical gated menu and its lemma suite; `bindingRequired`, which
      still reads the roster, is deleted.
   6. The generic bridge: `TimedApproximant.response_completion_law` and
      `TimedApproximant.completion_boundary` restated for any scheduler, with
      a `Within` version.
   7. Zero charge on retained histories, lifting the canonical conformance
      and serial results from "follows the policy" to "responds in the menu",
      with the treatment of misses fixed in "Waiting, misses and the charge".
   8. Milestone 4's beliefs.
   9. Generic local comparisons for the seven site kinds, each bound with
      `BoundaryContinuationWithin`. Large; not previously listed.
   10. Generic source-to-compiled step through the `lawError` limit lemma.
   11. Generic repair coupling (same public state, different private
       catalogue, round by round), the second-identifier lemma, and the
       compiled-to-native step through the depth-free extension. Large; not
       previously listed.
   12. The new capstone, the calendar corollary, and retirement of the
       calendar chain.

   Steps 1, 3, 4 and 6 are independent. After step 5, steps 7 and 11 run
   alongside steps 8, 9 and 10.
7. **Stage B.** Barrier-order graph: commutation, timing information,
   concurrent phase law.
8. **Pending-message stack.** Collapse staging, express the epoch service as
   a contract scheduler, and retarget or retire.

Milestones 2, 4 and 5 are each meaningful on the fixed calendar, so the
capstone stays green throughout; only milestone 6 changes its statement.

### Waiting, misses and the charge

The source is an idealization; the target must be realistic and the source
must compile to it. In the target, waiting is a real option: an owner who
waits gives up inclusion probability in exchange for a later, possibly better
informed decision. Within one game the builder is fixed, so that price is a
well-defined probability, and a builder that grants no second turn makes
waiting expensive.

What waiting buys depends on the graph. On the sequentialized graph nothing
else in the game completes while an owner's event is ready, so waiting learns
nothing the source game models: only inclusion timing, leaked packets and
rebroadcasts, which are stated limitations. Against the source's information,
waiting is pure cost. Under the barrier order (stage B) waiting does learn
who has committed, and the barrier order is what must keep that from mattering.

A missed binding is charged. The contract cannot distinguish an owner who
chose not to send from one who was censored, so it charges both alike: it
plays along with censorship. Protected inclusion is exactly the assumption
that a timely sole packet is never censored, so a prescribed owner is charged
only after waiting past its guarantee. A miss differs from a source forfeit:
the forfeit stays hidden until the reveal (it compiles to a handle with no
opening), while a miss is public at the deadline. The source therefore stays
as it is, and the miss is a charged outcome of the target.

Open obligations this creates:

- **Charges on retained histories.** Retained deferral reaches a miss with
  probability of order the deferral weight, so zero charge cannot hold on
  every retained history. Either the charge enters the compiled game's
  payoff and vanishes in the limit, or deferral past the last turn whose
  successor still fits the gate leaves the retained menu as a charged gamble.
  The second is dominated only if waiting buys nothing source-relevant, which
  holds on the sequentialized graph up to the stated limitations.
- **Play after a miss.** Other players need rational play at sites where an
  owner has publicly missed. If such histories are reached only through
  removed actions, the extension argument supplies the continuation as it
  does for charged evidence today.
- **Late sends.** The policy stops fresh calls once protected inclusion can
  no longer land before the deadline, but an auditor cannot see send time,
  so later sends are not charged. They are retained deferral: they land or
  end in a charged miss.
- **Play after a miss (proposed route).** The proof would pass through an
  extended source with a penalized "public miss" move at each binding. The
  restriction extension supplies play after a miss there, because the penalty
  pays its comparison, and compiled deferral is the mixture of that miss and
  deciding later. This requires the chance that a deferring owner gets no
  further turn to be independent of hidden values given the owner's
  information. To be validated by a finite probe before implementation.

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
  It is being resolved by giving the turn-counted policy its own decision at
  the audit's canonical slot, with a gate: no fresh call unless protected
  inclusion still lands before the deadline, so neither a late call nor a
  call overtaken by expiry desynchronizes the audit's checks. The retained
  menu is still built from the calendar decision and needs a canonical
  variant before milestones 4 and 6.
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
- **Stage B beliefs.** Probe C5 suggests that depth differences are no
  obstruction, but the concurrent-window information sets are new. If they
  break the extension, D2's contract-ordered service is the fallback.
- **Deposit size.** A scheduler-uniform deposit may be large. The statement
  allows it to depend on the scheduler, which is enough for existence.
