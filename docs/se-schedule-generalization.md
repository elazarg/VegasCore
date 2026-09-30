# Generalizing the sequential-equilibrium schedule

## Status

This is a design note; nothing in it is checked in Lean. It describes which
scheduling restrictions `Vegas.Paper.source_audited_raw_sequential_equilibrium`
imposes, argues that preservation should survive their removal under a
contract on the scheduler, and lists the obligations of a direct general
theorem for every contract-satisfying order policy. Finite probes support the
contract; two narrower reductions to the existing theorem are recorded as
intermediate results.

## What the library no longer requires

The pinned GameTheory library defines sequential rationality on terminal play,
so a decision site no longer carries a remaining step count, and the pinned
theorem states standard sequential equilibrium of complete play. Three upstream
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

The full-language proof still uses a common depth in two places. The first
is the fixed-depth Bayes projections of `Vegas/Game/SourceServiceBayes.lean`
and `Vegas/Game/RevealServiceRosterBayes.lean`, which the reach-weight
transport can replace. The second is the restriction extensions of
`Vegas/Game/SourceServiceRestrictionExtension.lean` and
`Vegas/Game/RevealServiceRosterAudit.lean`, which the depth-free extension can
replace. Under the fixed calendar the rank supplies that depth. Once both uses
are retargeted, no depth is needed under an adaptive order. The roster plan's
remaining role is operational: it identifies the granted event and phase at
each history.

## What the theorem fixes

The service of `SourceServiceSpec` is a fixed calendar:

- `SourceServiceSpec.scheduler` is `rosterScheduler`, which plays `rosterPlan`
  (`Vegas/Game/ServiceRoster.lean`). The plan visits every event in numeric
  order. Each event gets a fixed block: grant, the roster activations,
  include-latest or sample, `event.val + 1` clock ticks, and expiry.
- The next instruction is selected by the length of the history. Only
  delivery, through the network policy, is randomized.
- The graph is `EventGraph.sequentialize` of the compiled graph
  (`Vegas/Game/RevealService.lean`), so every source-earlier event is a
  predecessor of every later one.

The pending-message theorems instead take an adaptive
`EventGraphRuntime.ServiceOrderPolicy`, which chooses each epoch's order from
the public pool, receipts, application projection, and environment history, and
work in either dependency mode.

In sequential mode a fixed order costs nothing: only one event is ever ready,
so every valid scheduler grants events in source order. The restrictions that
matter are:

- **Concurrent dependency mode.** Different players' bindings between two
  public events have no fixed relative order.
- **An adaptive calendar.** The choice of the next ready event, and of whom to
  activate, cannot depend on the history.

## Why preservation should survive

The theorem asserts that *some* target sequential equilibrium has the source
law. Off-path observations that carry no verifiable evidence can therefore be
neutralized through beliefs. Observations that do carry verified evidence
cannot, and the pending pool can contain such evidence (below).

### A candidate counterexample and why it fails

A and B commit concurrently in a coordination game: each commits a bit, and
both receive one when the bits agree. At the source, B commits without learning
A's bit, and uniform mixing by both is an equilibrium. Suppose an adaptive
order grants B's event first exactly when the pool contains a replay broadcast
by A. Replays of published messages are permitted, so the audit never charges
them. A can replay when its bit is zero and stay quiet otherwise, and B can
read A's bit from the grant order.

This does not break existence. Choose trembles for A's replay that do not
depend on A's bit. B's beliefs after an off-path replay then stay at the source
beliefs, B ignores the signal, and A gains nothing by sending it. This is the
babbling equilibrium of cheap talk.

### What an adaptive order can and cannot read

The pending pool holds two kinds of content. A raw claim, such as an unwitnessed
opening, is unverified; an order policy that reacts only to such claims
transmits cheap talk, which beliefs can neutralize. A packet can also carry a
sound certificate, issued at emission rather than at inclusion
(`WitnessedSubmission.emit` in `Vegas/Pending/OpeningEvidence.lean`): a single
response can fix a fresh commitment and put its authentic opening into the
pool before any inclusion (`reactive_commitment_disclosure` in
`Vegas/Pending/ReactivePacketEvidence.lean`). A public order policy that reads
certificates in the pool can therefore reveal verified values through the grant
order, and trembles that ignore hidden values do not neutralize that.

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
    player's binding is ready but ungranted, an order policy reading its value
    would leak verified information on path, uncharged, and no assessment with
    the source law would be sequentially rational (probe C4). Concurrent mode
    rules this out: its dependency order is the compiled `barrierOrder`
    (`Vegas/EventGraph/Barriers.lean`), in which a public event, such as a
    resolution, depends on every earlier event and every later event depends
    on it. When an opening can be sent, every earlier binding has completed,
    and no later binding is ready until the resolution completes and the source
    publishes the value anyway. Only different players' bindings between
    consecutive public events are concurrent, and a pending commitment carries
    only a handle. The case matters only for a dependency policy that lets a
    public event overlap a binding.
- **Changes to opportunities.** In concurrent mode an order changes the
  relative order of different-owner bindings that are hidden from one another,
  and, through the deadline timers, whether each owner still has a timely
  opportunity (see the timeliness obligation below).

### The scheduler contract

A valid schedule for this purpose:

- reads only public data, as `EventGraphRuntime.ServiceOrderPolicy` already
  requires (under the barrier order this already excludes early verified
  values other than charged ones);
- grants only ready events;
- keeps the protected block at every grant: an activation of the event's owner,
  include-latest, the deadline, and expiry;
- gives every granted event's owner a timely opportunity: the owner's
  activation and the inclusion of its message precede the event's deadline,
  which is measured from when the event became ready, not from its grant;
- lets the audit record the actual grant history as each message's phase;
- has a bounded plan length, so the deposit and horizon remain finite.

A scheduler that starves an event, or runs without bound, is outside the claim.

## Target: the general theorem

The goal is the strongest statement, not the reuse of the existing proof. The
target is the barrier-ordered concurrent runtime under every order policy that
satisfies the contract above: every source sequential equilibrium has an
audited native sequential equilibrium with the source law. The fixed calendar,
a fixed permutation of concurrent bindings, and a public random order drawn up
front are special cases of an order policy, so they need no separate theorems.
The obligations are:

- **Timely opportunities.** A deadline timer starts when its event becomes
  ready (`State.refreshActivated` in `Vegas/Pending/EventApplication.lean`), not
  when it is granted. In the sequentialized graph an event becomes ready only
  after its predecessor completes, so its timer starts at its own block. In the
  concurrent graph several bindings are ready at once and their timers run
  together: with deadlines `event.val + 1` and blocks of `event.val + 1` ticks,
  three bindings ready at clock zero are granted at clocks 0, 1 and 3, and the
  third, with deadline 3, has already expired (probe C1). Either start timers
  at the grant, a runtime change that makes every contract-satisfying order
  timely, or state timeliness as a hypothesis on the order policy. The first
  gives the stronger theorem.
- **Enforced grants.** In the concurrent graph a packet for an event that is
  ready but not yet granted can be included out of calendar order, because
  grants are not inclusion authorization ([active tower](active-tower.md)).
  The handler must accept only packets for the granted event, or the theorem
  must cover the resulting inclusions.
- **Phase from the grant history.** Replace the rank-indexed calendar,
  `DecisionPhase.position` together with `rosterPlanPrefix` and
  `rosterPlanSuffix`, by a phase read from the public grant history. About 94
  files under `Vegas` refer to the roster plan. The one-shot principle and the
  Bayes transport no longer need the rank as a clock (see above); the
  replacement concerns the operational invariants.
- **Order-invariant continuations.** Prove that the compiled continuation law
  of the typed source readout is the same under every valid order policy, from
  any reachable public history. The pending-message laws prove this from the
  start of play; the general theorem needs it from arbitrary reachable states.
- **Proportional belief transport.** At information sets created by order
  choices, build beliefs from trembles that do not depend on hidden values, so
  that observers keep their source beliefs. The library's
  `bayesBelief_projection_of_reach` needs exact fiber sums, including equal
  information-set masses. Along a tremble sequence the sums are only
  proportional: in probe C2 a source history of Bob has weight 1/2 while the
  corresponding signal history has weight ε/4. Bayes beliefs are ratios, so
  they transport whenever the fiber sums are a fixed positive finite multiple
  of the target weights (`bayesBelief_projection_of_proportional_reach`, see
  above). This lemma strictly generalizes the exact version and needs no
  common depth.
- **Retained-site depth.** Resolved in the library, pending retargeting. An
  adaptive order breaks common decision depths without changing any player's
  information. For example, a scheduler that inserts zero or one wait before
  the same grant satisfies the contract above, yet the two histories reach the
  same information at different depths, because a wait updates only the
  environment's recall (probe C5 shows this is no obstruction to
  equilibrium). The depth-free extension
  (`ActionRestriction.sequentialEquilibrium_extends_of_continuation_unclocked`)
  needs no such depth. The contract therefore does not have to make scheduler
  steps public. What remains is to retarget the Vegas extensions onto it.

Adaptive rosters, whose activations respond to traffic, fall under the same
theorem once their activations are part of the order policy.

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
  directly. A gated concurrent runtime with adjusted timers is a different
  protocol: its activation metadata, menus and audit observations differ, so
  reusing the theorem there needs an equivalence of the complete native
  protocols and information models. Equality of terminal store laws, as in
  `Vegas/EventGraph/Commutation.lean` and
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
| C1 | Three concurrent bindings, deadline `event.val + 1`, blocks of `event.val + 1` ticks | Timers from readiness expire the third binding; timers from the grant do not. |
| C2 | Order reacts to an unverified pool signal | An equilibrium with the source law exists (babbling). |
| C3 | Order reads a certificate on a forbidden commitment | An equilibrium with the source law exists exactly when the expected charge is at least the gain from revealing (here 1/2). |
| C4 | Order reads a permitted opening while the other binding is ungranted (excluded by the barrier order) | No assessment with the source law is sequentially rational; an order blind to opening contents restores one. |
| C5 | An unobserved wait before the other player's grant | The translated profile is an equilibrium although its information set spans two depths: the depth requirement is a proof requirement, not an obstruction. |

Under the barrier order, C4 cannot arise, so the probes support preservation
under the contract above once deadline timers start at the grant (or deadlines
cover the grant offset). They are design evidence, not proofs.

## Suggested order of work

1. **Finite probes**: done, above.
2. **Library lemmas**: done. The proportional-reach Bayes transport and the
   depth-free restriction extension are in `GameTheoryExtensions`. The
   contract need not make scheduler steps public.
3. **Timers at the grant** in the runtime.
4. **Phase from the grant history and order-invariant continuations.**
5. **The general theorem**, with the fixed calendar recovered as an instance.
