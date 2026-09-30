# Generalizing the sequential-equilibrium schedule

## Status

This is a design note; nothing in it is checked in Lean. It describes which
scheduling restrictions `Vegas.Paper.source_audited_raw_sequential_equilibrium`
imposes, argues that preservation should survive their removal under a
contract on the scheduler, and proposes a proof in three steps. The first two
reduce to the existing theorem; the third, adaptive orders, needs a direct
generalization of the proof.

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
  map whose reach weights sum over its fibers (`bayesBelief_projection_of_reach`),
  both in [BeliefTransport.lean](../GameTheory/GameTheory/Analysis/Protocol/BeliefTransport.lean);
- extension across an action restriction
  ([RestrictionExtension.lean](../GameTheory/GameTheory/Analysis/Protocol/RestrictionExtension.lean))
  needs common decision depths only at the retained sites.

In the full-language proof a common depth is still used in two places: the
fixed-depth Bayes projections of `Vegas/Game/SourceServiceBayes.lean` and
`Vegas/Game/RevealServiceRosterBayes.lean`, which the reach-weight transport
can replace, and the restriction extensions of
`Vegas/Game/SourceServiceRestrictionExtension.lean` and
`Vegas/Game/RevealServiceRosterAudit.lean`, which need it at retained sites.
Under the fixed calendar the rank supplies that depth; under an adaptive order
nothing yet does (Step C). The roster plan's remaining role is operational: it identifies the
granted event and phase at each history.

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
  opportunity (Step A).

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

## A proof in three steps

### Step A: any fixed linear extension

A linear extension of the barrier order only permutes different-owner bindings
between consecutive public events. Swapping two adjacent source commitments by
different owners leaves the information structure unchanged: neither player
observes the other's commitment, and each player's own history is the same.

Required results:

1. **Source interchange.** The source law and the source sequential
   equilibria are preserved by such a swap. This is the interchange
   transformation of extensive-form games. Sequential equilibrium is invariant
   under interchange, unlike coalescing (see Experiment 1 in
   [action boundaries](action-coalescing.md)).
2. **Runtime identification.** The concurrent graph executed along an order π
   is the sequentialized graph of the permuted program, up to renaming events.

The runtime identification needs π to be enforced. In the concurrent graph a
packet for an event that is ready but not yet granted can be included out of
calendar order, because grants are not inclusion authorization
([active tower](active-tower.md)). Either sequentialize along π, or have the
handler accept only packets for the granted event.

Enforcing the order is not enough. A deadline timer starts when its event
becomes ready (`State.refreshActivated` in `Vegas/Pending/EventApplication.lean`),
not when it is granted. In the sequentialized graph an event becomes ready only
after its predecessor completes, so its timer starts at its own block. In the
concurrent graph several bindings are ready at once and their timers run
together. With the current deadlines, `event.val + 1`, and blocks of
`event.val + 1` ticks, three bindings ready at clock zero are granted at clocks
0, 1 and 3; the third, with deadline 3, has already expired, so its honest
owner cannot bind and the source law is lost although no event is starved.
Step A therefore needs timely owner opportunities as an explicit requirement,
either by starting timers at the grant or by deadlines that cover the grant
offset; with inclusion gating alone the existing theorem does not apply
unchanged.

The existing theorem then applies to the permuted program without change. The
graph-level commutation results in `Vegas/EventGraph/Commutation.lean` and
`Vegas/EventGraph/PolicyCommutation.lean` supply the graph half of the
interchange argument.

### Step B: a public random order drawn up front

If the order is drawn once, at the start, and announced, the draw is a public
chance move at the root. Every information set refines its outcome, so an
assessment is a sequential equilibrium exactly when it is one on each branch.
Step A applies branch by branch. This needs one generic lemma about public
chance at the root.

### Step C: adaptive orders

Adaptive orders do not reduce to Steps A and B. An adaptive policy is a mixture
of contingent plans only if the drawn plan stays hidden from the players.
Hidden chance merges information sets across plans, so sequential equilibrium
no longer decomposes over them. An up-front token cannot replace incremental
scheduling for the same reason.

Step C therefore generalizes the existing proof:

- **Phase from the grant history.** Replace the rank-indexed calendar,
  `DecisionPhase.position` together with `rosterPlanPrefix` and
  `rosterPlanSuffix`, by a phase read from the public grant history. About 94
  files under `Vegas` refer to the roster plan. The one-shot principle and the
  Bayes transport no longer need the rank as a clock (see above); the
  replacement concerns the operational invariants.
- **Retained-site depth.** The extension across the audited restriction still
  requires every retained site to have a common decision depth
  (`ActionRestriction.sequentialEquilibrium_extends_of_continuation` in
  [RestrictionExtension.lean](../GameTheory/GameTheory/Analysis/Protocol/RestrictionExtension.lean)).
  An adaptive order breaks this without changing any player's information: a
  scheduler that inserts zero or one wait before the same grant satisfies the
  contract above, yet the two histories reach the same information at
  different depths, because a wait updates only the environment's recall. The
  grant history and the clock-free Bayes transport do not supply the depth.
  Step C therefore needs either a clock-free restriction extension, a separate
  library result to be added as a prerequisite, or a contract under which
  players' information determines decision depth, for example by making every
  scheduler step publicly observed.
- **Order-invariant continuations.** Prove that the compiled continuation law
  of the typed source readout is the same under every valid order policy, from
  any reachable public history. The pending-message laws prove this from the
  start of play; Step C needs it from arbitrary reachable states.
- **Beliefs.** At information sets created by order choices, build beliefs
  from trembles that do not depend on hidden values, so that observers keep
  their source beliefs. Transport them with the reach-weight Bayes projection,
  which does not require an information set's histories to share a depth, as
  they need not under an adaptive order.

Adaptive rosters, whose activations respond to traffic, belong to Step C as
well.

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
2. **Step A.** It admits concurrent mode under a fixed calendar and reuses the
   entire existing proof.
3. **Step B.**
4. **Clock-free beliefs.** Move the two fixed-depth Bayes projections of the
   current proof to the reach-weight transport. This is independent of the
   schedule and removes the remaining clock outside the restriction
   extensions.
5. **Step C**, the substantial part.
