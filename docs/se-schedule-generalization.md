# Generalizing the sequential-equilibrium schedule

## Status

This is a design note; nothing in it is checked in Lean. It describes which
scheduling restrictions `Vegas.Paper.source_audited_raw_sequential_equilibrium`
imposes, argues that preservation should survive their removal under a
contract on the scheduler, and proposes a proof in three steps. The first two
reduce to the existing theorem; the third, adaptive orders, needs a direct
generalization of the proof.

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
neutralized through beliefs.

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

The scheduler cannot inspect hidden meanings. Anything it reads from the
pending pool, including a raw opening, is unverified. Verified evidence appears
only when a message is included, and inclusion is public under the fixed
calendar as well. An order policy that reads the pool therefore transmits cheap
talk, which beliefs can neutralize.

Two effects cannot be neutralized through beliefs:

- **Hard evidence reaching a player before the source allows it**, such as an
  early opening. The audit and deposit already deter these messages.
- **Changes to opportunities.** In concurrent mode the only opportunity an order
  can change is the relative order of different-owner bindings that are hidden
  from one another. Step A below argues that this order does not affect the game.

### The scheduler contract

A valid schedule for this purpose:

- reads only public data, as `EventGraphRuntime.ServiceOrderPolicy` already
  requires;
- grants only ready events;
- keeps the protected block at every grant: an activation of the event's owner,
  include-latest, the deadline, and expiry;
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
  files under `Vegas` refer to the roster plan.
- **Order-invariant continuations.** Prove that the compiled continuation law
  of the typed source readout is the same under every valid order policy, from
  any reachable public history. The pending-message laws prove this from the
  start of play; Step C needs it from arbitrary reachable states.
- **Beliefs.** At information sets created by order choices, build beliefs
  from trembles that do not depend on hidden values, so that observers keep
  their source beliefs.

Adaptive rosters, whose activations respond to traffic, belong to Step C as
well.

## Suggested order of work

1. **A finite experiment first**, in the style of
   `scripts/experiments/coalescing.py`: enumerate small concurrent games with
   pool-reading order policies and check that a sequential equilibrium with the
   source law exists. It is cheap and would expose a genuine obstruction before
   any proof work.
2. **Step A.** It admits concurrent mode under a fixed calendar and reuses the
   entire existing proof.
3. **Step B.**
4. **Step C**, the substantial part.
