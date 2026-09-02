/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Protocol.Execution
import GameTheory.Protocol.Information

/-!
# Adversarially scheduled protocols

A protocol in which players submit actions to a shared state machine and a
*scheduler* decides the order those submissions are applied in.  A blockchain is
one instance — the sequencer orders a block's transactions — but nothing here is
blockchain-specific: the underlying state machine is a parameter, so this covers
asynchronous public protocols generally.

The module depends only on `GameTheory`, so it can be lifted into that library
once the interface has been exercised by a real client.

## The scheduler is a player

Not a parameter.  A scheduler passed as a parameter sits in the protocol's
*type*, so two schedulers give two protocols, their histories and information
states live in different families, and every comparison between them drags a
transport across an equality that holds only propositionally.  As a coordinate
of the profile — agent `none` — two schedules are two profiles in one game, and
comparing them is ordinary game theory.

It is also the more honest reading.  A sequencer is a strategic participant with
its own options, not a fixed function; treating it as a player is what lets a
result quantify over adversarial scheduling rather than assume one schedule.

## The one design decision that matters

`State` records the realized order in a `log`.  On a public runtime the order in
which transactions landed *is* observable, so a model that quotients it away
understates what a strategy may condition on, and any preservation theorem
proved against such a model describes a system nobody runs.

`step_ne_of_order_ne` is what carrying it costs and buys: **confluence of
effects is not invisibility of order.**  Even where every pair of submissions
commutes, so the underlying state law is schedule-invariant, two schedules still
produce distinguishable protocol states.

## Deviation classes, not two games

`GameTheory` makes policy locality structural: a policy is a function of an
information state, so a policy reading something absent from that state cannot
be written.  The honest and robust readings are therefore two classes of policy
inside the one faithful game — `OrderOblivious` and everything — which is the
shape `DeviationAdequacyOn` consumes.  `blindSignals` is kept as the documented
idealization that resolves a round atomically, and
`blind_infoOf_eq_forgetOrders` measures exactly what it drops.

## Two disciplines, and when each is needed

An order-aware deviation can be answered in two ways, because equilibrium asks
of an available deviation only that it not improve on the equilibrium payoff.
Make it unavailable, or let it be available and show it gains nothing.

`EnforcesOrder` takes the first route: the runtime accepts one order per view,
so the scheduler has nothing to choose and `step_eq_of_enforcesOrder` makes it
strategically inert.  It costs the round's parallelism, and an enforced order
means a stalled participant blocks the protocol.

`EffectsCommute` takes the second: every accepted order has the same effect, so
`step_base_eq_of_effectsCommute` makes the scheduler irrelevant to the
underlying state while leaving it its choice.  This is the cheaper answer and
the common case, and `counterSystem` shows it is not degenerate — the state
genuinely moves, and commutation is a fact about addition.

The two are ordered, not alternative: `effectsCommute_of_enforcesOrder`.  But
they leave different things observable, and the gap is the point.  Enforcement
determines the *log*, so nothing separates two schedules.  Commutation
determines only the *base* state; the log still differs, so a payoff reading the
log still sees a difference.  Payoff-irrelevance is commutation *plus* a
schedule-blind game — a condition on the game, not on the runtime.

Neither is a default, and the choice is not this module's to make.  `schedules`
is a field, so an artifact is permissive or enforcing by construction and both
properties appear only as hypotheses.  A developer wanting no order-sensitive
guarantee keeps the parallelism; one who wants it pays for exactly it.  The
obligation is to find, per property, the weakest discipline that supports it.

`raceSystem` marks where the permissive tier ends: doubling and adding do not
commute, so `EffectsCommute` fails and a preservation claim there has to buy
enforcement.  Two pending operations whose order changes the result is the shape
a public runtime actually has, which is why enforcement stays available rather
than being argued away.

## What is observable, and what is assumed

Two different things are visible on a public runtime, and only one is modelled
here.  They are different epistemic objects, not different resolutions.

*Settled order.*  Once a round has been applied, the order it was applied in is
on the chain.  Everyone reads it, everyone reads that everyone reads it, and so
on: it is **common knowledge**, which is what a public signal means in this
vocabulary.  `log` records it and `revealingSignals` publishes it.

*In-flight submissions.*  Before a round is applied, pending submissions may be
visible to some observers.  This is **not** common knowledge.  A player seeing a
pending submission does not know who else saw it, nor that others know they saw
it.  Publishing it as a public signal would be *wrong* rather than coarse.

**This module assumes no participant observes a submission before it is
applied** — the scheduler included, which is conservative for the players and
restrictive for the adversary.  Front-running is outside the model.  Relaxing
the assumption is not a matter of publishing more signals: it needs an
information structure able to express mutual-but-not-common knowledge, which
`InfoSignals` does not directly provide.  It is stated because a reader taking
`revealingSignals` for "everything a chain reveals" would credit the model with
more faithfulness than it has.
-/

noncomputable section

namespace Vegas

open GameTheory.Protocol
open GameTheory.Math.Probability

universe u

variable {ι : Type u}

/-- A state machine whose round is resolved by applying each submitted action in
turn.  Ordering is a real degree of freedom exactly when `applyOne` calls fail
to commute. -/
structure ScheduledSystem (ι : Type u) where
  /-- The underlying state, before any scheduling record is attached. -/
  Base : Type u
  /-- Each player's action carrier. -/
  Action : ι → Type u
  /-- The initial underlying state. -/
  init : Base
  /-- Who must submit. -/
  active : Base → ι → Prop
  /-- What an active player may submit. -/
  available : (state : Base) → (i : ι) → Set (Action i)
  /-- Where execution stops. -/
  terminal : Base → Prop
  /-- Apply one player's submission. -/
  applyOne : (state : Base) → (i : ι) → Action i → FinDist Base
  /-- What everyone publicly sees of the underlying state. -/
  View : Type u
  /-- The public view of a state. -/
  view : Base → View
  /-- The options publicly visible at a view. -/
  menuAt : View → (i : ι) → Set (Option (Action i))
  /-- Legality is publicly determined: the visible menu is the real one.  On a
  contract this is automatic, since which entry points are enabled is a function
  of public storage.

  Split into the two cases rather than stated with a `match`, so the interface
  carries no matcher for a client's unifier to get stuck on. -/
  menuAt_some : ∀ (state : Base) (i : ι) (action : Action i),
    some action ∈ menuAt (view state) i ↔
      (active state i ∧ action ∈ available state i)
  /-- Abstaining is visibly allowed exactly when the player is not active. -/
  menuAt_none : ∀ (state : Base) (i : ι),
    (none : Option (Action i)) ∈ menuAt (view state) i ↔ ¬ active state i
  /-- Which orders the runtime will accept at a view.

  A permissive runtime accepts every order and leaves the scheduler a real
  choice.  An order-enforcing one accepts exactly one, and then the scheduler
  has no choice to make — see `EnforcesOrder`.  Indexed by the view rather than
  the state, because what the runtime accepts must be publicly determined for
  the scheduler's menu to be information-local. -/
  schedules : View → Set (List ι)
  /-- Some order is always acceptable, so a round can always be resolved. -/
  schedules_nonempty : ∀ v, (schedules v).Nonempty
  /-- Every non-terminal state admits a legal joint submission. -/
  progress : ∀ state, ¬ terminal state →
    ∃ joint, IsLegalJoint (active state) (available state) joint

namespace ScheduledSystem

variable (sys : ScheduledSystem.{u} ι)

/-- The order a round's submissions were applied in. -/
abbrev Order (_sys : ScheduledSystem.{u} ι) : Type u := List ι

/-- Participants: the submitting players, and the scheduler as `none`. -/
abbrev Agent (_sys : ScheduledSystem.{u} ι) : Type u := Option ι

/-- A protocol state: the underlying state together with the public record of
the orders actually realized, most recent first. -/
structure State (sys : ScheduledSystem.{u} ι) where
  /-- The underlying state machine's state. -/
  base : sys.Base
  /-- Realized orders, most recent first.  Publicly observable. -/
  log : List sys.Order

/-- What each participant may submit: an order for the scheduler, an action for
a player. -/
abbrev AgentAction (sys : ScheduledSystem.{u} ι) : sys.Agent → Type u
  | none => sys.Order
  | some i => sys.Action i

/-- Apply the submitted actions along a given order, skipping players who did
not submit. -/
noncomputable def applyOrder (sys : ScheduledSystem.{u} ι)
    (joint : ∀ a, Option (sys.AgentAction a)) :
    sys.Order → sys.Base → FinDist sys.Base
  | [], state => FinDist.pure state
  | i :: rest, state =>
      match joint (some i) with
      | none => applyOrder sys joint rest state
      | some action =>
          (sys.applyOne state i action).bind (applyOrder sys joint rest)

/-- The order a joint submission schedules. -/
def scheduledOrder (joint : ∀ a, Option (sys.AgentAction a)) : sys.Order :=
  (joint none).getD []

/-- Who is active: every player the state says must submit, and the scheduler,
always — a round is always ordered by someone. -/
def agentActive (state : sys.State) : sys.Agent → Prop
  | none => True
  | some i => sys.active state.base i

/-- What each participant may submit at a state. -/
def agentAvailable (state : sys.State) : (a : sys.Agent) → Set (sys.AgentAction a)
  | none => sys.schedules (sys.view state.base)
  | some i => sys.available state.base i

/-- The publicly visible menu for each participant.  The scheduler must order
the round, so abstaining is not on its menu. -/
def agentMenuAt (v : sys.View) : (a : sys.Agent) → Set (Option (sys.AgentAction a))
  | none => {choice | ∃ order ∈ sys.schedules v, choice = some order}
  | some i => sys.menuAt v i

/-- Extend a players-only joint submission with an order for the scheduler.
A named definition rather than an inline match, so it reduces on `some i`. -/
def withSchedule (order : sys.Order) (joint : ∀ i, Option (sys.Action i)) :
    ∀ a : sys.Agent, Option (sys.AgentAction a)
  | none => some order
  | some i => joint i

/-- The execution protocol.  There is exactly one: the scheduler is a coordinate
of the joint action, not a parameter of the protocol. -/
@[reducible] noncomputable def toExecutionProtocol : ExecutionProtocol sys.Agent where
  State := sys.State
  Action := sys.AgentAction
  init := { base := sys.init, log := [] }
  active := sys.agentActive
  available := sys.agentAvailable
  terminal state := sys.terminal state.base
  step state legal :=
    (sys.applyOrder legal.1 (sys.scheduledOrder legal.1) state.base).map
      fun next =>
        { base := next, log := sys.scheduledOrder legal.1 :: state.log }
  progress state hterminal := by
    obtain ⟨joint, hjoint⟩ := sys.progress state.base hterminal
    obtain ⟨order, horder⟩ := sys.schedules_nonempty (sys.view state.base)
    refine ⟨sys.withSchedule order joint, ?_⟩
    intro a
    cases a with
    | none => exact ⟨trivial, horder⟩
    | some i =>
        -- Case on the submission so both matchers reduce: the two sides are
        -- defeq but their matcher instances are generated at different types.
        have h := hjoint i
        simp only [withSchedule, agentActive, agentAvailable]
        cases hj : joint i with
        | none => rw [hj] at h; exact h
        | some action => rw [hj] at h; exact h

@[simp] theorem toExecutionProtocol_terminal (state : sys.State) :
    sys.toExecutionProtocol.terminal state = sys.terminal state.base := rfl

/-- Every successor of a step records exactly the order that was scheduled. -/
theorem log_of_mem_support_step
    {state : sys.State}
    {legal : { joint // sys.toExecutionProtocol.Legal state joint }}
    {next : sys.State}
    (hnext : next ∈ (sys.toExecutionProtocol.step state legal).support) :
    next.log = sys.scheduledOrder legal.1 :: state.log := by
  simp only [toExecutionProtocol, FinDist.support_map] at hnext
  obtain ⟨_base, _hbase, hnext⟩ := hnext
  rw [← hnext]

/-- **Confluence of effects is not invisibility of order.**

Two joint submissions that schedule different orders induce different successor
laws — whatever the state machine does, and in particular even when the two
orders have identical effects.

A schedule-invariance result about the underlying machine constrains what the
machine computes; it says nothing about what a participant observes.  Only a
statement about the protocol state does. -/
theorem step_ne_of_order_ne
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (horder : sys.scheduledOrder left.1 ≠ sys.scheduledOrder right.1) :
    sys.toExecutionProtocol.step state left ≠
      sys.toExecutionProtocol.step state right := by
  intro heq
  obtain ⟨next, hnext⟩ := (sys.toExecutionProtocol.step state left).support_nonempty
  have hleft : next.log = sys.scheduledOrder left.1 :: state.log :=
    sys.log_of_mem_support_step hnext
  have hnextRight : next ∈ (sys.toExecutionProtocol.step state right).support := by
    rw [← heq]; exact hnext
  have hright : next.log = sys.scheduledOrder right.1 :: state.log :=
    sys.log_of_mem_support_step hnextRight
  exact horder (List.cons.inj (hleft.symm.trans hright)).1

/-! ## Enforcing the schedule

Restricting attention to order-oblivious *play* is not enough to make the
scheduler harmless.  Equilibrium quantifies over the deviations a participant
*has available*, so a class of well-behaved policies cannot be imposed by fiat:
if an order-aware deviation exists, an equilibrium claim has to face it.  Such a
restriction describes a profile, not an equilibrium.

What does work is removing the freedom.  A runtime that accepts exactly one
order at each view leaves the scheduler nothing to choose, so the schedule is a
function of the history, carries no information, and the scheduler's payoff —
which is nowhere in the source program, and which nothing about the source lets
us infer — cannot matter.  That is a property of the emitted artifact, so a
compiler can establish it rather than assume it.

Enforcement is a dial, not a default.  `schedules` is a field of the system, so
a compiled artifact is permissive or enforcing by construction, and
`EnforcesOrder` appears only as a *hypothesis* on the results that need it.  A
developer who wants no order-sensitive guarantee pays nothing: the permissive
runtime keeps its parallelism, and the theorems below simply do not apply to it.
A developer who does want one pays for exactly that.  The obligation on this
development is therefore to identify, for each property worth preserving, the
weakest discipline that supports it — not to enforce everywhere.

The price is real and is not modelled here: serializing a round costs
throughput, and enforcing an order means a stalled participant blocks the
protocol, which is why an enforcing runtime needs timeouts.

`EnforcesOrder` does not make the protocol schedule-free.  Timing remains
public — block height, elapsed time, who was slow — and that is a separate
signal this development does not model at all.  Enforcement removes *order* as a
channel, not every channel. -/

/-- The runtime accepts at most one order at each view, so the scheduler has no
choice to make. -/
def EnforcesOrder (sys : ScheduledSystem.{u} ι) : Prop :=
  ∀ v : sys.View, (sys.schedules v).Subsingleton

/-- Applying a round reads the joint submission only through the players'
components, never the scheduler's. -/
theorem applyOrder_congr {left right : ∀ a, Option (sys.AgentAction a)}
    (hplayers : ∀ i, left (some i) = right (some i)) :
    ∀ (order : sys.Order) (state : sys.Base),
      sys.applyOrder left order state = sys.applyOrder right order state
  | [], _ => rfl
  | i :: rest, state => by
      simp only [applyOrder, hplayers i]
      cases hr : right (some i) with
      | none =>
          simp only
          exact applyOrder_congr hplayers rest state
      | some action =>
          simp only
          exact congrArg _ (funext fun next => applyOrder_congr hplayers rest next)

/-- Under an enforcing runtime every legal joint at a state schedules the same
order: the scheduler's component is determined. -/
theorem scheduledOrder_eq_of_enforcesOrder (henforce : sys.EnforcesOrder)
    {state : sys.State}
    (left right : { joint // sys.toExecutionProtocol.Legal state joint }) :
    sys.scheduledOrder left.1 = sys.scheduledOrder right.1 := by
  have hleft := left.2.2 none
  have hright := right.2.2 none
  unfold scheduledOrder
  cases hl : left.1 none with
  | none => rw [hl] at hleft; exact absurd trivial hleft
  | some orderLeft =>
      cases hr : right.1 none with
      | none => rw [hr] at hright; exact absurd trivial hright
      | some orderRight =>
          rw [hl] at hleft
          rw [hr] at hright
          simp only [Option.getD_some]
          exact henforce (sys.view state.base) hleft.2 hright.2

/-- **An enforcing runtime makes the scheduler strategically inert.**

Two legal joints agreeing on every player's submission induce the same successor
law, whatever the scheduler submitted.  So the scheduler cannot influence the
outcome at all, and its incentives — absent from the source program and not
inferable from it — are irrelevant rather than merely assumed away.

This is what restricting to order-oblivious play could not deliver.  That
restriction constrains behaviour and equilibrium quantifies over availability;
this removes the availability. -/
theorem step_eq_of_enforcesOrder (henforce : sys.EnforcesOrder)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (hplayers : ∀ i, left.1 (some i) = right.1 (some i)) :
    sys.toExecutionProtocol.step state left =
      sys.toExecutionProtocol.step state right := by
  have horder := sys.scheduledOrder_eq_of_enforcesOrder henforce left right
  simp only [toExecutionProtocol, horder]
  rw [sys.applyOrder_congr hplayers]

/-! ## Order that is available but useless

Enforcement is the heavy instrument, and it is not the only one.  A deviation
that exists but never pays is no threat to an equilibrium claim: the quantifier
ranges over available deviations, but what it *asks* of each is only that it not
improve on the equilibrium payoff.  So there are two ways to answer an
order-aware deviation — make it unavailable, or let it be available and show it
gains nothing.

The second is cheaper and covers the common case.  Leave the scheduler its
choice, and arrange that the choice cannot move anything a payoff can see.
Order-aware deviations remain expressible — `coinOrderAware` is one — and the
runtime keeps its parallelism.

`EnforcesOrder` removes the scheduler's choice; `EffectsCommute` leaves the
choice and removes its consequences.  They differ in what stays observable, and
the difference is not cosmetic.  Enforcement determines the *log*, so no
observation whatsoever separates two schedules.  Commutation determines only the
*base* state: the log still differs, so a payoff that reads the log still sees a
difference.  Payoff-irrelevance is commutation *plus* a utility blind to the
schedule, and that second half is a condition on the game, not on the runtime.

Neither discipline handles a scheduler that reacts to what it is ordering.  Both
quantify over a fixed joint submission, which is exactly the model's claim that
the scheduler commits to an order without seeing the round's submissions.  A
runtime where the order may depend on the submissions is a different system, and
front-running is what that difference is called. -/

/-- Every order the runtime accepts has the same effect on the underlying state.

Strictly weaker than `EnforcesOrder`, which collapses the accepted orders to one:
here the scheduler still chooses, its choice still enters the log, and the choice
is still observable.  What it cannot do is move the underlying state. -/
def EffectsCommute (sys : ScheduledSystem.{u} ι) : Prop :=
  ∀ (joint : ∀ a, Option (sys.AgentAction a)) (state : sys.Base)
      {left right : sys.Order},
    left ∈ sys.schedules (sys.view state) →
      right ∈ sys.schedules (sys.view state) →
        sys.applyOrder joint left state = sys.applyOrder joint right state

/-- Forgetting the log of a round's successor leaves exactly the effect of
applying the scheduled order. -/
theorem step_map_base {state : sys.State}
    (joint : { joint // sys.toExecutionProtocol.Legal state joint }) :
    (sys.toExecutionProtocol.step state joint).map State.base =
      sys.applyOrder joint.1 (sys.scheduledOrder joint.1) state.base := by
  simp only [toExecutionProtocol, FinDist.map_comp, Function.comp_def]
  exact FinDist.map_id _

/-- A legal joint's scheduled order is one the runtime accepts. -/
theorem scheduledOrder_mem_schedules {state : sys.State}
    (joint : { joint // sys.toExecutionProtocol.Legal state joint }) :
    sys.scheduledOrder joint.1 ∈ sys.schedules (sys.view state.base) := by
  have hlegal := joint.2.2 none
  unfold scheduledOrder
  cases hjoint : joint.1 none with
  | none => rw [hjoint] at hlegal; exact absurd trivial hlegal
  | some order => rw [hjoint] at hlegal; exact hlegal.2

/-- **Commuting effects make the scheduler irrelevant to the underlying state.**

Two legal joint submissions agreeing on every player's submission reach the same
law over underlying states, whatever the scheduler submitted.  The scheduler
keeps its choice and that choice stays visible in the log; what it has lost is
any influence on the state.

This is the permissive runtime's counterpart to `step_eq_of_enforcesOrder`, and
it is what lets such a runtime keep its parallelism and still support a
preservation claim.  Order-aware deviations remain expressible, but a payoff
reading only the underlying state cannot tell them apart from order-oblivious
ones, so the extra strategies buy nothing and there is nothing to back-translate.
Enforcement buys strictly more — equality of the whole successor law, log
included — at the cost of serializing the round. -/
theorem step_base_eq_of_effectsCommute (hcommute : sys.EffectsCommute)
    {state : sys.State}
    {left right : { joint // sys.toExecutionProtocol.Legal state joint }}
    (hplayers : ∀ i, left.1 (some i) = right.1 (some i)) :
    (sys.toExecutionProtocol.step state left).map State.base =
      (sys.toExecutionProtocol.step state right).map State.base := by
  rw [sys.step_map_base left, sys.step_map_base right, sys.applyOrder_congr hplayers]
  exact hcommute right.1 state.base
    (sys.scheduledOrder_mem_schedules left) (sys.scheduledOrder_mem_schedules right)

/-- Enforcement implies commutation: with one acceptable order there is nothing
for two orders to disagree about.  So the results below `EffectsCommute` are
available to an enforcing runtime too, and the two disciplines are ordered
rather than alternative. -/
theorem effectsCommute_of_enforcesOrder (henforce : sys.EnforcesOrder) :
    sys.EffectsCommute := by
  intro joint state left right hleft hright
  rw [henforce (sys.view state) hleft hright]

/-! ## Two information models over one protocol -/

/-- What an order-revealing participant knows: the current public view, and the
history of realized orders paired with the view each followed. -/
abbrev RevealingInfo (sys : ScheduledSystem.{u} ι) : Type u :=
  sys.View × List (sys.Order × sys.View)

/-- What an order-blind participant knows: the current and earlier public views,
with no record of how rounds were ordered. -/
abbrev BlindInfo (sys : ScheduledSystem.{u} ι) : Type u :=
  sys.View × List sys.View

/-- Discard the schedule from an order-revealing information state. -/
def forgetOrders (info : sys.RevealingInfo) : sys.BlindInfo :=
  (info.1, info.2.map Prod.snd)

/-- Signals that publish the realized order alongside the public view: the
faithful model of a public runtime. -/
def revealingSignals : InfoSignals sys.toExecutionProtocol where
  PublicSignal := sys.View × sys.Order
  PrivateSignal _ := PUnit
  initialPublic := (sys.view sys.init, [])
  initialPrivate _ := PUnit.unit
  publicSignal event := (sys.view event.target.base, event.target.log.headD [])
  privateSignal _ _ := PUnit.unit
  InfoState _ := sys.RevealingInfo
  initInfo _ _ signal := (signal.1, [])
  pushInfo _ info _ _ signal := (signal.1, (signal.2, info.1) :: info.2)

/-- Signals that publish only the public view: the idealization in which a round
resolves atomically.  A perfectly good information model — just not one of a
public chain. -/
def blindSignals : InfoSignals sys.toExecutionProtocol where
  PublicSignal := sys.View
  PrivateSignal _ := PUnit
  initialPublic := sys.view sys.init
  initialPrivate _ := PUnit.unit
  publicSignal event := sys.view event.target.base
  privateSignal _ _ := PUnit.unit
  InfoState _ := sys.BlindInfo
  initInfo _ _ signal := (signal, [])
  pushInfo _ info _ _ signal := (signal, info.1 :: info.2)

/-- **Blindness is exactly discarding the schedule.**

After every history the order-blind information state is the order-forgetting
projection of the order-revealing one.  The two models are related by a
forgetful map and differ in nothing else. -/
theorem blind_infoOf_eq_forgetOrders (a : sys.Agent)
    {state : sys.toExecutionProtocol.State}
    (trace : ExecutionProtocol.Trace sys.toExecutionProtocol state) :
    sys.blindSignals.infoOf a trace =
      sys.forgetOrders (sys.revealingSignals.infoOf a trace) := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih =>
      -- rewrite with `ih` before unfolding the signal records: unfolding first
      -- replaces the head symbol `ih` matches on.
      rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend, ih]
      rfl

/-- The current view a participant holds is the view of the state the history
reached.  This is what makes the public menu information-local. -/
theorem revealing_infoOf_fst (a : sys.Agent)
    {state : sys.toExecutionProtocol.State}
    (trace : ExecutionProtocol.Trace sys.toExecutionProtocol state) :
    (sys.revealingSignals.infoOf a trace).1 = sys.view state.base := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized _ih =>
      rw [InfoSignals.infoOf_extend]
      rfl

/-- The same, order-blind. -/
theorem blind_infoOf_fst (a : sys.Agent)
    {state : sys.toExecutionProtocol.State}
    (trace : ExecutionProtocol.Trace sys.toExecutionProtocol state) :
    (sys.blindSignals.infoOf a trace).1 = sys.view state.base := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized _ih =>
      rw [InfoSignals.infoOf_extend]
      rfl

private theorem agentMenuAt_adequate (state : sys.State) (a : sys.Agent)
    (choice : Option (sys.AgentAction a)) :
    choice ∈ sys.agentMenuAt (sys.view state.base) a ↔
      LegalOption sys.toExecutionProtocol state a choice := by
  cases a with
  | none =>
      cases choice with
      | none =>
          constructor
          · rintro ⟨order, _, hcontra⟩; exact absurd hcontra.symm (Option.some_ne_none order)
          · intro hlegal; exact absurd trivial hlegal
      | some order =>
          constructor
          · rintro ⟨other, hother, hchoice⟩
            have hsame : order = other := Option.some.inj hchoice
            subst hsame
            exact ⟨trivial, hother⟩
          · rintro ⟨_, hmem⟩; exact ⟨order, hmem, rfl⟩
  | some i =>
      cases choice with
      | none => exact sys.menuAt_none state.base i
      | some action => exact sys.menuAt_some state.base i action

/-- The order-revealing information model: the faithful one. -/
def revealingInformation : InformationModel sys.toExecutionProtocol where
  toInfoSignals := sys.revealingSignals
  menu a info := sys.agentMenuAt info.1 a
  menu_adequate := by
    intro a state trace choice
    rw [sys.revealing_infoOf_fst a trace]
    exact sys.agentMenuAt_adequate state a choice

/-- The order-blind information model: the idealization.  Same menus — the
schedule never changes what is legal, only what is known. -/
def blindInformation : InformationModel sys.toExecutionProtocol where
  toInfoSignals := sys.blindSignals
  menu a info := sys.agentMenuAt info.1 a
  menu_adequate := by
    intro a state trace choice
    rw [sys.blind_infoOf_fst a trace]
    exact sys.agentMenuAt_adequate state a choice

/-! ## Order-oblivious deviations

The honest and robust readings are two classes of policy inside the one faithful
game.  A policy is *order-oblivious* when the schedule cannot change what it
does; that restricts what a participant reads, never what it can express. -/

/-- A policy is order-oblivious when it acts the same at any two information
states differing only in schedule.

Phrased on the action rather than the menu-certified choice, whose type depends
on the information state; the action's does not. -/
def OrderOblivious {a : sys.Agent}
    (policy : sys.revealingInformation.Policy a) : Prop :=
  ∀ left right : sys.RevealingInfo,
    sys.forgetOrders left = sys.forgetOrders right →
      (policy left).1 = (policy right).1

/-- Read an order-blind policy as an order-revealing one by discarding the
schedule first.

This typechecks without transport because `forgetOrders` preserves the current
view and both menus are `agentMenuAt` of that view, so the two `Choice` types
are definitionally equal. -/
def liftPolicy {a : sys.Agent} (policy : sys.blindInformation.Policy a) :
    sys.revealingInformation.Policy a :=
  fun info => policy (sys.forgetOrders info)

/-- Everything an order-blind participant could have played is order-oblivious,
so the honest class is not an artificial restriction: it contains the image of
every schedule-free policy. -/
theorem liftPolicy_orderOblivious {a : sys.Agent}
    (policy : sys.blindInformation.Policy a) :
    sys.OrderOblivious (sys.liftPolicy policy) := by
  intro left right hforget
  change (policy (sys.forgetOrders left)).1 = (policy (sys.forgetOrders right)).1
  rw [hforget]

end ScheduledSystem

/-! ## Witnesses

Both facts below would be worthless if their hypotheses could not be met, so
they are met in the most extreme case available: a system whose actions are the
*identity*, so every pair of submissions commutes and the underlying state law
is literally constant.  Schedules remain distinguishable, and an order-aware
policy remains expressible.  Nothing weaker than recording the order could see
either, which is the argument for recording it. -/

/-- Two players, a binary submission each, and a state nothing changes.
Maximally confluent: every action is the identity. -/
def coinSystem : ScheduledSystem.{0} (Fin 2) where
  Base := Unit
  Action _ := Bool
  init := ()
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  applyOne state _ _ := FinDist.pure state
  View := Unit
  view _ := ()
  menuAt _ _ := {some true, some false}
  menuAt_some _ _ action := by cases action <;> simp
  menuAt_none _ _ := by simp
  schedules _ := Set.univ
  schedules_nonempty _ := ⟨[], Set.mem_univ _⟩
  progress _ _ := ⟨fun _ => some true, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

/-- A round in which both players submit and the scheduler picks `order`. -/
def coinRound (order : coinSystem.Order) (state : coinSystem.State) :
    { joint // coinSystem.toExecutionProtocol.Legal state joint } :=
  ⟨fun a =>
      match a with
      | none => some order
      | some _ => some true,
    not_false, by
      intro a
      cases a with
      | none => exact ⟨trivial, Set.mem_univ _⟩
      | some i => exact ⟨trivial, Set.mem_univ _⟩⟩

@[simp] theorem coinRound_scheduledOrder (order : coinSystem.Order)
    (state : coinSystem.State) :
    coinSystem.scheduledOrder (coinRound order state).1 = order := rfl

/-- **The separation is realized.**  Two schedules over a system in which every
action is the identity — so the underlying state law is the same constant either
way — nevertheless induce different successor laws, because the realized order
is part of what a participant observes. -/
theorem coin_step_ne (state : coinSystem.State) :
    coinSystem.toExecutionProtocol.step state (coinRound [0, 1] state) ≠
      coinSystem.toExecutionProtocol.step state (coinRound [1, 0] state) := by
  refine coinSystem.step_ne_of_order_ne ?_
  simp only [coinRound_scheduledOrder]
  intro horder
  exact absurd (List.cons.inj horder).1 (by decide)

@[simp] theorem coin_menu (i : Fin 2)
    (info : coinSystem.revealingInformation.InfoState (some i)) :
    coinSystem.revealingInformation.menu (some i) info =
      {some true, some false} := rfl

/-- A history in which player `0` was ordered first. -/
def coinFirstZero : coinSystem.RevealingInfo := ((), [([0, 1], ())])

/-- The same history except that player `1` was ordered first.  The two agree on
every public view and differ only in schedule. -/
def coinFirstOne : coinSystem.RevealingInfo := ((), [([1, 0], ())])

theorem coinFirst_forgetOrders_eq :
    coinSystem.forgetOrders coinFirstZero =
      coinSystem.forgetOrders coinFirstOne := rfl

/-- An order-aware policy: submit `true` exactly when player `0` was ordered
first.  Nothing about the state differs between those histories. -/
def coinOrderAware (i : Fin 2) :
    coinSystem.revealingInformation.Policy (some i) :=
  fun info =>
    if (info.2.headD ([], ())).1 = [0, 1] then
      ⟨some true, Set.mem_insert _ _⟩
    else
      ⟨some false, Set.mem_insert_of_mem _ rfl⟩

/-- **The order-oblivious class is proper.**

`coinOrderAware` acts differently at two histories that agree on every public
view and differ only in how a round was ordered, so it is not order-oblivious —
and by `liftPolicy_orderOblivious` no schedule-free policy induces it.

This is the obstruction to back-translation: an order-aware deviation has in
general no source counterpart, so adequacy against the unrestricted class does
not follow from adequacy against the order-oblivious one. -/
theorem coinOrderAware_not_orderOblivious (i : Fin 2) :
    ¬ coinSystem.OrderOblivious (coinOrderAware i) := by
  intro hoblivious
  have hcongr := hoblivious coinFirstZero coinFirstOne coinFirst_forgetOrders_eq
  simp only [coinFirstZero, Fin.isValue, coinOrderAware,
    List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, ↓reduceIte,
    coinFirstOne, List.cons.injEq, one_ne_zero, zero_ne_one, and_true,
    and_self] at hcongr
  exact Bool.noConfusion (Option.some.inj hcongr)

/-! ## A runtime that is permissive and still safe

`coinSystem` shows the separation exists but is a weak witness for commutation:
every action is the identity, so of course order does not matter.  The system
below is the honest case.  Two players each add to a running total, the runtime
accepts either order, and the total genuinely changes — yet addition commutes,
so the reachable state does not depend on who went first.

This is the configuration the permissive tier is for.  Order-aware deviations
exist and are expressible; the scheduler really does choose; and none of it can
move the total.  `counter_step_ne` and `counter_step_base_eq` are the two halves
of the point, and they are deliberately stated about the very same pair of
rounds: the successor laws differ, because the log records the order, while the
laws over *totals* coincide.  A payoff reading the total is untouched; a payoff
reading the log is not.  That is why payoff-irrelevance needs the game to be
schedule-blind and cannot be read off the runtime alone. -/

/-- Two players who each add a number to a running total, with the runtime free
to order them either way.  Reducible so that `Base`, `View` and `Action` line up
with `Nat` at instance transparency, which numerals need. -/
@[reducible] def counterSystem : ScheduledSystem.{0} (Fin 2) where
  Base := Nat
  Action _ := Nat
  init := 0
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  applyOne state _ amount := FinDist.pure (state + amount)
  View := Nat
  view state := state
  menuAt _ _ := {choice | choice ≠ none}
  menuAt_some _ _ action := by
    constructor
    · intro _; exact ⟨trivial, Set.mem_univ _⟩
    · intro _; exact Option.some_ne_none action
  menuAt_none _ _ := by
    constructor
    · intro hmem; exact absurd rfl hmem
    · intro hcontra; exact absurd trivial hcontra
  schedules _ := {[0, 1], [1, 0]}
  schedules_nonempty _ := ⟨[0, 1], Set.mem_insert _ _⟩
  progress _ _ := ⟨fun _ => some 0, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

/-- **The permissive runtime is genuinely permissive.**  Both orders are
accepted, so the scheduler has a real choice to make and `EnforcesOrder` fails.
Every result below therefore holds without enforcement. -/
theorem counter_not_enforcesOrder : ¬ counterSystem.EnforcesOrder := by
  intro henforce
  have hcontra := henforce 0 (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)
  exact absurd (List.cons.inj hcontra).1 (by decide)

/-- Resolving a round one player at a time, with the effect on the total made
explicit.  Stated separately because `applyOne` returning a point mass is what
collapses the bind. -/
private theorem counter_applyOrder_cons (joint) (i : Fin 2) (rest total) :
    counterSystem.applyOrder joint (i :: rest) total =
      match joint (some i) with
      | none => counterSystem.applyOrder joint rest total
      | some amount => counterSystem.applyOrder joint rest (total + amount) := by
  cases hjoint : joint (some i) with
  | none => simp only [ScheduledSystem.applyOrder, hjoint]
  | some amount =>
      simp only [ScheduledSystem.applyOrder, hjoint]
      exact FinDist.pure_bind _ _

/-- **And it is nevertheless safe.**  Addition commutes, so both accepted orders
carry a state to the same law even though each player's action moves it. -/
theorem counter_effectsCommute : counterSystem.EffectsCommute := by
  intro joint state left right hleft hright
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hleft hright
  rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl <;>
    simp only [counter_applyOrder_cons] <;>
    cases joint (some 0) <;> cases joint (some 1) <;>
    simp only [ScheduledSystem.applyOrder] <;>
    first
      | rfl
      | exact congrArg FinDist.pure (by omega)

/-- A round in which both players add `1` and the scheduler picks `order`. -/
def counterRound (state : counterSystem.State) (order : counterSystem.Order)
    (horder : order ∈ counterSystem.schedules (counterSystem.view state.base)) :
    { joint // counterSystem.toExecutionProtocol.Legal state joint } :=
  ⟨fun a =>
      match a with
      | none => some order
      | some _ => some 1,
    not_false, by
      intro a
      cases a with
      | none => exact ⟨trivial, horder⟩
      | some i => exact ⟨trivial, Set.mem_univ _⟩⟩

@[simp] theorem counterRound_scheduledOrder (state order horder) :
    counterSystem.scheduledOrder (counterRound state order horder).1 = order := rfl

/-- The first-player-first round at `state`. -/
def counterZeroFirst (state : counterSystem.State) :
    { joint // counterSystem.toExecutionProtocol.Legal state joint } :=
  counterRound state [0, 1] (Set.mem_insert _ _)

/-- The same round, ordered the other way. -/
def counterOneFirst (state : counterSystem.State) :
    { joint // counterSystem.toExecutionProtocol.Legal state joint } :=
  counterRound state [1, 0] (Set.mem_insert_of_mem _ rfl)

/-- **The schedule remains observable.**  The two accepted orders induce
different successor laws, because the realized order is recorded. -/
theorem counter_step_ne (state : counterSystem.State) :
    counterSystem.toExecutionProtocol.step state (counterZeroFirst state) ≠
      counterSystem.toExecutionProtocol.step state (counterOneFirst state) := by
  refine counterSystem.step_ne_of_order_ne ?_
  simp only [counterZeroFirst, counterOneFirst, counterRound_scheduledOrder]
  intro horder
  exact absurd (List.cons.inj horder).1 (by decide)

/-- **And is nevertheless payoff-inert for a schedule-blind game.**  The very
same two rounds carry the running total to the same law.  A utility reading the
total cannot separate them; only one reading the log can. -/
theorem counter_step_base_eq (state : counterSystem.State) :
    (counterSystem.toExecutionProtocol.step state
        (counterZeroFirst state)).map ScheduledSystem.State.base =
      (counterSystem.toExecutionProtocol.step state
        (counterOneFirst state)).map ScheduledSystem.State.base :=
  counterSystem.step_base_eq_of_effectsCommute counter_effectsCommute fun _ => rfl

/-! ## Where the permissive tier runs out

`EffectsCommute` would be worthless as a hypothesis if it held of every system,
so here is one it fails for.  Two players act on a total, one doubling it and one
adding to it.  Doubling and adding do not commute, the two accepted orders reach
different totals, and no amount of care about what the *game* reads can repair
that — the disagreement is in the runtime.

This is the smallest form of the problem a public runtime actually has: two
pending operations whose order changes the result.  A system in this shape is
where `EnforcesOrder` has to be paid for, and it is the reason enforcement stays
available rather than being argued away. -/

private theorem finDist_pure_ne {α : Type} {a b : α} (hne : a ≠ b) :
    FinDist.pure a ≠ FinDist.pure b := by
  intro heq
  have hprob : (FinDist.pure a).prob a = (FinDist.pure b).prob a := by rw [heq]
  rw [FinDist.prob_pure_self, FinDist.prob_pure_of_ne hne] at hprob
  exact absurd hprob one_ne_zero

/-- Two players acting on a total: player `0` doubles it, player `1` adds one. -/
@[reducible] def raceSystem : ScheduledSystem.{0} (Fin 2) where
  Base := Nat
  Action _ := Unit
  init := 1
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  applyOne state i _ := FinDist.pure (if i = 0 then state * 2 else state + 1)
  View := Nat
  view state := state
  menuAt _ _ := {choice | choice ≠ none}
  menuAt_some _ _ action := by
    constructor
    · intro _; exact ⟨trivial, Set.mem_univ _⟩
    · intro _; exact Option.some_ne_none action
  menuAt_none _ _ := by
    constructor
    · intro hmem; exact absurd rfl hmem
    · intro hcontra; exact absurd trivial hcontra
  schedules _ := {[0, 1], [1, 0]}
  schedules_nonempty _ := ⟨[0, 1], Set.mem_insert _ _⟩
  progress _ _ := ⟨fun _ => some (), fun _ => ⟨trivial, Set.mem_univ _⟩⟩

/-- Both players act, and the scheduler proposes `order`. -/
private def raceJoint (order : raceSystem.Order) :
    (a : raceSystem.Agent) → Option (raceSystem.AgentAction a)
  | none => some order
  | some _ => some ()

/-- **`EffectsCommute` is a real restriction.**  Doubling then adding reaches
`11` from `5`; adding then doubling reaches `12`.  So the permissive tier does
not cover every runtime, and for a system in this shape a preservation claim
needs `EnforcesOrder` rather than an argument that order does not matter. -/
theorem race_not_effectsCommute : ¬ raceSystem.EffectsCommute := by
  intro hcommute
  have hcontra := hcommute (raceJoint [0, 1]) 5
    (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)
  have hleft : raceSystem.applyOrder (raceJoint [0, 1]) [0, 1] 5 = FinDist.pure 11 := by
    simp only [ScheduledSystem.applyOrder, raceJoint, FinDist.pure_bind]
    norm_num
  have hright : raceSystem.applyOrder (raceJoint [0, 1]) [1, 0] 5 = FinDist.pure 12 := by
    simp only [ScheduledSystem.applyOrder, raceJoint, FinDist.pure_bind]
    norm_num
  rw [hleft, hright] at hcontra
  exact absurd hcontra (finDist_pure_ne (by decide))

end Vegas
