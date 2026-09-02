/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Protocol.Execution
import GameTheory.Protocol.Information

/-!
# Adversarially scheduled protocols

A protocol in which players submit actions to a shared state machine and some
*scheduler* decides the order those submissions are applied in.  A blockchain is
one instance — the sequencer orders a block's transactions — but nothing here is
blockchain-specific: the underlying state machine is a parameter, so this covers
asynchronous public protocols generally.

The module depends only on `GameTheory`, so it can be lifted into that library
once the interface has been exercised by a real client.

## The one design decision that matters

`State` records the realized order in a `log`, and the induced
`ExecutionProtocol` carries that log.  On a public runtime the order in which
transactions landed *is* observable, so a model that quotients it away
understates what a strategy may condition on, and any preservation theorem
proved against such a model describes a system nobody runs.

`step_ne_of_order_ne` is what carrying it costs and buys: **confluence of
effects is not invisibility of order.**  Even where every pair of submissions
commutes, so the underlying state law is schedule-invariant, two schedulers
still produce distinguishable protocol states.

## Two information models, not a predicate on strategies

`GameTheory` makes policy locality structural: a policy is a function of an
information state, so a policy that reads something absent from that state
cannot be written at all.  Whether a player may condition on the schedule is
therefore settled entirely by whether the realized order reaches the information
state — which makes the two readings two `InfoSignals` over one protocol, not a
side condition on strategies.

`blindSignals` is the idealization that resolves a round atomically;
`revealingSignals` is the faithful model of a public runtime.
`blind_infoOf_eq_forgetOrders` shows blindness is *exactly* discarding the
schedule, and `signals_separate_of_log_ne` shows that is the only place they
differ.

The *theorems*, though, are stated over the faithful model alone.  Comparing two
games is the wrong shape: an order-blind game is not a subgame of the revealing
one, and relating them needs transport across information-state types that agree
only propositionally.  Restricting *deviations* within the one faithful game
says the same thing with none of that friction, and it is what
`DeviationAdequacyOn` consumes: `OrderOblivious` is the honest class,
`fun _ _ => True` the robust one.  The blind model stays as the documented
idealization, and the projection theorem is what says precisely what it drops.

## What is observable, and what is assumed

Two different things are visible on a public runtime, and only one is modelled
here.  The distinction is not a matter of precision; they are different
epistemic objects.

*Settled order.*  Once a round has been applied, the order it was applied in is
on the chain.  Everyone reads it, everyone reads that everyone reads it, and so
on: it is **common knowledge**, which is exactly what a public signal means in
this vocabulary.  `log` records it and `revealingSignals` publishes it.

*In-flight submissions.*  Before a round is applied, pending submissions may be
visible to some observers.  This is **not** common knowledge.  A player seeing a
pending submission does not know who else saw it, nor that others know they saw
it.  Publishing it as a public signal would be *wrong* rather than coarse,
because a public signal here is common knowledge by construction.

**This module assumes no player observes a submission before it is applied.**
Front-running, and every strategy depending on reacting to a pending submission,
is outside the model.  Relaxing the assumption is not a matter of publishing
more signals: it needs an information structure able to express
mutual-but-not-common knowledge, which `InfoSignals` does not directly provide.
It is stated because a reader taking `revealingSignals` for "everything a chain
reveals" would credit the model with more faithfulness than it has.

The scheduler is given the joint submission, not merely the state.  That is the
adversarial reading — a sequencer sees what it is ordering — and it is a
modelling choice with game content, so it is explicit rather than buried inside
a step function.
-/

noncomputable section

namespace Vegas

open GameTheory.Protocol
open GameTheory.Math.Probability

universe uι uv

variable {ι : Type uι}

/-- A state machine whose round is resolved by applying each submitted action in
turn.  Ordering is a real degree of freedom exactly when `applyOne` calls fail
to commute. -/
structure ScheduledSystem (ι : Type uι) where
  /-- The underlying state, before any scheduling record is attached. -/
  Base : Type uv
  /-- Each player's action carrier. -/
  Action : ι → Type uv
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
  View : Type uv
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
  /-- Every non-terminal state admits a legal joint submission. -/
  progress : ∀ state, ¬ terminal state →
    ∃ joint, IsLegalJoint (active state) (available state) joint

namespace ScheduledSystem

variable (sys : ScheduledSystem.{uι, uv} ι)

/-- The order a round's submissions were applied in. -/
abbrev Order (_sys : ScheduledSystem.{uι, uv} ι) : Type uι := List ι

/-- A protocol state: the underlying state together with the public record of
the orders actually realized, most recent first. -/
structure State (sys : ScheduledSystem.{uι, uv} ι) where
  /-- The underlying state machine's state. -/
  base : sys.Base
  /-- Realized orders, most recent first.  Publicly observable. -/
  log : List sys.Order

/-- A scheduler picks the order a round's submissions are applied in.  It sees
both the protocol state and who submitted what. -/
abbrev Scheduler (sys : ScheduledSystem.{uι, uv} ι) : Type _ :=
  sys.State → (∀ i, Option (sys.Action i)) → sys.Order

/-- Apply the submitted actions along a given order, skipping players who did
not submit. -/
noncomputable def applyOrder (sys : ScheduledSystem.{uι, uv} ι)
    (joint : ∀ i, Option (sys.Action i)) :
    sys.Order → sys.Base → FinDist sys.Base
  | [], state => FinDist.pure state
  | i :: rest, state =>
      match joint i with
      | none => applyOrder sys joint rest state
      | some action =>
          (sys.applyOne state i action).bind (applyOrder sys joint rest)

/-- The execution protocol induced by a scheduler.  Its state carries the
realized-order log, so a strategy over it is a function of the order as well as
of the underlying state. -/
noncomputable def toExecutionProtocol (scheduler : sys.Scheduler) :
    ExecutionProtocol ι where
  State := sys.State
  Action := sys.Action
  init := { base := sys.init, log := [] }
  active state := sys.active state.base
  available state := sys.available state.base
  terminal state := sys.terminal state.base
  step state legal :=
    let order := scheduler state legal.1
    (sys.applyOrder legal.1 order state.base).map
      fun next => { base := next, log := order :: state.log }
  progress state hterminal := sys.progress state.base hterminal

/-- Every successor of a step records exactly the order the scheduler chose. -/
theorem log_of_mem_support_step (scheduler : sys.Scheduler)
    {state : sys.State}
    {legal : { joint // (sys.toExecutionProtocol scheduler).Legal state joint }}
    {next : sys.State}
    (hnext : next ∈ ((sys.toExecutionProtocol scheduler).step state legal).support) :
    next.log = scheduler state legal.1 :: state.log := by
  simp only [toExecutionProtocol, FinDist.support_map] at hnext
  obtain ⟨_base, _hbase, hnext⟩ := hnext
  rw [← hnext]

/-- **Confluence of effects is not invisibility of order.**

Two schedulers choosing different orders at the same state and submission induce
different successor laws — whatever the state machine does, and in particular
even when the two orders have identical effects.

A schedule-invariance result about the underlying machine constrains what the
machine computes; it says nothing about what a player observes.  Only a
statement about the protocol state does. -/
theorem step_ne_of_order_ne
    {left right : sys.Scheduler}
    {state : sys.State}
    {legalLeft : { joint // (sys.toExecutionProtocol left).Legal state joint }}
    {legalRight : { joint // (sys.toExecutionProtocol right).Legal state joint }}
    (hjoint : legalLeft.1 = legalRight.1)
    (horder : left state legalLeft.1 ≠ right state legalLeft.1) :
    (sys.toExecutionProtocol left).step state legalLeft ≠
      (sys.toExecutionProtocol right).step state legalRight := by
  intro heq
  obtain ⟨next, hnext⟩ :=
    ((sys.toExecutionProtocol left).step state legalLeft).support_nonempty
  have hleft : next.log = left state legalLeft.1 :: state.log :=
    sys.log_of_mem_support_step left hnext
  have hnextRight :
      next ∈ ((sys.toExecutionProtocol right).step state legalRight).support := by
    rw [← heq]
    exact hnext
  have hright : next.log = right state legalRight.1 :: state.log :=
    sys.log_of_mem_support_step right hnextRight
  rw [← hjoint] at hright
  exact horder (List.cons.inj (hleft.symm.trans hright)).1

/-! ## Two information models over one protocol -/

/-- What an order-revealing player knows: the current public view, and the
history of realized orders paired with the view each followed. -/
abbrev RevealingInfo (sys : ScheduledSystem.{uι, uv} ι) : Type _ :=
  sys.View × List (sys.Order × sys.View)

/-- What an order-blind player knows: the current public view and the earlier
views, with no record of how rounds were ordered. -/
abbrev BlindInfo (sys : ScheduledSystem.{uι, uv} ι) : Type _ :=
  sys.View × List sys.View

/-- Discard the schedule from an order-revealing information state. -/
def forgetOrders (info : sys.RevealingInfo) : sys.BlindInfo :=
  (info.1, info.2.map Prod.snd)

/-- Signals that publish the realized order alongside the public view: the
faithful model of a public runtime. -/
def revealingSignals (scheduler : sys.Scheduler) :
    InfoSignals (sys.toExecutionProtocol scheduler) where
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
def blindSignals (scheduler : sys.Scheduler) :
    InfoSignals (sys.toExecutionProtocol scheduler) where
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
forgetful map and differ in nothing else: whatever a blind player knows, a
revealing player knows, and the gap is precisely the realized orders. -/
theorem blind_infoOf_eq_forgetOrders (scheduler : sys.Scheduler) (i : ι)
    {state : (sys.toExecutionProtocol scheduler).State}
    (trace : ExecutionProtocol.Trace (sys.toExecutionProtocol scheduler) state) :
    (sys.blindSignals scheduler).infoOf i trace =
      sys.forgetOrders ((sys.revealingSignals scheduler).infoOf i trace) := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih =>
      -- rewrite with `ih` before unfolding the signal records: unfolding first
      -- replaces the head symbol `ih` matches on.
      rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend, ih]
      rfl

/-- The current view an order-blind player holds is the view of the state the
history reached.  This is what makes the public menu information-local. -/
theorem blind_infoOf_fst (scheduler : sys.Scheduler) (i : ι)
    {state : (sys.toExecutionProtocol scheduler).State}
    (trace : ExecutionProtocol.Trace (sys.toExecutionProtocol scheduler) state) :
    ((sys.blindSignals scheduler).infoOf i trace).1 = sys.view state.base := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized _ih =>
      rw [InfoSignals.infoOf_extend]
      rfl

/-- The same, for an order-revealing player. -/
theorem revealing_infoOf_fst (scheduler : sys.Scheduler) (i : ι)
    {state : (sys.toExecutionProtocol scheduler).State}
    (trace : ExecutionProtocol.Trace (sys.toExecutionProtocol scheduler) state) :
    ((sys.revealingSignals scheduler).infoOf i trace).1 = sys.view state.base := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized _ih =>
      rw [InfoSignals.infoOf_extend]
      rfl

/-- The order-blind information model: menus come from the publicly visible
view, which `menuAt_adequate` makes the real one. -/
def blindInformation (scheduler : sys.Scheduler) :
    InformationModel (sys.toExecutionProtocol scheduler) where
  toInfoSignals := sys.blindSignals scheduler
  menu i info := sys.menuAt info.1 i
  menu_adequate := by
    intro i state trace choice
    rw [sys.blind_infoOf_fst scheduler i trace]
    cases choice with
    | none => exact sys.menuAt_none state.base i
    | some action => exact sys.menuAt_some state.base i action

/-- The order-revealing information model.  Same menus — the schedule never
changes what is legal, only what is known. -/
def revealingInformation (scheduler : sys.Scheduler) :
    InformationModel (sys.toExecutionProtocol scheduler) where
  toInfoSignals := sys.revealingSignals scheduler
  menu i info := sys.menuAt info.1 i
  menu_adequate := by
    intro i state trace choice
    rw [sys.revealing_infoOf_fst scheduler i trace]
    cases choice with
    | none => exact sys.menuAt_none state.base i
    | some action => exact sys.menuAt_some state.base i action

/-- **The two models separate exactly on the schedule.**

Two realized steps reaching the same public view but scheduled differently are
*indistinguishable* to an order-blind observer and *distinguishable* to an
order-revealing one.

With `blind_infoOf_eq_forgetOrders`, which says blindness is precisely
discarding the order, this pins down the whole difference between the models:
not the state, not the effects, only the schedule. -/
theorem signals_separate_of_log_ne (scheduler : sys.Scheduler)
    {left right : ExecutionProtocol.StepEvent (sys.toExecutionProtocol scheduler)}
    (hview : sys.view left.target.base = sys.view right.target.base)
    (hlog : left.target.log.headD [] ≠ right.target.log.headD []) :
    (sys.blindSignals scheduler).publicSignal left =
        (sys.blindSignals scheduler).publicSignal right ∧
      (sys.revealingSignals scheduler).publicSignal left ≠
        (sys.revealingSignals scheduler).publicSignal right := by
  refine ⟨hview, ?_⟩
  intro heq
  exact hlog (congrArg Prod.snd heq)

/-! ## Order-oblivious deviations

The honest and robust readings are two classes of policy inside the one faithful
game, not two games.  A policy is *order-oblivious* when the schedule cannot
change what it does; that is a restriction on what a player reads, never on what
it can express, so the class still contains every policy a schedule-free source
could offer. -/

/-- A policy is order-oblivious when it acts the same at any two information
states differing only in schedule.

Phrased on the action rather than the menu-certified choice, whose type depends
on the information state; the action's does not. -/
def OrderOblivious (scheduler : sys.Scheduler) {i : ι}
    (policy : (sys.revealingInformation scheduler).Policy i) : Prop :=
  ∀ left right : sys.RevealingInfo,
    sys.forgetOrders left = sys.forgetOrders right → (policy left).1 = (policy right).1

/-- Read an order-blind policy as an order-revealing one by discarding the
schedule first.

This typechecks without transport because `forgetOrders` preserves the current
view and both menus are `menuAt` of that view, so the two `Choice` types are
definitionally equal. -/
def liftPolicy (scheduler : sys.Scheduler) {i : ι}
    (policy : (sys.blindInformation scheduler).Policy i) :
    (sys.revealingInformation scheduler).Policy i :=
  fun info => policy (sys.forgetOrders info)

/-- Everything an order-blind player could have played is order-oblivious.  So
the honest class is not an artificial restriction: it contains the image of
every schedule-free policy. -/
theorem liftPolicy_orderOblivious (scheduler : sys.Scheduler) {i : ι}
    (policy : (sys.blindInformation scheduler).Policy i) :
    sys.OrderOblivious scheduler (sys.liftPolicy scheduler policy) := by
  intro left right hforget
  change (policy (sys.forgetOrders left)).1 = (policy (sys.forgetOrders right)).1
  rw [hforget]

end ScheduledSystem

/-! ## A witness that the carrier is strictly larger

`liftPolicy_action_congr` is only interesting if some order-revealing policy
really does separate two schedule-distinct histories.  The system below is again
maximally confluent — every action is the identity — but gives each player two
options, which is the least a policy needs in order to say anything at all. -/

/-- Two players, a binary submission each, and a state nothing changes. -/
def coinSystem : ScheduledSystem.{0, 0} (Fin 2) where
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
  progress _ _ := ⟨fun _ => some true, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

/-- Any scheduler; the carrier question does not depend on which. -/
def coinScheduler : coinSystem.Scheduler := fun _ _ => [0, 1]

@[simp] theorem coin_menu (i : Fin 2)
    (info : (coinSystem.revealingInformation coinScheduler).InfoState i) :
    (coinSystem.revealingInformation coinScheduler).menu i info =
      {some true, some false} := rfl

/-- A history in which player `0` was ordered first. -/
def coinFirstZero : coinSystem.RevealingInfo := ((), [([0, 1], ())])

/-- The same history except that player `1` was ordered first.  The two have the
same public views throughout and differ only in schedule. -/
def coinFirstOne : coinSystem.RevealingInfo := ((), [([1, 0], ())])

theorem coinFirst_forgetOrders_eq :
    coinSystem.forgetOrders coinFirstZero =
      coinSystem.forgetOrders coinFirstOne := rfl

/-- An order-aware policy: submit `true` exactly when player `0` was ordered
first.  Nothing about the state differs between those histories — only the
schedule does. -/
def coinOrderAware (i : Fin 2) :
    (coinSystem.revealingInformation coinScheduler).Policy i :=
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
not follow from adequacy against the order-oblivious one.  The robust tier has
to be established on its own. -/
theorem coinOrderAware_not_orderOblivious (i : Fin 2) :
    ¬ coinSystem.OrderOblivious coinScheduler (coinOrderAware i) := by
  intro hoblivious
  have hcongr :=
    hoblivious coinFirstZero coinFirstOne coinFirst_forgetOrders_eq
  simp only [coinFirstZero, Fin.isValue, coinOrderAware,
    List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, ↓reduceIte,
    coinFirstOne, List.cons.injEq, one_ne_zero, zero_ne_one, and_true,
    and_self] at hcongr
  exact Bool.noConfusion (Option.some.inj hcongr)

/-! ## A witness that the separation is not vacuous

`step_ne_of_order_ne` would be worthless if its hypotheses could not be met, so
they are met here in the most extreme case available: a system whose actions are
the *identity*, so every pair of submissions commutes and the underlying state
law is literally constant.  Two schedulers remain distinguishable.  Nothing
weaker than recording the order could tell them apart, which is the argument for
recording it. -/

/-- Two players, one trivial submission each, and a state nothing changes.
Maximally confluent: every action is the identity. -/
def idleSystem : ScheduledSystem.{0, 0} (Fin 2) where
  Base := Unit
  Action _ := Unit
  init := ()
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  applyOne state _ _ := FinDist.pure state
  View := Unit
  view _ := ()
  menuAt _ _ := {some ()}
  menuAt_some _ _ _ := by simp
  menuAt_none _ _ := by simp
  progress _ _ := ⟨fun _ => some (), fun _ => ⟨trivial, Set.mem_univ _⟩⟩

/-- Both players submit. -/
def idleLegal (scheduler : idleSystem.Scheduler) (state : idleSystem.State) :
    { joint // (idleSystem.toExecutionProtocol scheduler).Legal state joint } :=
  ⟨fun _ => some (), not_false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

/-- One scheduler applies the players in index order. -/
def idleForward : idleSystem.Scheduler := fun _ _ => [0, 1]

/-- The other reverses them.  Same effects — every action is the identity. -/
def idleBackward : idleSystem.Scheduler := fun _ _ => [1, 0]

/-- **The separation is realized.**  Two schedulers over a system in which every
action is the identity — so the underlying state law is the same constant under
either order — nevertheless induce different successor laws, because the
realized order is part of what a player observes. -/
theorem idle_step_ne (state : idleSystem.State) :
    (idleSystem.toExecutionProtocol idleForward).step state
        (idleLegal idleForward state) ≠
      (idleSystem.toExecutionProtocol idleBackward).step state
        (idleLegal idleBackward state) := by
  refine idleSystem.step_ne_of_order_ne rfl ?_
  intro horder
  exact absurd (List.cons.inj horder).1 (by decide)

end Vegas
