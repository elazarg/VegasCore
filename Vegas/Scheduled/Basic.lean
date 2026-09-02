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
blockchain-specific: the underlying state machine is a parameter.

The module deliberately depends only on `GameTheory`, so it can be lifted into
that library once the interface has been exercised by a real client.

## The one design decision that matters

`ScheduledState` records the realized order in a `log`, and the induced
`ExecutionProtocol` carries that log in its state.  On a public runtime the
order in which transactions landed *is* observable, so a model that quotients it
away understates what a strategy may condition on, and any preservation theorem
proved against such a model is a theorem about a system nobody runs.

The cost of carrying it is `log_ne_of_order_ne`: **confluence of effects is not
invisibility of order.**  Even where every pair of submissions commutes, so the
underlying state law is schedule-invariant, two schedulers still produce
distinguishable protocol states.  Order-independence of *effects* and
order-independence of *information* are different properties, and only the first
follows from commutation.

The scheduler is given the joint submission, not merely the state.  That is the
adversarial reading — a sequencer sees the pending transactions — and it is a
modelling choice with game content, so it is made explicitly here rather than
left implicit in a step function.

## What is observable, and what is assumed

Two different things are visible on a public runtime, and only one of them is
modelled here.  The distinction is not a matter of precision; they are different
epistemic objects.

*Settled order.*  Once a round has been applied, the order it was applied in is
on the chain.  Everyone can read it, everyone can read that everyone can read
it, and so on: it is **common knowledge**, which is exactly what a public signal
means in this vocabulary.  `log` records this, and `revealingSignals` publishes
it.

*In-flight submissions.*  Before a round is applied, pending submissions may be
visible to some observers.  This is **not** common knowledge.  A player who sees
a pending submission does not know who else saw it, nor that others know they
saw it, and a player who did not see it may not know it existed.  Publishing it
as a public signal would therefore be *wrong* rather than merely coarse, because
a public signal in an information model is common knowledge by construction.

**This module assumes no player observes a submission before it is applied.**
Front-running, and every strategy that depends on reacting to a pending
submission, is outside the model.  Relaxing the assumption is not a matter of
publishing more signals: it needs an information structure able to express
mutual-but-not-common knowledge, which `InfoSignals` does not directly provide.
The assumption is stated here because a reader who takes `revealingSignals` for
"everything a chain reveals" would credit the model with more faithfulness than
it has.
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
  /-- Every non-terminal state admits a legal joint submission. -/
  progress : ∀ state, ¬ terminal state →
    ∃ joint, IsLegalJoint (active state) (available state) joint

namespace ScheduledSystem

variable (sys : ScheduledSystem.{uι, uv} ι)

/-- The order a round's submissions were applied in. -/
abbrev Order (_sys : ScheduledSystem.{uι, uv} ι) : Type uι := List ι

/-- A protocol state: the underlying state together with the public record of
the orders actually realized, most recent first.

The `log` is what makes this model faithful to a public runtime, and what
distinguishes it from a model that resolves a round atomically. -/
structure State (sys : ScheduledSystem.{uι, uv} ι) where
  /-- The underlying state machine's state. -/
  base : sys.Base
  /-- Realized orders, most recent first.  Publicly observable. -/
  log : List (sys.Order)

/-- A scheduler picks the order in which a round's submissions are applied.  It
sees both the protocol state and who submitted what. -/
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

/-- The execution protocol induced by a scheduler.

Its state carries the realized-order log, so a strategy over this protocol is a
function of the order as well as of the underlying state — which is exactly the
enlarged carrier a public runtime offers. -/
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

@[simp] theorem toExecutionProtocol_terminal (scheduler : sys.Scheduler)
    (state : sys.State) :
    (sys.toExecutionProtocol scheduler).terminal state = sys.terminal state.base :=
  rfl

/-- Every successor of a step records exactly the order the scheduler chose.
The realized order is therefore observable, not merely operational. -/
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

Whenever two schedulers choose different orders at the same state and joint
submission, their successor laws differ — even if the underlying state law is
identical, so that the two orders are indistinguishable in their *effect*.

This is the formal content of the distinction the development turns on.  A
schedule-invariance result about the underlying state machine says nothing about
what a strategy can observe; only a statement about the protocol state does. -/
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

end ScheduledSystem

/-! ## Two information models over one protocol

The honest and robust readings are not a predicate on strategies; they are a
choice of *information model* over the same protocol.  `GameTheory` makes policy
locality structural — a policy is a function of an information state, so a
policy that reads something absent from that state cannot be written at all.
So the question "may a player condition on the schedule?" is settled entirely by
whether the realized order reaches the information state.

Both models below are legitimate `InfoSignals` over the same execution
protocol.  They differ in one component. -/

namespace ScheduledSystem

variable (sys : ScheduledSystem.{uι, uv} ι)

/-- Signals that publish the realized order alongside the public view.

This is the faithful model of a public runtime: a player sees the state *and*
the order transactions landed in. -/
def revealingSignals (scheduler : sys.Scheduler) :
    InfoSignals (sys.toExecutionProtocol scheduler) where
  PublicSignal := sys.View × sys.Order
  PrivateSignal _ := PUnit
  initialPublic := (sys.view sys.init, [])
  initialPrivate _ := PUnit.unit
  publicSignal event := (sys.view event.target.base, event.target.log.headD [])
  privateSignal _ _ := PUnit.unit
  InfoState _ := List (sys.View × sys.Order)
  initInfo _ _ signal := [signal]
  pushInfo _ info _ _ signal := signal :: info

/-- Signals that publish only the public view, discarding the realized order.

This is the idealization: it describes a runtime that resolves a round
atomically.  It is a perfectly good information model — it just is not a model
of a public chain. -/
def blindSignals (scheduler : sys.Scheduler) :
    InfoSignals (sys.toExecutionProtocol scheduler) where
  PublicSignal := sys.View
  PrivateSignal _ := PUnit
  initialPublic := sys.view sys.init
  initialPrivate _ := PUnit.unit
  publicSignal event := sys.view event.target.base
  privateSignal _ _ := PUnit.unit
  InfoState _ := List sys.View
  initInfo _ _ signal := [signal]
  pushInfo _ info _ _ signal := signal :: info

/-- **Blindness is exactly discarding the schedule.**

The order-blind information state is the schedule-forgetting projection of the
order-revealing one, after every history.  So the two models are related by a
forgetful map and differ in nothing else: whatever an order-blind player knows,
an order-revealing player also knows, and the gap between them is precisely the
realized orders. -/
theorem blind_infoOf_eq_map_revealing (scheduler : sys.Scheduler) (i : ι)
    {state : (sys.toExecutionProtocol scheduler).State}
    (trace : ExecutionProtocol.Trace (sys.toExecutionProtocol scheduler) state) :
    (sys.blindSignals scheduler).infoOf i trace =
      ((sys.revealingSignals scheduler).infoOf i trace).map Prod.fst := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih =>
      -- rewrite with `ih` before unfolding the signal records: unfolding them
      -- first replaces the head symbol `ih` matches on.
      rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend, ih]
      rfl

/-- **The two models separate exactly on the schedule.**

Two realized steps that reach the same public view but were scheduled
differently are *indistinguishable* to an order-blind observer and
*distinguishable* to an order-revealing one.

With `blind_infoOf_eq_map_revealing`, which says blindness is precisely
discarding the order, this pins down the entire difference between the two
models: not the state, not the effects, only the schedule. -/
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

end ScheduledSystem

/-! ## A witness that the separation is not vacuous

`step_ne_of_order_ne` would be worthless if its hypotheses could not be met, so
they are met here in the most extreme case available: a system whose actions are
the *identity*, so every pair of submissions commutes and the underlying state
law is literally constant.  Two schedulers are still distinguishable.

Nothing weaker than recording the order could distinguish them, which is the
argument for carrying the log at all. -/

/-- Two players, one trivial submission each, and a state that nothing changes.
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
