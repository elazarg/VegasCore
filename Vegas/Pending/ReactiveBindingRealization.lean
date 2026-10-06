/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingContinuation
import Interaction.ReactiveMenuContinuation

/-! # One legal behavioral continuation for the whole starting information set

The repaired continuation is the existing retained policy. Its private seed is
fixed by the starting own recall, so the same policy and seed serve every
hidden history in that information set. This identifies the exact protocol
continuation law with the joint implementation runner used by stopped repair.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (menu larger : (runtime.reactiveApplication leaks).ResponseMenu)
  (included : menu.IncludedIn larger)

/-- The actual retained behavioral evaluator equals the repair runner against
unchanged target opponents. Neither the policy nor its initial private seed
depends on the hidden execution. No payoff comparison is assumed here. -/
theorem retainedPolicy_runFrom
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (source : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, (larger.information initial horizon scheduler).BehavioralPolicy who)
    (agrees : (included.actionRestriction initial horizon scheduler).ExtendsProfile source target)
    (who : Player) (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (policy : (runtime.reactiveApplication leaks).Policy)
    (remaining fuel : Nat) (enough : 2 * remaining + 1 ≤ fuel)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (history : (menu.protocol initial horizon scheduler).History)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (recalled : execution.recall who = reference) :
    let app := runtime.reactiveApplication leaks
    let players := Function.update (larger.decodeProfile initial horizon scheduler target)
      who policy
    let strategy := retainedImplementation runtime leaks menu who reference policy
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (Function.update source who
        (retainedPolicy runtime leaks menu initial horizon scheduler who reference policy))
      fuel history).map History.state =
        ((strategy.resume who players (some who) execution (atRecall runtime leaks reference)).bind
          fun next => strategy.runJoint who players scheduler remaining next.1 next.2).map
            (fun next => app.finished next.1) := by
  intro app players strategy
  have law := included.runFrom_restrictPolicy_finish initial horizon scheduler source target agrees
    who strategy.policy (retainedImplementation_policy_available runtime leaks menu who reference
      policy) fuel history (by rw [current]; exact enough)
  change ((menu.information initial horizon scheduler).runBehavioralFrom
    (Function.update source who
      (retainedPolicy runtime leaks menu initial horizon scheduler who reference policy))
    fuel history).map History.state = _ at law
  rw [law, current, ReactiveApplication.finish]
  have realized := retainedImplementation_continuation runtime leaks menu who reference policy
    players scheduler remaining execution recalled
  change ((strategy.resume who players (some who) execution (atRecall runtime leaks reference)).bind
    fun next => strategy.run who players scheduler remaining next.1 next.2) =
      (app.resume (Function.update players who strategy.policy) (some who) execution).bind
        (app.runRounds scheduler (Function.update players who strategy.policy) remaining)
    at realized
  simp only [players, Function.update_idem] at realized
  rw [← realized]
  simp only [ReactiveApplication.Implementation.run, PMF.map_bind, PMF.map_comp]
  rfl

/-- From the initial history, the retained policy with the empty reference
recall realizes the repair runner from every initial execution, with private
memory starting at the empty recall. -/
theorem retainedPolicy_initialLaw
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (source : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (target : ∀ who, (larger.information initial horizon scheduler).BehavioralPolicy who)
    (agrees : (included.actionRestriction initial horizon scheduler).ExtendsProfile source target)
    (who : Player) (policy : (runtime.reactiveApplication leaks).Policy)
    (fuel : Nat) (enough : 2 * horizon + 1 ≤ fuel) :
    let app := runtime.reactiveApplication leaks
    let players := Function.update (larger.decodeProfile initial horizon scheduler target)
      who policy
    let strategy := retainedImplementation runtime leaks menu who [] policy
    ((menu.information initial horizon scheduler).runBehavioral
      (Function.update source who
        (retainedPolicy runtime leaks menu initial horizon scheduler who [] policy))
      fuel).map History.state =
        initial.bind fun state =>
          (strategy.runJoint who players scheduler horizon
            (ReactiveApplication.Execution.initial app state) (atRecall runtime leaks [])).map
              (fun next => app.finished next.1) := by
  intro app players strategy
  have law := included.runFrom_restrictPolicy_finish initial horizon scheduler source target agrees
    who strategy.policy (retainedImplementation_policy_available runtime leaks menu who [] policy)
    fuel (menu.protocol initial horizon scheduler).initHistory enough
  change ((menu.information initial horizon scheduler).runBehavioralFrom
    (Function.update source who
      (retainedPolicy runtime leaks menu initial horizon scheduler who [] policy))
    fuel (menu.protocol initial horizon scheduler).initHistory).map History.state = _ at law
  rw [InformationModel.runBehavioral, law]
  change initial.bind (fun state => (app.runRounds scheduler
    (Function.update (larger.decodeProfile initial horizon scheduler target) who strategy.policy)
    horizon (ReactiveApplication.Execution.initial app state)).map app.finished) = _
  apply bind_congr_on_support _
  intro state _
  have realized := strategy.realize who players scheduler horizon
    (ReactiveApplication.Execution.initial app state)
  have empty : (ReactiveApplication.Execution.initial app state).recall who = [] := rfl
  rw [empty, retainedImplementation_posterior_prefix runtime leaks menu who [] [] policy le_rfl,
    PMF.pure_bind] at realized
  simp only [players, Function.update_idem] at realized
  rw [← realized, ReactiveApplication.Implementation.run, PMF.map_comp]
  rfl

end Vegas.EventGraphRuntime.BindingMemory
