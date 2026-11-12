module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.CanonicalKeyLaw
public import Vegas.EventGraph.LastSchedulerErasure

@[expose] public section

/-! # The last-served key law under native automatic completion

A defaulted owner's event is movable under the scheduler that serves one player
last: it belongs to another player, or that player has defaulted. Automatic
completion executes the owner's forced failure, which is the profile's action
law there, so draining preserves the law of the final key when that player is
served last.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.State

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A defaulted owner's event is movable. -/
theorem movable_of_defaulted (who : Player) {config : graph.Config} {event : graph.EventId}
    {owner : Player} (acting : graph.actor? event = some owner)
    (inactive : owner ∈ config.defaulted) : Movable who config event := by
  by_cases same : owner = who
  · subst owner
    exact Or.inr inactive
  · exact Or.inl fun owned => same (Option.some.inj (acting.symm.trans owned))

/-- A step of a defaulted owner's ready event preserves the last-served key
law, whatever action it is given. -/
theorem lastLaw_of_mem_step_defaulted {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) (config next : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) (owner : Player)
    (acting : graph.actor? event = some owner) (inactive : owner ∈ config.defaulted)
    (action : graph.Action event) (member : next ∈ (config.step event ready action).support) :
    lastLaw profile who next = lastLaw profile who config := by
  obtain ⟨result, law⟩ := config.step_eq_pure_of_actor event ready action owner acting
  rw [law, PMF.mem_support_pure_iff] at member
  subst next
  have stepLaw : eventStep profile config event ready = PMF.pure result := by
    unfold eventStep
    rw [actionLaw_of_actor profile config acting, dite_eq_left inactive, PMF.pure_bind,
      config.step_eq_of_defaulted event ready owner acting inactive _ action, law]
  rw [← independent.eventStep_bind_lastLaw _ config rfl event ready
    (movable_of_defaulted who acting inactive), stepLaw, PMF.pure_bind]

/-- One automatic completion preserves the last-served key law. -/
theorem completeAutomatic_lastLaw {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    lastLaw profile who (state.completeAutomatic event eligible).config =
      lastLaw profile who state.config := by
  obtain ⟨owner, acting, inactive⟩ := eligible.owned
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  exact lastLaw_of_mem_step_defaulted independent _ _ event eligible.1 owner acting inactive
    action supported

/-- Bounded automatic draining preserves the last-served key law. -/
theorem drain_lastLaw {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) (state : State graph) :
    lastLaw profile who state.drain.config = lastLaw profile who state.config :=
  drainFuel_induction (fun current => lastLaw profile who current.config =
      lastLaw profile who state.config)
    (fun before event eligible previous =>
      (completeAutomatic_lastLaw independent before event eligible).trans previous)
    state.config.remaining state rfl

end Vegas.EventGraphRuntime.State
