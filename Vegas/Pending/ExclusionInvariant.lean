/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionCompletion
import Vegas.Pending.EventInvariant

/-! # Invariants of automatic graph completion

Automatic service preserves the same native invariant, typed cells and
relative deadlines as inclusion, samples and expiry.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.State

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Automatic completion uses the native activation refresh around its graph step. -/
theorem completeAutomatic_activatedAt (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    (state.completeAutomatic event eligible).activatedAt =
      refreshActivated (state.completeAutomatic event eligible).config
        state.clock state.activatedAt := by
  obtain ⟨owner, acting, _inactive⟩ := eligible.owned
  cases view : nodeView graph event with
  | bind actor payload outputEq codeEq =>
      simp only [completeAutomatic, completeFailure, view, complete]
  | resolve actor payload binding checks outputEq codeEq =>
      simp only [completeAutomatic, completeFailure, view, complete]
  | sample payload law outputEq codeEq =>
      have ownerless : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [ownerless] at acting
      cases acting

/-- Native automatic completion preserves graph reachability and activation clocks. -/
theorem Invariant.completeAutomatic {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    (state.completeAutomatic event eligible).Invariant inputs := by
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  have refreshed := invariant.refreshStep event eligible.1 action
    (state.completeAutomatic event eligible).config supported
  apply refreshed.copy
  · rfl
  · exact (state.completeFailure_tables event eligible.1).2.2
  · exact state.completeAutomatic_activatedAt event eligible

/-- The bounded automatic trace preserves the same native invariant. -/
theorem Invariant.drainFuel {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) (fuel : Nat) :
    (drainFuel fuel state).Invariant inputs := by
  exact drainFuel_induction (fun current => current.Invariant inputs)
    (fun _ event eligible valid => valid.completeAutomatic event eligible)
    fuel state invariant

/-- Fully draining automatic events preserves the same native invariant. -/
theorem Invariant.drain {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) : state.drain.Invariant inputs :=
  invariant.drainFuel state.config.remaining

/-- Automatic completion retains every existing typed cell without reachability assumptions. -/
theorem completeAutomatic_store_of_some (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) (field : graph.Field)
    (value : (graph.layout field).Value) (stored : state.config.store field = some value) :
    (state.completeAutomatic event eligible).config.store field = some value := by
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  exact state.config.step_store_of_some _ event eligible.1 action supported field value stored

/-- The bounded automatic trace retains every existing typed cell. -/
theorem drainFuel_store_of_some (fuel : Nat) (state : State graph) (field : graph.Field)
    (value : (graph.layout field).Value) (stored : state.config.store field = some value) :
    (drainFuel fuel state).config.store field = some value := by
  exact drainFuel_induction (fun current => current.config.store field = some value)
    (fun before event eligible current =>
      before.completeAutomatic_store_of_some event eligible field value current)
    fuel state stored

/-- Fully draining automatic events retains every existing typed cell. -/
theorem drain_store_of_some (state : State graph) (field : graph.Field)
    (value : (graph.layout field).Value) (stored : state.config.store field = some value) :
    state.drain.config.store field = some value :=
  drainFuel_store_of_some state.config.remaining state field value stored

/-- An unrelated automatic completion cannot reset an unfinished event's deadline. -/
theorem Invariant.completeAutomatic_activatedAt_of_not_completed
    {inputs : graph.Inputs} {state : State graph} (invariant : state.Invariant inputs)
    (event : graph.EventId) (eligible : state.AutomaticReady event)
    (query : graph.EventId) (entered : Nat) (activated : state.activatedAt query = some entered)
    (unfinished : query ∉ (state.completeAutomatic event eligible).config.cut.completed) :
    (state.completeAutomatic event eligible).activatedAt query = some entered := by
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  rw [state.completeAutomatic_activatedAt event eligible]
  exact invariant.refreshStep_activatedAt_of_not_completed event query eligible.1 action
    (state.completeAutomatic event eligible).config supported entered activated unfinished

/-- Automatic completion can only enlarge the completed frontier. -/
theorem completeAutomatic_completed_subset (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    state.config.cut.completed ⊆
      (state.completeAutomatic event eligible).config.cut.completed := by
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  exact completed_subset_of_mem_step state.config event eligible.1 action _ supported

/-- The bounded automatic trace can only enlarge the completed frontier. -/
theorem drainFuel_completed_subset (fuel : Nat) (state : State graph) :
    state.config.cut.completed ⊆ (drainFuel fuel state).config.cut.completed := by
  exact drainFuel_induction
    (fun current => state.config.cut.completed ⊆ current.config.cut.completed)
    (fun before event eligible prior =>
      prior.trans (before.completeAutomatic_completed_subset event eligible))
    fuel state (Finset.Subset.refl _)

/-- A whole automatic drain retains an existing deadline for an unfinished event. -/
theorem Invariant.drainFuel_activatedAt_of_not_completed
    {inputs : graph.Inputs} {state : State graph} (invariant : state.Invariant inputs)
    (fuel : Nat) (query : graph.EventId) (entered : Nat)
    (activated : state.activatedAt query = some entered)
    (unfinished : query ∉ (State.drainFuel fuel state).config.cut.completed) :
    (State.drainFuel fuel state).activatedAt query = some entered := by
  have preserved := drainFuel_induction
    (fun current => current.Invariant inputs ∧
      (query ∉ current.config.cut.completed → current.activatedAt query = some entered))
    (fun before event eligible prior => by
      refine ⟨prior.1.completeAutomatic event eligible, ?_⟩
      intro remains
      have earlier : query ∉ before.config.cut.completed :=
        fun completed =>
          remains (before.completeAutomatic_completed_subset event eligible completed)
      exact prior.1.completeAutomatic_activatedAt_of_not_completed event eligible query entered
        (prior.2 earlier) remains)
    fuel state ⟨invariant, fun _ => activated⟩
  exact preserved.2 unfinished

/-- Draining automatic events cannot reset an unfinished event's deadline. -/
theorem Invariant.drain_activatedAt_of_not_completed
    {inputs : graph.Inputs} {state : State graph} (invariant : state.Invariant inputs)
    (query : graph.EventId) (entered : Nat) (activated : state.activatedAt query = some entered)
    (unfinished : query ∉ state.drain.config.cut.completed) :
    state.drain.activatedAt query = some entered :=
  invariant.drainFuel_activatedAt_of_not_completed state.config.remaining query entered
    activated unfinished

end Vegas.EventGraphRuntime.State
