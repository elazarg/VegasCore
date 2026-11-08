/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunPoint
import Vegas.Game.DeviationSplit

/-! # Solitary phases through the closure

At a phase boundary whose event is not a reveal, the event may already have
completed automatically, for an owner defaulted by an earlier event. Those
executions skip the phase. The deviator tells them apart from the others, both
before and after the phase, by whether the event's owner was defaulted by an
event before it.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A simulation for a larger set of executions is one for a smaller set. -/
theorem DeviationSimulation.mono {Principal : Type} [DecidableEq Principal]
    {app : ReactiveApplication Principal} {scheduler : app.Scheduler}
    {players : Principal → app.Policy} {horizon : Nat} {Point Outcome Traffic View Policy : Type}
    {read : Point → Outcome} {point : app.Execution → Point} {traffic : app.Execution → Traffic}
    {view : Point → View} {target : Policy → Point → PMF Outcome}
    {small large : app.Execution → Prop}
    (simulation :
      DeviationSimulation scheduler players horizon read point traffic view target large)
    (within : ∀ execution, small execution → large execution) :
    DeviationSimulation scheduler players horizon read point traffic view target small :=
  fun prior execution goods noise factor => simulation prior execution
    (fun seed member => within _ (goods seed member)) noise factor

/-- The deviator sees that an owner was defaulted by an event before `event`. -/
def DefaultedBefore (who : Player) (event : (serviceGraph setup mode).EventId) (owner : Player)
    (view : Option ((serviceGraph setup mode).PlayerObservation who)) : Prop :=
  ∃ config : (serviceGraph setup mode).Config, keyView who (runKey config) = view ∧
    ∃ defaulting : (serviceGraph setup mode).EventId, defaulting.val < event.val ∧
      (completionOf config defaulting).bind EventCompletion.defaultEvent = some owner

/-- **An owned solitary event skipped at a boundary.** At a phase boundary
whose event is owned, the event has completed exactly when the deviator sees,
in the closure of any later configuration, that its owner was defaulted by an
earlier event. -/
theorem completed_iff_defaultedBefore (reference : (serviceGraph setup mode).BehavioralProfile)
    (who : Player)
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {horizon : Nat}
    {event : (serviceGraph setup mode).EventId} {owner : Player}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (boundary : PhaseBoundary scheduler players horizon event.val execution)
    {later : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step execution.application.config later) :
    event ∈ execution.application.config.cut.completed ↔
      DefaultedBefore who event owner
        (keyView who (runKey (closure reference who later))) := by
  let G := serviceGraph setup mode
  have toClosure := path.trans (closure_path reference who later)
  constructor
  · intro done
    obtain ⟨_, _, other, otherOwned, inactive⟩ := boundary.later event le_rfl done
    rw [owned] at otherOwned
    cases otherOwned
    rw [mem_defaulted_iff_completionOf] at inactive
    obtain ⟨defaulting, found⟩ := inactive
    obtain ⟨record, recorded⟩ : ∃ record,
        completionOf execution.application.config defaulting = some record := by
      cases recordedEq : completionOf execution.application.config defaulting with
      | none => rw [recordedEq] at found; cases found
      | some record => exact ⟨record, rfl⟩
    have doneDefaulting : defaulting ∈ execution.application.config.cut.completed :=
      (completionOf_isSome_iff _ defaulting).mp (by rw [recorded]; rfl)
    have early : defaulting.val < event.val := by
      by_contra late
      push Not at late
      rw [(boundary.later defaulting late doneDefaulting).1] at found
      cases found
    refine ⟨closure reference who later, rfl, defaulting, early, ?_⟩
    rw [Config.Step.path_completionOf_of_some toClosure defaulting record recorded, ← recorded]
    exact found
  · rintro ⟨config, views, defaulting, early, found⟩
    rw [keyView_runKey, keyView_runKey] at views
    have present : (completionOf config defaulting).isSome := by
      cases recordedEq : completionOf config defaulting with
      | none => rw [recordedEq] at found; cases found
      | some _ => rfl
    have defaults := normalize_defaultEvent_congr who (Option.some.inj views) defaulting present
    have doneDefaulting := boundary.earlier defaulting early
    obtain ⟨record, recorded⟩ := Option.isSome_iff_exists.mp
      ((completionOf_isSome_iff _ defaulting).mpr doneDefaulting)
    rw [Config.Step.path_completionOf_of_some toClosure defaulting record recorded] at defaults
    have inactive : owner ∈ execution.application.config.defaulted := by
      rw [mem_defaulted_iff_completionOf]
      exact ⟨defaulting, by rw [recorded, ← defaults]; exact found⟩
    by_contra pending
    have ready : execution.application.config.cut.Ready event := ⟨pending, fun prior member =>
      boundary.earlier prior (G.order.predecessor_lt member)⟩
    apply boundary.quiescent event
    unfold EventGraphRuntime.State.AutomaticReady
    rw [owned]
    exact ⟨ready, inactive⟩

end Vegas
