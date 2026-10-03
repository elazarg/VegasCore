/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstActivation
import Vegas.Game.SourceServiceFirstTurnMixture
import Vegas.Game.SourceServiceCanonicalConformance

/-! # Physical resources before the first own event input

These facts concern actual turn counting and nonowner scheduler commands.
They do not depend on the binding or resolution constructor, a source
posterior, or a completion law.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
/-- No recalled input at an event makes its current own turn the first one. -/
theorem sourceServiceTurnInput_first
    (owner : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (absent : sourceServiceTurnInput? setup leaks owner event past = none)
    (turn : view.application.publicView.ownTurn? owner = some event) :
    sourceServiceTurn setup leaks owner event past view = some 0 := by
  unfold sourceServiceTurn
  simp only [turn, ↓reduceIte]
  apply congrArg some
  apply List.countP_eq_zero.mpr
  intro entry member selected
  exact (sourceServiceTurnInput?_eq_none_iff owner event past).mp absent entry member
    (of_decide_eq_true selected)

/-- Away from the current event owner's activation, both the fixed first-turn
policy and the whole prescribed profile dispatch only silent responses. -/
theorem sourceServiceFirstTurn_nonowner_dispatch
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event)
    (execution : (application setup leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup leaks).Command) (foreign : command ≠ .activate owner) :
    (application setup leaks).dispatch
        (decidedProfile (leaks := leaks) bound owner event action) command execution =
      (application setup leaks).dispatch
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        command execution ∧
    (application setup leaks).dispatch
        (decidedProfile (leaks := leaks) bound owner event action) command execution =
      (application setup leaks).dispatch
        (fun _ => (application setup leaks).silentPolicy) command execution := by
  let app := application setup leaks
  cases command with
  | activate actor =>
      have different : actor ≠ owner := fun same => foreign (by rw [same])
      have each (middle : app.Execution)
          (observed : middle ∈ (execution.environmentStep app (.activate actor)).support) :
          sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile
              actor (middle.recall actor) (middle.observe app actor) =
            app.silentPolicy (middle.recall actor) (middle.observe app actor) := by
        apply sourceServiceTurnPolicy_idle setup leaks bound turns _ profile actor _ _
        apply (soleReady_of_ready setup middle.application (by
          rw [activation_application setup leaks execution middle actor observed]
          exact ready)).idle
        rw [owned]
        intro same
        exact different (Option.some.inj same).symm
      dsimp only [app] at each
      constructor
      · simp only [ReactiveApplication.dispatch]
        apply bind_congr_on_support _
        intro middle observed
        simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
          ReactiveApplication.invoke, decidedProfile, Function.update_of_ne different,
          each middle observed]
      · simp only [ReactiveApplication.dispatch]
        apply bind_congr_on_support _
        intro middle _
        simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
          ReactiveApplication.invoke, decidedProfile, Function.update_of_ne different]
  | «include» _ | application _ | wait => exact ⟨rfl, rfl⟩

/-- A nonowner scheduler command cannot create the owner's first event input. -/
theorem sourceServiceTurnInput_nonowner_dispatch
    (players : Player → (application setup leaks).Policy) (owner : Player)
    (event : (graph setup).EventId) (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command) (foreign : command ≠ .activate owner)
    (absent : sourceServiceTurnInput? setup leaks owner event (execution.recall owner) = none)
    (moved : next ∈ ((application setup leaks).dispatch players command execution).support) :
    sourceServiceTurnInput? setup leaks owner event (next.recall owner) = none := by
  let app := application setup leaks
  obtain ⟨middle, observed, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have recallEq := app.environmentStep_recall execution middle command observed
  cases actor : command.actor? app with
  | none =>
      change next ∈ (app.resume players (command.actor? app) middle).support at resumed
      rw [actor, ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
      subst next
      rw [recallEq]
      exact absent
  | some who =>
      have different : owner ≠ who := by
        intro same
        subst who
        apply foreign
        cases command with
        | activate actor =>
            exact congrArg ReactiveApplication.Command.activate
              (Option.some.inj actor)
        | «include» _ | application _ | wait => cases actor
      change next ∈ (app.resume players (command.actor? app) middle).support at resumed
      rw [actor, ReactiveApplication.resume, ReactiveApplication.invoke, PMF.support_map] at resumed
      obtain ⟨response, _, rfl⟩ := resumed
      rw [app.respond_recall_other middle who owner different response, recallEq]
      exact absent

/-- An actual first owner activation supplies its real trace, protected
deadline, unused canonical slot and conforming earlier packets. These facts
hold for either kind of owned decision. -/
theorem sourceServiceFirstActivation_resources
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (execution middle : (application setup leaks).Execution)
    (within : execution.environmentRecall.length < horizon)
    (initialized : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup)
      scheduler (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        profile) execution.environmentRecall.length).support)
    (ready : execution.application.config.cut.Ready event)
    (absent : sourceServiceTurnInput? setup leaks owner event (execution.recall owner) = none)
    (selected : .activate owner ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment (application setup leaks))).support)
    (observed : middle ∈ (execution.environmentStep (application setup leaks)
      (.activate owner)).support) :
    Nonempty (((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨horizon - execution.environmentRecall.length - 1, some owner, middle⟩)) ∧
      middle.application.publicView.ownTurn? owner = some event ∧
      sourceServiceTurn setup leaks owner event (middle.recall owner)
        (middle.observe (application setup leaks) owner) = some 0 ∧
      middle.application.publicView.InclusionFitsDeadline (runtime setup) bound event ∧
      OwnSubmissionsAtTurn setup leaks middle owner ∧
      CanonicalSlotsUsed setup leaks middle owner ∧
      (runtime setup).eventRecorded leaks (middle.recall owner) event = false ∧
      middle.application.candidates.lookup
        (owner, .prepared (middle.application.publicView.bindingCount owner)) = .fresh ∧
      FreshCallsConform setup leaks middle owner := by
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    execution.environmentRecall.length within.le execution initialized
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
    (horizon - execution.environmentRecall.length - 1) execution middle (.activate owner)
    (by convert trace using 1; congr 2; omega) selected observed
  have applicationEq := activation_application setup leaks execution middle owner observed
  have recallEq := app.environmentStep_recall execution middle (.activate owner) observed
  have middleReady : middle.application.config.cut.Ready event := by
    rw [applicationEq]
    exact ready
  have turn := ownTurn?_of_ready setup middle.application middleReady owned
  have first := sourceServiceTurnInput_first setup leaks owner event (middle.recall owner)
    (middle.observe app owner) (by rw [recallEq]; exact absent) turn
  have firstBefore : sourceServiceTurn setup leaks owner event (execution.recall owner)
      (middle.observe app owner) = some 0 := by rw [← recallEq]; exact first
  have fits := firstTurn_inclusionFits contract timely trace
    (roundsFrom_activationsAnswered _ execution initialized) owned ready firstBefore
  have middleFits : middle.application.publicView.InclusionFitsDeadline (runtime setup) bound
      event := by rw [applicationEq]; exact fits
  obtain ⟨atTurn, slots⟩ := canonicalSlots_roundsFrom scheduler players owner
    (firstTurnTiming setup turns) profile rfl _ execution initialized
  have middleAtTurn : OwnSubmissionsAtTurn setup leaks middle owner := by
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact atTurn
  have middleSlots := canonicalSlotsUsed_environment observed owner slots
  have unrecorded := sourceServiceFirstTurn_unrecorded middleAtTurn first
  have fresh := canonicalSlot_fresh_of_used middleTrace owner middleAtTurn middleSlots event
    turn unrecorded
  refine ⟨⟨middleTrace⟩, turn, first, middleFits, middleAtTurn, middleSlots, unrecorded, fresh, ?_⟩
  unfold FreshCallsConform
  rw [recallEq]
  intro entry member material message submits emitted
  exact sourceServiceTurnPolicy_freshServiceEnvelope scheduler players owner
    (firstTurnTiming setup turns) profile rfl _ execution initialized entry member material
      submits message emitted

end Vegas
