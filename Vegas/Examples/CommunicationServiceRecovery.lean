/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.ReactiveEarlyOpeningPolicy
import Vegas.Pending.ReactiveAuthorization
import GameTheoryExtensions.Math.Probability.Support

/-! # An earlier own proposal can defeat a fresh recovery proposal

The recurring service visits the unavailable reveal before the binding. In
that first visit the owner submits a binding for value one, which remains
pending. At the next ready, timely binding visit, the actual compiler recovers
by submitting the source policy's value zero. One permitted wire inclusion
installs the earlier proposal before reserved inclusion.

This uses the existing early-opening graph and a permitted decreasing service
order, from its initialized state. It refutes unconditional restoration of
the original graph choice menu after own deviations; it is not an equilibrium
impossibility for a source environment that retains pending proposals.
-/

noncomputable section

namespace Vegas.Examples.CommunicationServiceRecovery

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime
open ReactiveEarlyOpening

private def record (before after : app.Execution) (command : app.Command) : app.Execution :=
  { after with environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment app, command⟩] }

def root : app.Execution := .initial app (State.initial input)
def sideSubmitted : app.Execution := (activated root).respond app () first
private def wireWait : app.Execution := record sideSubmitted sideSubmitted .wait
private def reservedWait : app.Execution := record wireWait wireWait .wait
def atBinding : app.Execution :=
  record reservedWait reservedWait (.application (.executeSample 1))
def recoverySubmitted : app.Execution := (activated atBinding).respond app () bindingAction
def installed : app.Execution := record recoverySubmitted
  (recoverySubmitted.includePending app ((), 0)) (.include ((), 0))
def final : app.Execution := record installed (installed.includePending app ((), 1))
  (.include ((), 1))

def network : runtime.NetworkPolicy leaks := fun history _ =>
  PMF.pure (if history.length < 5 then .wait else .include ((), 0))

def players : Unit → app.Policy := fun _ history view =>
  if history = [] then PMF.pure first else compiled history view

theorem ready : atBinding.application.config.cut.Ready 0 := by decide
theorem timely : atBinding.application.WithinDeadline runtime 0 := by change 0 < 2; decide

/-- The old proposal was already authorized when sent. Submission dependency
checks therefore do not remove this competing binding. -/
theorem earlier_authorized :
    recoverySubmitted.AuthorizedAtSubmission app (runtime.submissionDependencyCondition leaks)
      ⟨((), 0), ⟨.commitment 0 ((), .prepared 0), none, some ⟨0⟩⟩⟩ := by
  refine ⟨⟨(activated root).observe app (), first,
    some ⟨((), 0), ⟨.commitment 0 ((), .prepared 0), none, some ⟨0⟩⟩⟩⟩, rfl, rfl, ?_⟩
  intro event addressed predecessor member
  have same : (0 : graph.EventId) = event := Option.some.inj addressed
  subst event
  exact False.elim (Finset.notMem_empty predecessor member)

private theorem idle_step (instruction : ServiceInstruction graph) (command : app.Command)
    (execution : app.Execution)
    (selected : runtime.interactionInstruction leaks network execution.environmentRecall
      (execution.observeEnvironment app) instruction = PMF.pure command)
    (noActor : command.actor? app = none)
    (stutter : execution.environmentStep app command =
      PMF.pure (record execution execution command)) :
    runtime.interactionStep leaks players network instruction execution =
      PMF.pure (record execution execution command) := by
  simp only [interactionStep, selected, PMF.pure_bind, ReactiveApplication.dispatch,
    stutter, noActor, ReactiveApplication.resume, PMF.pure_bind]

private theorem wait_step (instruction : ServiceInstruction graph) (execution : app.Execution)
    (selected : runtime.interactionInstruction leaks network execution.environmentRecall
      (execution.observeEnvironment app) instruction = PMF.pure .wait) :
    runtime.interactionStep leaks players network instruction execution =
      PMF.pure (record execution execution .wait) := by
  apply idle_step instruction .wait execution selected rfl
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

theorem side_prefix :
    runtime.runInteractionPlan leaks players network (interactionVisit 1 1) root =
      PMF.pure atBinding := by
  have firstStep : runtime.interactionStep leaks players network (.player ()) root =
      PMF.pure sideSubmitted := by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind,
      ReactiveApplication.dispatch, activation, PMF.pure_bind,
      ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      ReactiveApplication.invoke]
    change (PMF.pure first).map _ = _
    rw [PMF.pure_map]
    rfl
  have firstWait := wait_step .wire sideSubmitted (by
    change (PMF.pure NetworkChoice.wait).map _ = _
    rw [PMF.pure_map]
    rfl)
  let afterWait := record sideSubmitted sideSubmitted .wait
  have secondWait := wait_step (.includeLatest 1 ()) afterWait rfl
  let beforeSample := record afterWait afterWait .wait
  have sample := idle_step (.sample 1) (.application (.executeSample 1)) beforeSample rfl rfl (by
    have unready : ¬ beforeSample.application.config.cut.Ready 1 := by decide
    simp only [ReactiveApplication.Execution.environmentStep, app, reactiveApplication,
      environmentStep_executeSample_of_not_ready runtime _ _ unready, PMF.pure_map]
    rfl)
  dsimp only [afterWait] at secondWait
  dsimp only [beforeSample, afterWait] at sample
  change runtime.runInteractionPlan leaks players network
    [.player (), .wire, .includeLatest 1 (), .sample 1] root = _
  simp only [runInteractionPlan, firstStep, firstWait, secondWait,
    sample, PMF.pure_bind]
  rfl

theorem compiled_response :
    compiled ((activated atBinding).recall ()) ((activated atBinding).observe app ()) =
      PMF.pure bindingAction := by
  have incompatible : ¬ (runtime.prescribedReactivePolicy leaks () zeroPolicy).Consistent
      ((activated atBinding).recall ()) := by
    intro consistent
    change ReactiveApplication.Policy.Consistent _ ([] ++ [_]) at consistent
    have supported := (ReactiveApplication.Policy.consistent_snoc_iff _ [] _).mp consistent
    have selected := supported.2
    have turn : ((activated root).observe app ()).application.publicView.ownTurn? () =
        some 0 := by
      decide
    have readyZero :
        ((activated root).observe app ()).application.publicView.EventReady 0 := by
      decide
    have actor : graph.actor? 0 = some () := rfl
    change first ∈ (runtime.prescribedReactivePolicy leaks () zeroPolicy []
      ((activated root).observe app ())).support at selected
    rw [prescribedReactivePolicy_apply] at selected
    simp only [prescribedReactiveResponse, turn, reactiveAlreadySubmitted, List.any_nil,
      Bool.false_eq_true, ite_false, dite_true, ite_eq_left readyZero, dite_eq_left actor,
      EventGraph.normalizePolicy, zeroPolicy, Fin.cases_zero, PMF.pure_map, PMF.bind_const,
      PMF.mem_support_pure_iff _ _] at selected
    have sent := congrArg ReactiveApplication.Action.transmission selected
    have slot :
        reactiveFreshSlot ((activated root).observe app ()).application = some 0 := by
      unfold reactiveFreshSlot
      split
      · congr 1
        exact (Nat.find_eq_zero _).mpr rfl
      · rename_i impossible
        exact False.elim (impossible ⟨0, rfl⟩)
    change some (ReactiveApplication.Transmission.submit (app := app)
        ⟨⟨.commitment 0 ((), .prepared 0), some ⟨.int, 1⟩⟩, .none⟩) =
      (reactiveFreshSlot ((activated root).observe app ()).application).map _ at sent
    rw [slot] at sent
    have material := ReactiveApplication.Transmission.submit.inj (Option.some.inj sent)
    have opening := congrArg
      (fun submission : WitnessedSubmission graph => submission.call.opening) material
    have raw := Option.some.inj opening
    have value := congrArg (fun raw : Raw simpleExpr => raw.as? .int) raw
    cases value
  rw [compiled, compileReactivePolicy, ReactiveApplication.Policy.recover_eq_recovery _ _ _ _
    incompatible]
  have turn : ((activated atBinding).observe app ()).application.publicView.ownTurn? () =
      some 0 := by
    decide
  have readyView : ((activated atBinding).observe app ()).application.publicView.EventReady 0 :=
    by decide
  have actor : graph.actor? 0 = some () := rfl
  rw [recoverReactivePolicy_apply]
  simp only [recoverReactiveResponse, turn, dite_true, ite_eq_left readyView,
    dite_eq_left actor, EventGraph.normalizePolicy, zeroPolicy, Fin.cases_zero,
    reactiveRecoveryLaw_pure (graph := graph), PMF.pure_map, PMF.bind_const]
  change PMF.pure (ReactiveApplication.Action.mk (app := app)
    ((reactiveFreshSlot ((activated atBinding).observe app ()).application).map _)) = _
  have slot : reactiveFreshSlot ((activated atBinding).observe app ()).application = some 1 := by
    unfold reactiveFreshSlot
    split
    · congr 1
      apply (Nat.find_eq_iff _).mpr
      refine ⟨rfl, ?_⟩
      intro index less
      have zero : index = 0 := by omega
      subst index
      intro impossible
      cases impossible
    · rename_i impossible
      exact False.elim (impossible ⟨1, rfl⟩)
  rw [slot]
  rfl

theorem recovery_block : runtime.runInteractionPlan leaks players network
    [.player (), .wire, .includeLatest 0 ()] atBinding = PMF.pure final := by
  have playerStep : runtime.interactionStep leaks players network (.player ()) atBinding =
      PMF.pure recoverySubmitted := by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind,
      ReactiveApplication.dispatch, activation, PMF.pure_bind,
      ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      ReactiveApplication.invoke]
    have notEmpty : (activated atBinding).recall () ≠ [] := by decide
    simp only [players, notEmpty, ↓reduceIte, compiled_response, PMF.pure_map]
    rfl
  have wireCommand : runtime.interactionInstruction leaks network
      recoverySubmitted.environmentRecall (recoverySubmitted.observeEnvironment app) .wire =
        PMF.pure (.include ((), 0)) := by
    change (PMF.pure (NetworkChoice.include ((), 0))).map _ = _
    rw [PMF.pure_map]
    rfl
  have wireStep : runtime.interactionStep leaks players network .wire recoverySubmitted =
      PMF.pure installed := by
    simp only [interactionStep, wireCommand, PMF.pure_bind, ReactiveApplication.dispatch,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind,
      ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  have select : runtime.reactiveLatest leaks 0 () (installed.observeEnvironment app) =
      .include ((), 1) := rfl
  have includeStep : runtime.interactionStep leaks players network (.includeLatest 0 ()) installed =
      PMF.pure final := by
    simp only [interactionStep, interactionInstruction, select, PMF.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
      ReactiveApplication.resume]
    rfl
  simp only [runInteractionPlan, playerStep, wireStep, includeStep, PMF.pure_bind]

theorem installed_value : installed.application.config.outputs 0 = some (.success 1) := by
  have application : installed.application = (included true false).application := rfl
  rw [application, included_state true false (by simp)]
  exact EventGraph.Config.complete_output_same ..

theorem recovery_rejected :
    handle runtime installed.application ⟨((), 1), .commitment 0 ((), .prepared 1)⟩ = none := by
  have application : installed.application = (included true false).application := rfl
  rw [application, included_state true false (by simp)]
  have completed : 0 ∈ (boundState true false).config.cut.completed := by decide
  have unavailable : ¬ (boundState true false).config.cut.Ready 0 := fun valid => valid.1 completed
  simp only [handle, unavailable, ↓reduceDIte]

theorem final_value : final.application.config.outputs 0 = some (.success 1) :=
  (runtime.reactiveStoreInvariant leaks (.inr 0) (.success 1)).includePending
    installed ((), 1) installed_value

def servicePrefix : List (ServiceInstruction graph) :=
  interactionVisit 1 1 ++ [.player (), .wire, .includeLatest 0 ()]

theorem prefix_law : runtime.runInteractionPlan leaks players network servicePrefix root =
    PMF.pure final := by
  change runtime.runInteractionPlan leaks players network
    (interactionVisit 1 1 ++ [.player (), .wire, .includeLatest 0 ()]) root = _
  rw [runInteractionPlan_append, side_prefix, PMF.pure_bind, recovery_block]

theorem epoch_split : interactionEpoch (ServiceOrder.decreasing graph) 1 =
    servicePrefix ++ [.sample 0, .tick, .expire 0, .expire 1] := rfl

theorem epoch_stores_earlier (next : app.Execution)
    (reached : next ∈ (runtime.runInteractionPlan leaks players network
      (interactionEpoch (ServiceOrder.decreasing graph) 1) root).support) :
    next.application.config.outputs 0 = some (.success 1) := by
  rw [epoch_split, runInteractionPlan_append, prefix_law, PMF.pure_bind] at reached
  rw [← runtime.interactionSuffix_rounds leaks (ServiceOrder.decreasing graph) 1 players network
    servicePrefix [.sample 0, .tick, .expire 0, .expire 1] epoch_split 0 final (by rfl)] at reached
  have preserved := ReactiveApplication.Invariant.policyInvariant app
    (runtime.reactiveStoreInvariant leaks (.inr 0) (.success 1)) players
  exact preserved.runRounds _ _ final next final_value reached

/-- An exact initialized law of the existing recurring scheduler. Only the
first response deviates; subsequent responses use the actual recovery compiler. -/
theorem recurring_result :
    (app.runRounds (runtime.interactionScheduler leaks (ServiceOrder.decreasing graph) 1 network)
      players (interactionEpoch (ServiceOrder.decreasing graph) 1).length root).map
        (fun execution => execution.application.config.outputs 0) =
          PMF.pure (some (.success 1)) := by
  rw [runtime.interactionSuffix_rounds leaks (ServiceOrder.decreasing graph) 1 players network
    [] (interactionEpoch (ServiceOrder.decreasing graph) 1) (by simp) 0 root (by rfl)]
  calc
    _ = (runtime.runInteractionPlan leaks players network
        (interactionEpoch (ServiceOrder.decreasing graph) 1) root).map
          (fun _ => some (.success (1 : Int))) :=
      map_congr_on_support _ epoch_stores_earlier
    _ = _ := PMF.map_const _ _

end Vegas.Examples.CommunicationServiceRecovery
