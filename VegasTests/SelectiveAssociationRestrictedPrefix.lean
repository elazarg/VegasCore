/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedInitial
import Interaction.ReactiveResponseKernel

/-! # Raw responses before the restricted guessing decisions

These tuples record the three or four responses preceding the two guessing
sites. Their evaluation uses the actual native environment transitions. The
factorization theorems retain every raw response and its original probability.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.Prefix

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

private theorem sample_inert (state : State nativeGraph) (event : nativeGraph.EventId) :
    environmentStep nativeRuntime state (.executeSample event) = FinDist.pure state := by
  by_cases ready : state.config.cut.Ready event
  · apply environmentStep_executeSample_of_nonsample nativeRuntime state event ready
    intro payload law outputEq codeEq view
    fin_cases event <;> cases view
  · exact environmentStep_executeSample_of_not_ready nativeRuntime state event ready

theorem environment_pure (execution : app.Execution) (command : app.Command) :
    ∃ next, execution.environmentStep app command = FinDist.pure next := by
  cases command with
  | activate who => exact ⟨activate execution who, activation_law execution who⟩
  | wait | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
      exact ⟨_, rfl⟩
  | application command =>
      cases command with
      | grant event | advanceClock | expire event =>
          simp only [ReactiveApplication.Execution.environmentStep, app, serviceApp,
            reactiveApplication, environmentStep, FinDist.map_pure]
          exact ⟨_, rfl⟩
      | executeSample event =>
          simp only [ReactiveApplication.Execution.environmentStep, app, serviceApp,
            reactiveApplication, sample_inert, FinDist.map_pure]
          exact ⟨_, rfl⟩

/-- The unique point of the existing deterministic environment law. -/
def environmentResult (execution : app.Execution) (command : app.Command) : app.Execution :=
  (environment_pure execution command).choose

theorem environmentResult_law (execution : app.Execution) (command : app.Command) :
    execution.environmentStep app command = FinDist.pure (environmentResult execution command) :=
  (environment_pure execution command).choose_spec

theorem environmentResult_eq (execution : app.Execution) (command : app.Command)
    (next : app.Execution) (law : execution.environmentStep app command = FinDist.pure next) :
    environmentResult execution command = next := by
  have same := (environmentResult_law execution command).symm.trans law
  exact FinDist.mem_support_pure.mp (same ▸ FinDist.mem_support_pure.mpr rfl)

theorem environmentResult_application_law (execution : app.Execution)
    (command : EnvironmentCommand nativeGraph) :
    app.environment execution.application command =
      FinDist.pure (environmentResult execution (.application command)).application := by
  have law := congrArg (fun distribution : FinDist app.Execution =>
    distribution.map (fun result => result.application))
      (environmentResult_law execution (.application command))
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_comp,
    Function.comp_def, FinDist.map_pure] at law
  have identity : (app.environment execution.application command).map
      (fun state : app.State => state) = app.environment execution.application command :=
    FinDist.map_id _
  exact identity.symm.trans law

theorem environmentResult_recall (execution : app.Execution) (command : app.Command) :
    (environmentResult execution command).environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] := by
  have reached : environmentResult execution command ∈
      (execution.environmentStep app command).support := by
    rw [environmentResult_law]
    exact FinDist.mem_support_pure.mpr rfl
  obtain ⟨middle, _, same⟩ := FinDist.support_map .. ▸ reached
  exact congrArg ReactiveApplication.Execution.environmentRecall same.symm

theorem environmentResult_activate (execution : app.Execution) (who : Player) :
    environmentResult execution (.activate who) = activate execution who :=
  environmentResult_eq execution _ _ (activation_law execution who)

theorem environmentResult_preserves {predicate : app.State → Prop}
    (invariant : app.Invariant predicate) (execution : app.Execution) (command : app.Command)
    (valid : predicate execution.application) :
    predicate (environmentResult execution command).application := by
  apply invariant.environmentStep execution _ command valid
  rw [environmentResult_law]
  exact FinDist.mem_support_pure.mpr rfl

theorem environmentResult_grant (execution : app.Execution) (event : nativeGraph.EventId) :
    environmentResult execution (.application (.grant event)) = granted execution event := by
  apply environmentResult_eq
  simp only [ReactiveApplication.Execution.environmentStep, app, serviceApp,
    reactiveApplication, environmentStep, FinDist.map_pure, granted]

def includeLatest (execution : app.Execution) (event : nativeGraph.EventId) (who : Player) :
    app.Execution :=
  environmentResult execution
    (nativeRuntime.reactiveLatest leaks event who (execution.observeEnvironment app))

private theorem passive_step (players : Player → app.Policy) (execution : app.Execution)
    (instruction : ServiceInstruction nativeGraph) (command : app.Command)
    (selected : nativeRuntime.interactionInstruction leaks network execution.environmentRecall
      (execution.observeEnvironment app) instruction = FinDist.pure command)
    (passive : command.actor? app = none) :
    nativeRuntime.interactionStep leaks players network instruction execution =
      FinDist.pure (environmentResult execution command) := by
  simp only [interactionStep, selected, FinDist.pure_bind, ReactiveApplication.dispatch,
    environmentResult_law, FinDist.pure_bind, passive, ReactiveApplication.resume]

theorem grant_step (players : Player → app.Policy) (execution : app.Execution)
    (event : nativeGraph.EventId) :
    nativeRuntime.interactionStep leaks players network (.grant event) execution =
      FinDist.pure (environmentResult execution (.application (.grant event))) :=
  passive_step players execution _ _ rfl rfl

theorem tick_step (players : Player → app.Policy) (execution : app.Execution) :
    nativeRuntime.interactionStep leaks players network .tick execution =
      FinDist.pure (environmentResult execution (.application .advanceClock)) :=
  passive_step players execution _ _ rfl rfl

theorem expire_step (players : Player → app.Policy) (execution : app.Execution)
    (event : nativeGraph.EventId) :
    nativeRuntime.interactionStep leaks players network (.expire event) execution =
      FinDist.pure (environmentResult execution (.application (.expire event))) :=
  passive_step players execution _ _ rfl rfl

theorem include_step (players : Player → app.Policy) (execution : app.Execution)
    (event : nativeGraph.EventId) (who : Player) :
    nativeRuntime.interactionStep leaks players network (.includeLatest event who) execution =
      FinDist.pure (includeLatest execution event who) := by
  apply passive_step players execution _ _ rfl
  unfold reactiveLatest
  split <;> rfl

theorem player_step (players : Player → app.Policy) (execution : app.Execution) (who : Player) :
    nativeRuntime.interactionStep leaks players network (.player who) execution =
      (players who (execution.recall who) (execution.observe app who)).map
        (fun response => (activate execution who).respond app who response) := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, activation_law, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke]
  rfl

structure CarolResponses where
  alicePrelude : app.Action
  bobPrelude : app.Action
  aliceBinding : app.Action

structure BobResponses where
  beforeCarol : CarolResponses
  carolBinding : app.Action

def bobPreludeInput (first : app.Action) : app.Execution :=
  activate ((activate initial alice).respond app alice first) bob

def aliceInput (first second : app.Action) : app.Execution :=
  activate (environmentResult ((bobPreludeInput first).respond app bob second)
    (.application (.grant aliceBinding))) alice

def carolInput (responses : CarolResponses) : app.Execution :=
  let submitted := (aliceInput responses.alicePrelude responses.bobPrelude).respond app alice
    responses.aliceBinding
  let included := includeLatest submitted aliceBinding alice
  let ticked := environmentResult included (.application .advanceClock)
  let expired := environmentResult ticked (.application (.expire aliceBinding))
  activate (environmentResult expired (.application (.grant carolBinding))) carol

def bobInput (responses : BobResponses) : app.Execution :=
  let submitted := (carolInput responses.beforeCarol).respond app carol responses.carolBinding
  let included := includeLatest submitted carolBinding carol
  let firstTick := environmentResult included (.application .advanceClock)
  let secondTick := environmentResult firstTick (.application .advanceClock)
  let expired := environmentResult secondTick (.application (.expire carolBinding))
  activate (environmentResult expired (.application (.grant bobBinding))) bob

def preludeLaw (players : Player → app.Policy) : FinDist (app.Action × app.Action) :=
  (players alice (initial.recall alice) (initial.observe app alice)).bind fun first =>
    let beforeBob := bobPreludeInput first
    (players bob (beforeBob.recall bob) (beforeBob.observe app bob)).map
      fun second => (first, second)

def carolLaw (players : Player → app.Policy) : FinDist CarolResponses :=
  (players alice (initial.recall alice) (initial.observe app alice)).bind fun first =>
    let beforeBob := bobPreludeInput first
    (players bob (beforeBob.recall bob) (beforeBob.observe app bob)).bind fun second =>
      let beforeAlice := aliceInput first second
      (players alice (beforeAlice.recall alice) (beforeAlice.observe app alice)).map fun third =>
        ⟨first, second, third⟩

def bobLaw (players : Player → app.Policy) : FinDist BobResponses :=
  (carolLaw players).bind fun first =>
    let beforeCarol := carolInput first
    (players carol (beforeCarol.recall carol) (beforeCarol.observe app carol)).map fun second =>
      ⟨first, second⟩

def decisionLaw (players : Player → app.Policy) (event : nativeGraph.EventId) :
    FinDist app.Execution :=
  (nativeRuntime.runInteractionPlan leaks players network (nativeBeforeResponse event) initial).bind
    fun prior => prior.environmentStep app (.activate (nativeOwner event))

theorem carol_factorization (players : Player → app.Policy) :
    decisionLaw players carolBinding = (carolLaw players).map carolInput := by
  change ((nativeRuntime.runInteractionPlan leaks players network
    [.player alice, .player bob, .grant aliceBinding, .player alice,
      .includeLatest aliceBinding alice, .tick, .expire aliceBinding, .grant carolBinding]
      initial).bind fun prior => prior.environmentStep app (.activate carol)) = _
  simp only [runInteractionPlan, player_step, grant_step, tick_step, expire_step, include_step,
    FinDist.pure_bind, FinDist.bind_pure, FinDist.bind_map, FinDist.map_bind,
    FinDist.bind_bind, activation_law, carolLaw, FinDist.map_comp]
  rfl

theorem bob_factorization (players : Player → app.Policy) :
    decisionLaw players bobBinding = (bobLaw players).map bobInput := by
  change ((nativeRuntime.runInteractionPlan leaks players network
    [.player alice, .player bob, .grant aliceBinding, .player alice,
      .includeLatest aliceBinding alice, .tick, .expire aliceBinding, .grant carolBinding,
      .player carol, .includeLatest carolBinding carol, .tick, .tick,
      .expire carolBinding, .grant bobBinding]
      initial).bind fun prior => prior.environmentStep app (.activate bob)) = _
  simp only [runInteractionPlan, player_step, grant_step, tick_step, expire_step, include_step,
    FinDist.pure_bind, FinDist.bind_pure, FinDist.bind_map, FinDist.map_bind,
    FinDist.bind_bind, activation_law, bobLaw, carolLaw, FinDist.map_comp]
  rfl

end VegasTests.SelectiveAssociation.Restricted.Prefix
