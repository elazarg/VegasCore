/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedPrefix
import VegasTests.SelectiveAssociationRestrictedBinding
import Interaction.ReactiveTraceDepth

/-! # Behavioral history laws at the two native guessing sites

The response tuple laws are projections of the original finite-menu protocol
at its actual decision depths. These equations support conditioning on the
existing information sets without constructing another game.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.Prefix

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def aliceControl (responses : app.Action × app.Action) : app.ProtocolState :=
  some ⟨85, some alice, aliceInput responses.1 responses.2⟩

def carolControl (responses : CarolResponses) : app.ProtocolState :=
  some ⟨80, some carol, carolInput responses⟩

def bobControl (responses : BobResponses) : app.ProtocolState :=
  some ⟨74, some bob, bobInput responses⟩

def decisionDepth (event : nativeGraph.EventId) : Nat :=
  1 + ((nativeBeforeResponse event).length + 1) +
    ∑ who, nativeResponseCount who (nativeBeforeResponse event)

theorem decision_depth (event : nativeGraph.EventId) (control : app.Control)
    (trace : arena.Trace (some control)) (who : Player) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some event) :
    trace.length = decisionDepth event := by
  rw [← menu.toRawTrace_length (FinDist.pure nativeInitial) nativeHorizon scheduler trace,
    app.trace_length_of_control]
  rw [(native_decision_cursor (observation := leaks) event control trace who active granted).2]
  apply congrArg (fun count => 1 + ((nativeBeforeResponse event).length + 1) + count)
  apply Finset.sum_congr rfl
  intro observer _
  exact native_decision_recall_count (observation := leaks) event control trace who active
    granted observer

theorem carol_depth : decisionDepth carolBinding = 13 := by decide
theorem bob_depth : decisionDepth bobBinding = 20 := by decide

private theorem step_initial (players : Player → app.Policy) :
    app.controlStep (FinDist.pure nativeInitial) nativeHorizon scheduler players none =
      FinDist.pure (some ⟨89, none, initial⟩) := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_none,
    ReactiveApplication.transition, FinDist.map_pure]
  rfl

theorem step_player (players : Player → app.Policy) (execution : app.Execution)
    (remaining : Nat) (who : Player) :
    app.controlStep (FinDist.pure nativeInitial) nativeHorizon scheduler players
      (some ⟨remaining, some who, execution⟩) =
      (players who (execution.recall who) (execution.observe app who)).map fun action =>
        some ⟨remaining, none, execution.respond app who action⟩ := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
    ReactiveApplication.transition, ite_true, Option.getD_some, FinDist.map_eq_bind]

theorem step_environment (players : Player → app.Policy) (execution : app.Execution)
    (remaining : Nat) :
    app.controlStep (FinDist.pure nativeInitial) nativeHorizon scheduler players
      (some ⟨remaining + 1, none, execution⟩) =
      (scheduler execution.environmentRecall (execution.observeEnvironment app)).map fun command =>
        some ⟨remaining, command.actor? app, environmentResult execution command⟩ := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
    ReactiveApplication.transition, environmentResult_law, FinDist.map_eq_bind, FinDist.pure_bind]

theorem prefix_lookup (index : Nat) (early : index < 15) :
    nativePlan[index]? =
      ([.player alice, .player bob, .grant aliceBinding, .player alice,
        .includeLatest aliceBinding alice, .tick, .expire aliceBinding, .grant carolBinding,
        .player carol, .includeLatest carolBinding carol, .tick, .tick,
        .expire carolBinding, .grant bobBinding, .player bob] :
          List (ServiceInstruction nativeGraph))[index]? := by
  have front : nativePlan.take 15 =
      [.player alice, .player bob, .grant aliceBinding, .player alice,
        .includeLatest aliceBinding alice, .tick, .expire aliceBinding, .grant carolBinding,
        .player carol, .includeLatest carolBinding carol, .tick, .tick,
        .expire carolBinding, .grant bobBinding, .player bob] := rfl
  rw [← front, List.getElem?_take_of_lt early]

theorem activation_recall (execution : app.Execution) (who : Player) :
    (activate execution who).environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate who⟩] := rfl

theorem selection_passive (event : nativeGraph.EventId) (who : Player)
    (execution : app.Execution) :
    (nativeRuntime.reactiveLatest leaks event who (execution.observeEnvironment app)).actor? app =
      none := by
  unfold reactiveLatest
  split <;> rfl

theorem activation_actor (who : Player) :
    (ReactiveApplication.Command.activate who).actor? app = some who := rfl

theorem application_actor (command : EnvironmentCommand nativeGraph) :
    (ReactiveApplication.Command.application command).actor? app = none := rfl

theorem alice_control_law (players : Player → app.Policy) :
    (fun distribution => distribution.bind
      (app.controlStep (FinDist.pure nativeInitial) nativeHorizon scheduler players))^[7]
        (FinDist.pure none) = (preludeLaw players).map aliceControl := by
  simp (disch := decide) only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    FinDist.pure_bind, step_initial, step_player, step_environment, scheduler, serviceScheduler,
    ReactiveApplication.respond_environmentRecall, environmentResult_recall, activation_recall,
    initial, ReactiveApplication.Execution.initial, List.length_nil, List.length_append,
    List.length_singleton, Nat.zero_add, prefix_lookup, List.getElem?_cons_zero,
    List.getElem?_cons_succ, interactionInstruction, FinDist.map_pure, FinDist.bind_map,
    FinDist.bind_bind, FinDist.map_bind, environmentResult_activate,
    activation_actor, application_actor, preludeLaw, FinDist.map_comp]
  rfl

theorem carol_control_law (players : Player → app.Policy) :
    (fun distribution => distribution.bind
      (app.controlStep (FinDist.pure nativeInitial) nativeHorizon scheduler players))^[13]
        (FinDist.pure none) = (carolLaw players).map carolControl := by
  simp (disch := decide) only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    FinDist.pure_bind, step_initial, step_player, step_environment, scheduler, serviceScheduler,
    ReactiveApplication.respond_environmentRecall, environmentResult_recall, activation_recall,
    initial, ReactiveApplication.Execution.initial, List.length_nil, List.length_append,
    List.length_singleton, Nat.zero_add, prefix_lookup, List.getElem?_cons_zero,
    List.getElem?_cons_succ, interactionInstruction, FinDist.map_pure, FinDist.bind_map,
    FinDist.bind_bind, FinDist.map_bind, environmentResult_activate,
    activation_actor, application_actor, selection_passive, carolLaw, FinDist.map_comp]
  rfl

theorem bob_control_law (players : Player → app.Policy) :
    (fun distribution => distribution.bind
      (app.controlStep (FinDist.pure nativeInitial) nativeHorizon scheduler players))^[20]
        (FinDist.pure none) = (bobLaw players).map bobControl := by
  simp (disch := decide) only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    FinDist.pure_bind, step_initial, step_player, step_environment, scheduler, serviceScheduler,
    ReactiveApplication.respond_environmentRecall, environmentResult_recall, activation_recall,
    initial, ReactiveApplication.Execution.initial, List.length_nil, List.length_append,
    List.length_singleton, Nat.zero_add, prefix_lookup, List.getElem?_cons_zero,
    List.getElem?_cons_succ, interactionInstruction, FinDist.map_pure, FinDist.bind_map,
    FinDist.bind_bind, FinDist.map_bind, environmentResult_activate,
    activation_actor, application_actor, selection_passive, bobLaw, carolLaw, FinDist.map_comp]
  rfl

theorem alice_history_law (players : Profile model.behavioralSignature) :
    (model.runBehavioral players 7).map ExecutionProtocol.History.state =
      (preludeLaw (menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler
        players)).map aliceControl := by
  rw [InformationModel.runBehavioral, menu.run_map_controlStep]
  exact alice_control_law _

theorem carol_history_law (players : Profile model.behavioralSignature) :
    (model.runBehavioral players 13).map ExecutionProtocol.History.state =
      (carolLaw (menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler
        players)).map carolControl := by
  rw [InformationModel.runBehavioral, menu.run_map_controlStep]
  exact carol_control_law _

theorem bob_history_law (players : Profile model.behavioralSignature) :
    (model.runBehavioral players 20).map ExecutionProtocol.History.state =
      (bobLaw (menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler
        players)).map bobControl := by
  rw [InformationModel.runBehavioral, menu.run_map_controlStep]
  exact bob_control_law _

theorem alice_legal (players : Profile model.behavioralSignature)
    (responses : app.Action × app.Action)
    (supported : responses ∈ (preludeLaw (menu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon scheduler players)).support) :
    Nonempty (arena.Trace (aliceControl responses)) := by
  have reached : aliceControl responses ∈
      ((model.runBehavioral players 7).map ExecutionProtocol.History.state).support := by
    rw [alice_history_law, FinDist.support_map]
    exact ⟨responses, supported, rfl⟩
  obtain ⟨history, _, same⟩ := FinDist.support_map .. ▸ reached
  exact ⟨same ▸ history.trace⟩

theorem carol_legal (players : Profile model.behavioralSignature) (responses : CarolResponses)
    (supported : responses ∈ (carolLaw (menu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon scheduler players)).support) :
    Nonempty (arena.Trace (carolControl responses)) := by
  have reached : carolControl responses ∈
      ((model.runBehavioral players 13).map ExecutionProtocol.History.state).support := by
    rw [carol_history_law, FinDist.support_map]
    exact ⟨responses, supported, rfl⟩
  obtain ⟨history, _, same⟩ := FinDist.support_map .. ▸ reached
  exact ⟨same ▸ history.trace⟩

theorem bob_legal (players : Profile model.behavioralSignature) (responses : BobResponses)
    (supported : responses ∈ (bobLaw (menu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon scheduler players)).support) :
    Nonempty (arena.Trace (bobControl responses)) := by
  have reached : bobControl responses ∈
      ((model.runBehavioral players 20).map ExecutionProtocol.History.state).support := by
    rw [bob_history_law, FinDist.support_map]
    exact ⟨responses, supported, rfl⟩
  obtain ⟨history, _, same⟩ := FinDist.support_map .. ▸ reached
  exact ⟨same ▸ history.trace⟩

theorem carol_support_prelude (players : Player → app.Policy) (responses : CarolResponses)
    (supported : responses ∈ (carolLaw players).support) :
    (responses.alicePrelude, responses.bobPrelude) ∈ (preludeLaw players).support := by
  obtain ⟨first, firstMem, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨second, secondMem, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨third, _, same⟩ := FinDist.support_map .. ▸ reached
  subst responses
  rw [preludeLaw, FinDist.support_bind]
  apply Set.mem_iUnion₂.mpr ⟨first, firstMem, ?_⟩
  exact FinDist.support_map .. ▸ ⟨second, secondMem, rfl⟩

theorem bob_support_carol (players : Player → app.Policy) (responses : BobResponses)
    (supported : responses ∈ (bobLaw players).support) :
    responses.beforeCarol ∈ (carolLaw players).support := by
  obtain ⟨first, firstMem, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨second, _, same⟩ := FinDist.support_map .. ▸ reached
  exact congrArg BobResponses.beforeCarol same ▸ firstMem

theorem aliceInput_granted (first second : app.Action) :
    (aliceInput first second).application.serviceGrant = some aliceBinding := by
  simp only [aliceInput, environmentResult_grant, activate, granted]

theorem carolInput_preserves {predicate : app.State → Prop}
    (invariant : app.Invariant predicate) (responses : CarolResponses)
    (valid : predicate (includeLatest
      ((aliceInput responses.alicePrelude responses.bobPrelude).respond app alice
        responses.aliceBinding) aliceBinding alice).application) :
    predicate (carolInput responses).application := by
  exact environmentResult_preserves invariant _ _
    (environmentResult_preserves invariant _ _
      (environmentResult_preserves invariant _ _ valid))

theorem bobInput_preserves {predicate : app.State → Prop}
    (invariant : app.Invariant predicate) (responses : BobResponses)
    (valid : predicate (carolInput responses.beforeCarol).application) :
    predicate (bobInput responses).application := by
  exact environmentResult_preserves invariant _ _
    (environmentResult_preserves invariant _ _
      (environmentResult_preserves invariant _ _
        (environmentResult_preserves invariant _ _
          (environmentResult_preserves invariant _ _
            (invariant.respond _ carol responses.carolBinding valid)))))

/-- The prescribed fresh correction rules out a true Alice binding, even
after arbitrary earlier raw responses and subsequent maintenance steps. -/
theorem carol_prescribed_alice_false (players : Profile model.behavioralSignature)
    (responses : CarolResponses)
    (supported : responses ∈ (carolLaw (menu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon scheduler players)).support)
    (prescribed : responses.aliceBinding = response alice
      ((aliceInput responses.alicePrelude responses.bobPrelude).observe app alice)) :
    aliceBindingRef.get? (carolInput responses).application.config.store =
      some (.success false) := by
  obtain ⟨trace⟩ := alice_legal players _ (carol_support_prelude _ responses supported)
  let control : app.Control :=
    ⟨85, some alice, aliceInput responses.alicePrelude responses.bobPrelude⟩
  have grant : control.execution.application.serviceGrant = some (nativeBindingEvent alice) :=
    aliceInput_granted _ _
  have unfinished := native_decision_unfinished (observation := leaks) (nativeBindingEvent alice)
    control trace alice rfl grant
  obtain ⟨next, stored, law⟩ :=
    correctiveBinding_realizes policy control trace alice rfl grant unfinished false
  have selected : responses.aliceBinding = correctiveBinding alice aliceBinding false
      (control.execution.observe app alice) :=
    prescribed.trans (response_binds alice _ grant)
  rw [include_step, FinDist.map_pure] at law
  have same := FinDist.mem_support_pure.mp (law ▸ FinDist.mem_support_pure.mpr rfl)
  apply carolInput_preserves (binding_invariant alice (.success false)) responses
  change aliceBindingRef.get?
    (includeLatest (control.execution.respond app alice responses.aliceBinding)
      aliceBinding alice).application.config.store = some (.success false)
  rw [selected]
  exact (congrArg (fun state : app.State => aliceBindingRef.get? state.config.store) same).trans
    stored

theorem carol_true_response_different (players : Profile model.behavioralSignature)
    (responses : CarolResponses)
    (supported : responses ∈ (carolLaw (menu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon scheduler players)).support)
    (trueBinding : aliceBindingRef.get? (carolInput responses).application.config.store =
      some (.success true)) :
    responses.aliceBinding ≠ response alice
      ((aliceInput responses.alicePrelude responses.bobPrelude).observe app alice) := by
  intro prescribed
  have falseBinding := carol_prescribed_alice_false players responses supported prescribed
  rw [trueBinding] at falseBinding
  cases falseBinding

theorem bob_true_response_different (players : Profile model.behavioralSignature)
    (responses : BobResponses)
    (supported : responses ∈ (bobLaw (menu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon scheduler players)).support)
    (trueBinding : aliceBindingRef.get? (bobInput responses).application.config.store =
      some (.success true)) :
    responses.beforeCarol.aliceBinding ≠ response alice
      ((aliceInput responses.beforeCarol.alicePrelude responses.beforeCarol.bobPrelude).observe
        app alice) := by
  intro prescribed
  have falseBinding := carol_prescribed_alice_false players responses.beforeCarol
    (bob_support_carol _ responses supported) prescribed
  have persistent := bobInput_preserves (binding_invariant alice (.success false)) responses
    falseBinding
  change aliceBindingRef.get? _ = some (.success false) at persistent
  rw [trueBinding] at persistent
  cases persistent

end VegasTests.SelectiveAssociation.Restricted.Prefix
