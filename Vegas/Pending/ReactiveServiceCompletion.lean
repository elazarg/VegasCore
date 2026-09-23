/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.CompletionService

/-! # Completion of canonical reactive service

Every epoch services each ready chance event and every strategic event whose
deadline is due. The shared completion contract then supplies the finite bound.
The final theorem applies to canonical behavioral play with arbitrary players
and adaptive network choices, including further player activations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem runInteractionPlan_support_instruction (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (before after : List (ServiceInstruction graph)) (instruction : ServiceInstruction graph)
    (execution final : (runtime.reactiveApplication leaks).Execution)
    (supported : final ∈ (runtime.runInteractionPlan leaks players network
      (before ++ instruction :: after) execution).support) :
    ∃ prior ∈ (runtime.runInteractionPlan leaks players network before execution).support,
      ∃ next ∈ (runtime.interactionStep leaks players network instruction prior).support,
        final ∈ (runtime.runInteractionPlan leaks players network after next).support := by
  rw [runInteractionPlan_append] at supported
  obtain ⟨prior, priorMem, finalMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨next, nextMem, restMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ finalMem)
  exact ⟨prior, priorMem, next, nextMem, restMem⟩

omit [DecidableEq Player] in
theorem interactionEpoch_split_expire (chosen : ServiceOrder graph)
    (networkTurns : Nat) (event : graph.EventId) :
    ∃ before after, interactionEpoch chosen networkTurns =
      before ++ ServiceInstruction.expire event :: after ∧ serviceTicks before = 1 := by
  have member : ServiceInstruction.expire event ∈
      (List.finRange graph.order.eventCount).map ServiceInstruction.expire :=
    List.mem_map.mpr ⟨event, List.mem_finRange event, rfl⟩
  obtain ⟨expiryBefore, expiryAfter, expiryEq⟩ := List.mem_iff_append.mp member
  let sweep := chosen.val.flatMap (interactionVisit networkTurns)
  refine ⟨sweep ++ [.tick] ++ expiryBefore, expiryAfter, ?_, ?_⟩
  · simp only [interactionEpoch, expiryEq, List.append_assoc, sweep]
  · have expiryTicks : serviceTicks
        ((List.finRange graph.order.eventCount).map ServiceInstruction.expire) = 0 := by
      simp [serviceTicks, ServiceInstruction.ticks, Function.comp_def]
    rw [expiryEq, serviceTicks_append, serviceTicks_cons] at expiryTicks
    have sweepTicks : serviceTicks sweep = 0 := by
      dsimp only [sweep]
      induction chosen.val with
      | nil => rfl
      | cons event rest ih =>
          rw [List.flatMap_cons, serviceTicks_append, interactionVisit_ticks, ih]
    rw [serviceTicks_append, serviceTicks_append, sweepTicks]
    change 0 + 1 + serviceTicks expiryBefore = 1
    omega

omit [DecidableEq Player] in
theorem interactionEpoch_has_sample (chosen : ServiceOrder graph)
    (networkTurns : Nat) (event : graph.EventId) :
    ServiceInstruction.sample event ∈ interactionEpoch chosen networkTurns := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨event, chosen.mem event, ?_⟩
  simp [interactionVisit]

theorem reactive_application_support (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (command : EnvironmentCommand graph)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (supported : next ∈ ((runtime.reactiveApplication leaks).dispatch players
      (.application command) execution).support) :
    next.application ∈ (environmentStep runtime execution.application command).support := by
  change next ∈ ((execution.environmentStep (runtime.reactiveApplication leaks)
    (.application command)).bind FinDist.pure).support at supported
  rw [FinDist.bind_pure] at supported
  simp only [ReactiveApplication.Execution.environmentStep] at supported
  obtain ⟨updated, moved, rfl⟩ := FinDist.support_map .. ▸ supported
  obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ moved
  exact changed

theorem interactionStep_sample_complete (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (event : graph.EventId) (execution next : (runtime.reactiveApplication leaks).Execution)
    (ready : execution.application.config.cut.Ready event) (chance : graph.actor? event = none)
    (supported : next ∈
      (runtime.interactionStep leaks players network (.sample event) execution).support) :
    event ∈ next.application.config.cut.completed := by
  have moved : next ∈ ((runtime.reactiveApplication leaks).dispatch players
      (.application (.executeSample event)) execution).support := by
    simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using supported
  exact runtime.environmentStep_sample_complete _ _ event ready chance
    (runtime.reactive_application_support leaks players _ execution next moved)

theorem interactionStep_expire_complete (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (event : graph.EventId) (execution next : (runtime.reactiveApplication leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (strategic : (graph.actor? event).isSome = true)
    (entered : Nat) (activated : execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ execution.application.clock - entered)
    (supported : next ∈
      (runtime.interactionStep leaks players network (.expire event) execution).support) :
    event ∈ next.application.config.cut.completed := by
  have moved : next ∈ ((runtime.reactiveApplication leaks).dispatch players
      (.application (.expire event)) execution).support := by
    simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using supported
  exact runtime.environmentStep_expire_complete _ _ event ready strategic entered activated due
    (runtime.reactive_application_support leaks players _ execution next moved)

theorem interactionEpoch_chance_complete (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (event : graph.EventId) (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (ready : execution.application.config.cut.Ready event) (chance : graph.actor? event = none)
    (supported : next ∈ (runtime.runInteractionPlan leaks players network
      (interactionEpoch chosen networkTurns) execution).support) :
    event ∈ next.application.config.cut.completed := by
  obtain ⟨before, after, planEq⟩ :=
    List.mem_iff_append.mp (interactionEpoch_has_sample chosen networkTurns event)
  rw [planEq] at supported
  obtain ⟨prior, priorMem, sampled, sampledMem, afterMem⟩ :=
    runtime.runInteractionPlan_support_instruction leaks players network before after
      (.sample event) execution next supported
  have progress := runtime.runInteractionPlan_facts leaks inputs players network before
    execution prior invariant priorMem
  have sampledProgress := runtime.interactionStep_facts leaks inputs players network
    (.sample event)
    prior sampled progress.invariant sampledMem
  have suffix := runtime.runInteractionPlan_facts leaks inputs players network after
    sampled next sampledProgress.invariant afterMem
  rcases progress.ready_or_completed event ready with completed | priorReady
  · exact suffix.completed (sampledProgress.completed completed)
  · exact suffix.completed (runtime.interactionStep_sample_complete leaks players network event
      prior sampled priorReady chance sampledMem)

theorem interactionEpoch_strategic_complete (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (event : graph.EventId) (entered : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (ready : execution.application.config.cut.Ready event)
    (strategic : (graph.actor? event).isSome = true)
    (activated : execution.application.activatedAt event = some entered)
    (dueAfterTick : runtime.deadline event ≤ execution.application.clock + 1 - entered)
    (supported : next ∈ (runtime.runInteractionPlan leaks players network
      (interactionEpoch chosen networkTurns) execution).support) :
    event ∈ next.application.config.cut.completed := by
  obtain ⟨before, after, planEq, beforeTicks⟩ :=
    interactionEpoch_split_expire chosen networkTurns event
  rw [planEq] at supported
  obtain ⟨prior, priorMem, expired, expiredMem, afterMem⟩ :=
    runtime.runInteractionPlan_support_instruction leaks players network before after
      (.expire event) execution next supported
  have progress := runtime.runInteractionPlan_facts leaks inputs players network before
    execution prior invariant priorMem
  have expiredProgress := runtime.interactionStep_facts leaks inputs players network
    (.expire event)
    prior expired progress.invariant expiredMem
  have suffix := runtime.runInteractionPlan_facts leaks inputs players network after
    expired next expiredProgress.invariant afterMem
  rcases progress.ready_or_completed event ready with completed | priorReady
  · exact suffix.completed (expiredProgress.completed completed)
  · apply suffix.completed
    apply runtime.interactionStep_expire_complete leaks players network event prior expired
      priorReady strategic entered (progress.activated event entered activated priorReady.1)
      _ expiredMem
    rw [progress.clock, beforeTicks]
    exact dueAfterTick

def reactiveCompletionService (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (chosen : ServiceOrder graph)
    (networkTurns : Nat) (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) :
    CompletionService runtime (runtime.reactiveApplication leaks).Execution where
  state := ReactiveApplication.Execution.application
  epoch := runtime.runInteractionPlan leaks players network (interactionEpoch chosen networkTurns)
  progress inputs before after invariant supported := by
    simpa only [interactionEpoch_ticks] using runtime.runInteractionPlan_facts leaks
      inputs players
      network _ before after invariant supported
  chance inputs event before after := runtime.interactionEpoch_chance_complete leaks inputs
    chosen networkTurns players network event before after
  due inputs event entered before after := runtime.interactionEpoch_strategic_complete
    leaks inputs
    chosen networkTurns players network event entered before after

theorem reactiveCompletionService_run (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (count : Nat) (execution : (runtime.reactiveApplication leaks).Execution) :
    (runtime.reactiveCompletionService leaks chosen networkTurns players network).run
      count execution =
      runtime.runInteractionEpochs leaks chosen networkTurns players network count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      simp only [CompletionService.run, runInteractionEpochs, reactiveCompletionService]
      exact FinDist.bind_congr fun next _ => ih next

theorem runInteractionEpochs_terminal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (supported : next ∈ (runtime.runInteractionEpochs leaks chosen networkTurns players network
      runtime.serviceEpochs execution).support) : next.application.config.cut.Terminal := by
  apply (runtime.reactiveCompletionService leaks chosen networkTurns players network).terminal
    inputs execution next invariant
  rwa [runtime.reactiveCompletionService_run leaks]

/-- Every supported terminal result of canonical reactive service completes
the application, even under arbitrary player deviations and network choices. -/
theorem canonical_interaction_complete (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : FinDist graph.Inputs) (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (result : (runtime.reactiveApplication leaks).ProtocolState)
    (supported :
      let initial := inputs.map State.initial
      let scheduler := runtime.interactionScheduler leaks chosen networkTurns network
      let horizon := runtime.interactionHorizon chosen networkTurns
      result ∈ ((((runtime.reactiveApplication leaks).information
        initial horizon scheduler).runSingleMoverBehavioralFrom
          ((runtime.reactiveApplication leaks).singleMover initial horizon scheduler)
          (fun who => (runtime.reactiveApplication leaks).encodePolicy (players who)) (2 *
            horizon + 1)
          ((runtime.reactiveApplication leaks).protocol initial horizon
            scheduler).initHistory).map
            ExecutionProtocol.History.state).support) :
    ∃ control, result = some control ∧ control.execution.application.config.cut.Terminal := by
  dsimp only at supported
  rw [runtime.canonical_interaction_service leaks, FinDist.bind_map] at supported
  obtain ⟨input, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨execution, moved, rfl⟩ := FinDist.support_map .. ▸ reached
  exact ⟨_, rfl, runtime.runInteractionEpochs_terminal leaks input chosen networkTurns
    players network
    _ execution (State.initial_invariant input) moved⟩

end Vegas.EventGraphRuntime
