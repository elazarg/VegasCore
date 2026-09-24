/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceEvaluation
import Vegas.Pending.EventProgress

/-! # Progress under arbitrary reactive player and network policies

The service advances the application clock only at explicit ticks. Player
responses and network choices preserve completed events and live activation
times. These laws do not assume prescribed behavior or successful inclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactive_respond_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action)
    (invariant : execution.application.Invariant inputs) :
    State.ServiceProgress inputs 0 execution.application
      (execution.respond (runtime.reactiveApplication leaks) who action).application := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact .refl invariant
  | some transmission =>
      cases transmission with
      | replay id => exact .refl invariant
      | submit submission =>
          change State.ServiceProgress inputs 0 execution.application
            (submitStep (submission.register execution.application who) who submission.packet)
          have facts := submission.register_facts who execution.application
          have publicEq : State.publicView
              (submitStep (submission.register execution.application who) who submission.packet) =
                execution.application.publicView := by
            rw [submitStep_publicView, facts.2.2]
          have configEq := (submitStep_config
            (submission.register execution.application who) who submission.packet).trans facts.1
          have clockEq := congrArg PublicView.clock publicEq
          have activationEq := congrArg PublicView.activatedAt publicEq
          dsimp only [State.publicView] at clockEq activationEq
          refine ⟨invariant.copy configEq clockEq activationEq, ?_, ?_, ?_⟩
          · rw [configEq]
          · simpa only [Nat.add_zero] using clockEq
          · intro event entered activated _
            rw [activationEq]
            exact activated

theorem reactive_resume_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (actor : Option Player)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (reached : next ∈ ((runtime.reactiveApplication leaks).resume players actor
      execution).support) :
    State.ServiceProgress inputs 0 execution.application next.application := by
  cases actor with
  | none => cases FinDist.mem_support_pure.mp reached; exact .refl invariant
  | some who =>
      obtain ⟨action, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact runtime.reactive_respond_progress leaks inputs execution who action invariant

def reactiveTicks (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) :
      (runtime.reactiveApplication leaks).Command → Nat
  | .application .advanceClock => 1
  | _ => 0

theorem reactive_include_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (execution : (runtime.reactiveApplication leaks).Execution) (id : MessageId Player)
    (invariant : execution.application.Invariant inputs) :
    State.ServiceProgress inputs 0 execution.application
      (execution.includePending (runtime.reactiveApplication leaks) id).application := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact .refl invariant
  | some message =>
      change State.ServiceProgress inputs 0 execution.application
        ((handle runtime execution.application message).getD execution.application)
      cases accepted : handle runtime execution.application message with
      | none => exact .refl invariant
      | some next => exact handle_progress runtime inputs _ next message invariant accepted

theorem reactive_environment_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (invariant : execution.application.Invariant inputs)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    State.ServiceProgress inputs (runtime.reactiveTicks leaks command)
      execution.application next.application := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact .refl invariant
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact .refl invariant
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact runtime.reactive_include_progress leaks inputs execution id invariant
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
      refine ⟨environmentStep_invariant runtime execution.application state
        command invariant changed,
        environmentStep_completed_subset runtime execution.application state command changed,
        ?_, ?_⟩
      · have clock := environmentStep_clock runtime execution.application state command changed
        cases command <;> simpa [reactiveTicks, EnvironmentCommand.clockTicks] using clock
      · exact environmentStep_activatedAt_of_not_completed runtime
          execution.application state command invariant changed

theorem reactive_dispatch_progress (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (invariant : execution.application.Invariant inputs)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players command
      execution).support) :
    State.ServiceProgress inputs (runtime.reactiveTicks leaks command)
      execution.application next.application := by
  obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have environment := runtime.reactive_environment_progress leaks inputs execution middle command
    invariant supported
  have response := runtime.reactive_resume_progress leaks inputs players _ middle next
    environment.invariant moved
  simpa only [Nat.add_zero] using environment.trans response

theorem interactionInstruction_ticks (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (network : runtime.NetworkPolicy leaks)
    (history : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (instruction : ServiceInstruction graph)
    (command : (runtime.reactiveApplication leaks).Command)
    (supported : command ∈
      (runtime.interactionInstruction leaks network history view instruction).support) :
    runtime.reactiveTicks leaks command = instruction.ticks := by
  cases instruction with
  | wire =>
      obtain ⟨choice, _, rfl⟩ := FinDist.support_map .. ▸ supported
      cases choice with
      | activate who | wait => rfl
      | «include» id =>
          dsimp only [NetworkChoice.command, ReactiveApplication.atMostOnceCommand]
          split <;> rfl
  | includeLatest event owner =>
      cases FinDist.mem_support_pure.mp supported
      unfold reactiveLatest
      split <;> rfl
  | player who | grant event | sample event | tick | expire event =>
      cases FinDist.mem_support_pure.mp supported
      rfl

theorem interactionStep_facts (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (instruction : ServiceInstruction graph)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (supported : next ∈ (runtime.interactionStep leaks players network instruction
      execution).support) :
    State.ServiceProgress inputs instruction.ticks execution.application next.application := by
  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have progress := runtime.reactive_dispatch_progress leaks inputs players execution next command
    invariant moved
  rwa [runtime.interactionInstruction_ticks leaks network _ _ instruction command
    selected] at progress

theorem runInteractionPlan_facts (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (plan : List (ServiceInstruction graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (supported : next ∈ (runtime.runInteractionPlan leaks players network plan
      execution).support) :
    State.ServiceProgress inputs (serviceTicks plan) execution.application next.application := by
  induction plan generalizing execution with
  | nil => cases FinDist.mem_support_pure.mp supported; exact .refl invariant
  | cons instruction rest ih =>
      obtain ⟨middle, moved, finished⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      have first := runtime.interactionStep_facts leaks inputs players network instruction
        execution middle invariant moved
      exact first.trans (ih middle first.invariant finished)

omit [DecidableEq Player] in
theorem interactionVisit_ticks (networkTurns : Nat) (event : graph.EventId) :
    serviceTicks (interactionVisit networkTurns event) = 0 := by
  simp only [interactionVisit, serviceTicks_append]
  cases graph.actor? event <;>
    simp [serviceTicks, ServiceInstruction.ticks]

omit [DecidableEq Player] in
theorem interactionEpoch_ticks (chosen : ServiceOrder graph) (networkTurns : Nat) :
    serviceTicks (interactionEpoch chosen networkTurns) = 1 := by
  have sweep : ∀ events : List graph.EventId,
      serviceTicks (events.flatMap (interactionVisit networkTurns)) = 0 := by
    intro events
    induction events with
    | nil => rfl
    | cons event rest ih =>
        rw [List.flatMap_cons, serviceTicks_append, interactionVisit_ticks, ih]
  simp only [interactionEpoch, serviceTicks_append, sweep]
  simp [serviceTicks, ServiceInstruction.ticks, Function.comp_def]

theorem runInteractionEpochs_facts (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (inputs : graph.Inputs)
    (chosen : ServiceOrder graph) (networkTurns : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (count : Nat) (execution next : (runtime.reactiveApplication leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (supported : next ∈ (runtime.runInteractionEpochs leaks chosen networkTurns players network
      count execution).support) :
    State.ServiceProgress inputs count execution.application next.application := by
  induction count generalizing execution with
  | zero => cases FinDist.mem_support_pure.mp supported; exact .refl invariant
  | succ count ih =>
      obtain ⟨middle, moved, finished⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      have first := runtime.runInteractionPlan_facts leaks inputs players network _
        execution middle invariant moved
      rw [interactionEpoch_ticks] at first
      simpa only [Nat.add_comm 1 count] using first.trans (ih middle first.invariant finished)

end Vegas.EventGraphRuntime
