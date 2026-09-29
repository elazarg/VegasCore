/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceEvaluation
import Vegas.Pending.EventApplication

/-! # Public grants through actual reactive service execution -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactive_respond_serviceGrant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    (execution.respond (runtime.reactiveApplication leaks) who action).application.serviceGrant =
      execution.application.serviceGrant := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id => rfl
      | submit submission =>
          change (submitStep (submission.call.register execution.application who) who
            submission.call.packet).serviceGrant = _
          have same := (submitStep_publicView
            (submission.call.register execution.application who) who submission.call.packet).trans
              (submission.call.register_facts who execution.application).2.2
          exact congrArg PublicView.serviceGrant same

theorem reactive_environment_serviceGrant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (noGrant : ∀ event, command ≠ .application (.grant event))
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    next.application.serviceGrant = execution.application.serviceGrant := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at reached
      subst next
      rfl
  | activate who =>
      obtain ⟨middle, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at reached
      subst next
      change (execution.includePending (runtime.reactiveApplication leaks)
        id).application.serviceGrant = _
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => rfl
      | some message =>
          change ((handle runtime execution.application
            ⟨message.id, message.payload.call⟩).getD execution.application).serviceGrant = _
          cases accepted : handle runtime execution.application
              ⟨message.id, message.payload.call⟩ with
          | none => rfl
          | some state => exact runtime.handle_serviceGrant _ _ _ accepted
  | application command =>
      obtain ⟨middle, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      have same := environmentStep_serviceGrant runtime execution.application state command changed
      cases command with
      | grant event => exact (noGrant event rfl).elim
      | executeSample event | advanceClock | expire event => exact same

theorem interactionStep_serviceGrant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (instruction : ServiceInstruction graph)
    (fixed : instruction ≠ .wire)
    (noGrant : ∀ event, instruction ≠ .grant event)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ (runtime.interactionStep leaks players network instruction
      execution).support) :
    next.application.serviceGrant = execution.application.serviceGrant := by
  obtain ⟨command, selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, observed, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have unchanged : next.application.serviceGrant = middle.application.serviceGrant := by
    cases actor : command.actor? (runtime.reactiveApplication leaks) with
    | none =>
        change next ∈ ((runtime.reactiveApplication leaks).resume players
          (command.actor? (runtime.reactiveApplication leaks)) middle).support at resumed
        rw [actor] at resumed
        cases (PMF.mem_support_pure_iff _ _).mp resumed
        rfl
    | some who =>
        change next ∈ ((runtime.reactiveApplication leaks).resume players
          (command.actor? (runtime.reactiveApplication leaks)) middle).support at resumed
        rw [actor] at resumed
        obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
        exact runtime.reactive_respond_serviceGrant leaks middle who response
  rw [unchanged]
  apply runtime.reactive_environment_serviceGrant leaks execution middle command _ observed
  intro event
  cases instruction with
  | wire => exact (fixed rfl).elim
  | grant granted => exact (noGrant granted rfl).elim
  | player who | sample sampled | tick | expire expired =>
      simp only [interactionInstruction, PMF.mem_support_pure_iff _ _] at selected
      subst command
      intro impossible
      cases impossible
  | includeLatest target owner =>
      simp only [interactionInstruction, PMF.mem_support_pure_iff _ _] at selected
      subst command
      unfold reactiveLatest
      split <;> simp

/-- A fixed service tail without another grant retains the current public
event cursor under arbitrary raw player responses. -/
theorem runInteractionPlan_serviceGrant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (fixed : ServiceInstruction.wire ∉ plan)
    (noGrant : ∀ event, ServiceInstruction.grant event ∉ plan)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ (runtime.runInteractionPlan leaks players network plan execution).support) :
    next.application.serviceGrant = execution.application.serviceGrant := by
  induction plan generalizing execution with
  | nil => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | cons instruction rest ih =>
      obtain ⟨middle, stepped, continued⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      rw [ih (fun member => fixed (List.mem_cons_of_mem _ member))
        (fun event member => noGrant event (List.mem_cons_of_mem _ member)) middle continued]
      exact runtime.interactionStep_serviceGrant leaks players network instruction
        (fun equal => fixed (List.mem_cons.mpr (Or.inl equal.symm)))
        (fun event equal => noGrant event (List.mem_cons.mpr (Or.inl equal.symm)))
        execution middle stepped

end Vegas.EventGraphRuntime
