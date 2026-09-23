/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EventCommitmentBinding

/-! # Binding under arbitrary reactive continuations

Every player response and scheduler step retains every fixed candidate meaning.
The statements cover arbitrary policies and raw protocol states; no service,
honesty, or eventual inclusion assumption is needed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactive_respond_candidate_fixed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) (candidate : Handle graph)
    (fixed : execution.application.candidates.lookup candidate ≠ .fresh) :
    (execution.respond (runtime.reactiveApplication leaks) who
      action).application.candidates.lookup
      candidate = execution.application.candidates.lookup candidate := by
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id => rfl
      | submit submission =>
          have registered : (submission.register execution.application who).candidates.lookup
              candidate = execution.application.candidates.lookup candidate := by
            rw [submission.register_eq]
            cases submission.registrationCommand who with
            | none => rfl
            | some command => exact privateStep_lookup_of_not_fresh _ who command candidate fixed
          exact (submitStep_lookup_of_not_fresh _ who submission.packet candidate
            (by rwa [registered])).trans registered

theorem reactive_include_candidate_fixed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (id : MessageId Player)
    (candidate : Handle graph)
    (fixed : execution.application.candidates.lookup candidate ≠ .fresh) :
    (execution.includePending (runtime.reactiveApplication leaks)
      id).application.candidates.lookup
      candidate = execution.application.candidates.lookup candidate := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => rfl
  | some envelope =>
      simp only
      change (State.candidates ((handle runtime execution.application envelope).getD
        execution.application)).lookup candidate = _
      cases accepted : handle runtime execution.application envelope with
      | none => rfl
      | some next =>
          exact handle_lookup_of_not_fresh runtime _ next envelope candidate fixed accepted

theorem reactive_environment_candidate_fixed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command) (candidate : Handle graph)
    (fixed : execution.application.candidates.lookup candidate ≠ .fresh)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    next.application.candidates.lookup candidate =
      execution.application.candidates.lookup candidate := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact runtime.reactive_include_candidate_fixed leaks execution id candidate fixed
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
      rw [(environmentStep_tables runtime execution.application state command changed).2]

/-- The preservation law holds for each supported canonical transition from
any continuation, including a player move or an adaptive scheduler choice. -/
theorem reactive_transition_candidate_fixed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (before : (runtime.reactiveApplication leaks).Control)
    (after : (runtime.reactiveApplication leaks).ProtocolState)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (candidate : Handle graph)
    (fixed : before.execution.application.candidates.lookup candidate ≠ .fresh)
    (reached : after ∈ ((runtime.reactiveApplication leaks).transition initial horizon scheduler
      (some before) joint).support) :
    ∃ next, after = some next ∧ next.execution.application.candidates.lookup candidate =
      before.execution.application.candidates.lookup candidate := by
  rcases before with ⟨remaining, current, execution⟩
  cases current with
  | some who =>
      cases FinDist.mem_support_pure.mp reached
      exact ⟨_, rfl, runtime.reactive_respond_candidate_fixed leaks execution who _
        candidate fixed⟩
  | none =>
      cases remaining with
      | zero => cases FinDist.mem_support_pure.mp reached; exact ⟨_, rfl, rfl⟩
      | succ remaining =>
          obtain ⟨command, _, supported⟩ :=
            Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
          obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
          exact ⟨_, rfl,
            runtime.reactive_environment_candidate_fixed leaks
              execution next command candidate fixed moved⟩

end Vegas.EventGraphRuntime
