/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPublicState
import Vegas.Pending.ReactiveDisclosureStability

/-! # Public evidence of an omitted required binding

Completion without an accepted handle is visible in the application state.
This detector needs no inference from absent partial traffic records. An
accepted opaque handle does not trigger it, even if its hidden meaning is
unusable. Once present, the evidence survives arbitrary native continuations.

Using this evidence as a sanction additionally requires a backend guarantee
that a timely permitted submission is included before expiry. The detector
alone does not attribute censorship or prove that an earlier silent response
will miss the eventual deadline.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def PublicView.missedBinding (view : PublicView graph) (event : graph.EventId) : Bool :=
  match graph.outputLayout event with
  | .binding _ _ => decide (event ∈ view.observation.completionOrder) &&
      (view.accepted (.inr event)).isNone
  | .publicData _ | .privateInput _ _ | .publication _ => false

theorem State.publicView_missedBinding (state : State graph) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    state.publicView.missedBinding event = true ↔
      event ∈ state.config.cut.completed ∧ state.accepted (.inr event) = none := by
  simp only [PublicView.missedBinding, binding, Bool.and_eq_true, decide_eq_true_eq,
    Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨completed, absent⟩
    exact ⟨(state.config.history_exact event).mp completed, absent⟩
  · rintro ⟨completed, absent⟩
    exact ⟨(state.config.history_exact event).mpr completed, absent⟩

theorem PublicView.missedBinding_of_accepted (view : PublicView graph)
    (event : graph.EventId) (candidate : Handle graph)
    (accepted : view.accepted (.inr event) = some candidate) :
    view.missedBinding event = false := by
  unfold missedBinding
  cases graph.outputLayout event <;> simp only [accepted, Option.isNone_some, Bool.and_false]

theorem State.missedBinding_complete (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (absent : state.accepted (.inr event) = none) :
    (state.complete event ready action value).publicView.missedBinding event = true := by
  classical
  apply (State.publicView_missedBinding _ event owner payload binding).mpr
  exact ⟨by simp [State.complete, EventOrder.Cut.complete], absent⟩

/-- Actual binding expiry produces publicly persistent omission evidence.
The accepted-handle premise is about ledger state, not a watcher's sample. -/
theorem missedBinding_expire (runtime : EventGraphRuntime graph) (state next : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (absent : state.accepted (.inr event) = none)
    (reached : next ∈ (environmentStep runtime state (.expire event)).support) :
    next.publicView.missedBinding event = true := by
  classical
  rw [environmentStep_expire_bind_eq runtime state event ready entered activated due owner payload
    outputEq codeEq node] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  exact state.missedBinding_complete event ready _ _ owner payload outputEq absent

/-- Native submissions, packet handling, public chance and service commands
cannot erase a completed binding omission, even after further deviations. -/
theorem reactiveMissedBindingInvariant [DecidableEq Player] (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    (runtime.reactiveApplication leaks).Invariant
      (fun state => state.publicView.missedBinding event = true) where
  submit state who material missed := by
    have same := (runtime.reactive_respond_application leaks
      (.initial (runtime.reactiveApplication leaks) state) who ⟨some material⟩).2
    exact (congrArg (fun view : PublicView graph => view.missedBinding event) same).trans missed
  handle state message next missed handled := by
    obtain ⟨completed, absent⟩ :=
      (state.publicView_missedBinding event owner payload binding).mp missed
    have present : (state.config.store (.inr event)).isSome = true :=
      (state.config.output_available event).mpr completed
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
    have retained := handle_store_of_some runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call handled) (.inr event) value stored
    apply (next.publicView_missedBinding event owner payload binding).mpr
    refine ⟨(next.config.output_available event).mp ?_, ?_⟩
    · change (next.config.store (.inr event)).isSome = true
      rw [retained]
      rfl
    · exact (handle_accepted_of_present runtime state next (.inr event) present
        ⟨message.id, message.payload.call⟩
          (reactiveHandle_call handled)).trans absent
  environment state command next missed reached := by
    obtain ⟨completed, absent⟩ :=
      (state.publicView_missedBinding event owner payload binding).mp missed
    have present : (state.config.store (.inr event)).isSome = true :=
      (state.config.output_available event).mpr completed
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
    have retained := environmentStep_store_of_some runtime state next command reached
      (.inr event) value stored
    apply (next.publicView_missedBinding event owner payload binding).mpr
    refine ⟨(next.config.output_available event).mp ?_, ?_⟩
    · change (next.config.store (.inr event)).isSome = true
      rw [retained]
      rfl
    · exact (congrFun (environmentStep_tables runtime state next command reached).1
        (.inr event)).trans absent

end Vegas.EventGraphRuntime
