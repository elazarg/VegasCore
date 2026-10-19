/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingExpiry
import Vegas.Game.ReservedEpochDrainFrame

/-! # Foreign native expiry cannot change a surviving owner's binding cone -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

private theorem foreign_complete_failure_frame (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (state : State graph) (inputs : (graph).Inputs)
    (valid : state.Invariant inputs) (event : (graph).EventId) (inside : event ∈ phase.events)
    (ready : state.config.cut.Ready event) (owner foreign : Player)
    (actor : (graph).actor? event = some foreign) (different : foreign ≠ owner) :
    BindingFrame program owner state (state.completeFailure event ready) := by
  classical
  let current : RecoveryState graph := ⟨state, {foreign}⟩
  have eligible : current.AutomaticReady event := by
    refine ⟨ready, ?_⟩
    change (match (graph).actor? event with
      | none => False | some who => who ∈ ({foreign} : Finset Player))
    rw [actor]
    exact Finset.mem_singleton_self _
  have survivor : owner ∉ current.excluded := by
    simpa only [current, Finset.mem_singleton] using Ne.symm different
  have step : phase.AutomaticStep current (current.completeAutomatic event eligible) :=
    ⟨event, ⟨inside, eligible⟩, rfl⟩
  exact automatic_commitment_frame program phase commitment current _ inputs valid owner
    survivor step

theorem foreign_expiry_frame (runtime : EventGraphRuntime graph) (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (state next : State graph) (inputs : (graph).Inputs)
    (valid : state.Invariant inputs) (event : (graph).EventId) (inside : event ∈ phase.events)
    (owner foreign : Player) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding foreign payload)
    (different : foreign ≠ owner)
    (reached : next ∈ (environmentStep runtime state (.expire event)).support) :
    BindingFrame program owner state next := by
  have actor := (graph).actor?_of_outputLayout_binding binding
  have code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind foreign payload := by
    generalize cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) = body
    cases body
    rfl
  have node := nodeView_eq_bind binding code
  by_cases ready : state.config.cut.Ready event
  · cases entered : state.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated runtime state event ready entered,
          PMF.mem_support_pure_iff _ _] at reached
        subst next
        exact BindingFrame.refl owner state
    | some clock =>
        by_cases due : runtime.deadline event ≤ state.clock - clock
        · rw [environmentStep_expire_bind_eq runtime state event ready clock entered due
            foreign payload binding code node, PMF.mem_support_pure_iff _ _] at reached
          subst next
          have retained := foreign_complete_failure_frame program phase commitment state inputs
            valid event inside ready owner foreign actor different
          simpa only [State.completeFailure, node] using retained
        · rw [environmentStep_expire_of_not_due runtime state event ready clock entered due,
            PMF.mem_support_pure_iff _ _] at reached
          subst next
          exact BindingFrame.refl owner state
  · rw [environmentStep_expire_of_not_ready runtime state event ready,
      PMF.mem_support_pure_iff _ _] at reached
    subst next
    exact BindingFrame.refl owner state

/-- Every actual native expiry check preserves a paired selected-owner cone:
its own expiry is matched, and any other owner's expiry stutters on that cone. -/
theorem binding_expiry_pair (runtime : EventGraphRuntime graph) (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (left right nextLeft nextRight : State graph)
    (inputs : (graph).Inputs) (leftValid : left.Invariant inputs)
    (rightValid : right.Invariant inputs) (owner : Player)
    (frame : BindingFrame program owner left right) (event : (graph).EventId)
    (inside : event ∈ phase.events)
    (first : nextLeft ∈ (environmentStep runtime left (.expire event)).support)
    (second : nextRight ∈ (environmentStep runtime right (.expire event)).support) :
    BindingFrame program owner nextLeft nextRight := by
  obtain ⟨low, high⟩ := (phase.mem_events event).mp inside
  obtain ⟨foreign, payload, binding⟩ := by
    simpa only [commitment] using phase.fields event low high
  by_cases same : foreign = owner
  · subst foreign
    exact BindingFrame.expire_owned program frame runtime event payload binding _ _ first second
  · have firstFrame := foreign_expiry_frame program runtime phase commitment left nextLeft
      inputs leftValid event inside owner foreign payload binding same first
    have secondFrame := foreign_expiry_frame program runtime phase commitment right nextRight
      inputs rightValid event inside owner foreign payload binding same second
    exact firstFrame.symm.trans (frame.trans secondFrame)

end Vegas.EventGraphRuntime.ReservedEpoch
