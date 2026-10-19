/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochForeignExpiry

/-! # Actual owned expiry outcomes retain their original pre-reset pair -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem phase_owned_expiry_pair (runtime : EventGraphRuntime graph)
    (left right nextLeft nextRight : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (firstInstalled : phase ∈ left.phases.head?) (secondInstalled : phase ∈ right.phases.head?)
    (commitment : phase.kind = .commitment) (inputs : (graph).Inputs)
    (firstValid : left.current.native.Invariant inputs)
    (secondValid : right.current.native.Invariant inputs) (owner : Player)
    (frame : BindingFrame program owner left.current.native right.current.native)
    (excluded : left.current.excluded = right.current.excluded)
    (event : (graph).EventId) (inside : event ∈ phase.events) (payload : L.Ty)
    (typed : (graph).outputLayout event = .binding owner payload)
    (first : nextLeft ∈ (left.environment runtime (.expire event)).support)
    (second : nextRight ∈ (right.environment runtime (.expire event)).support) :
    ∃ firstNative secondNative : State graph,
      firstNative ∈ (environmentStep runtime left.current.native (.expire event)).support ∧
      secondNative ∈ (environmentStep runtime right.current.native (.expire event)).support ∧
      nextLeft = ({ left with current :=
        left.current.environmentResult (.expire event) firstNative } :
          PhaseRuntimeState graph).normalize ∧
      nextRight = ({ right with current :=
        right.current.environmentResult (.expire event) secondNative } :
          PhaseRuntimeState graph).normalize ∧
      BindingFrame program owner firstNative secondNative ∧
      (left.current.environmentResult (.expire event) firstNative).excluded =
        (right.current.environmentResult (.expire event) secondNative).excluded := by
  have firstAllowed : left.commandAllowed (.expire event) = true := by
    simp only [PhaseRuntimeState.commandAllowed, Option.mem_def.mp firstInstalled,
      Option.any_some, inside, decide_true]
  have secondAllowed : right.commandAllowed (.expire event) = true := by
    simp only [PhaseRuntimeState.commandAllowed, Option.mem_def.mp secondInstalled,
      Option.any_some, inside, decide_true]
  unfold PhaseRuntimeState.environment at first second
  rw [ite_eq_left firstAllowed, PMF.mem_support_map_iff] at first
  rw [ite_eq_left secondAllowed, PMF.mem_support_map_iff] at second
  obtain ⟨firstNative, firstSupport, rfl⟩ := first
  obtain ⟨secondNative, secondSupport, rfl⟩ := second
  have paired := binding_expiry_pair program runtime phase commitment left.current.native
    right.current.native firstNative secondNative inputs firstValid secondValid owner frame
      event inside firstSupport secondSupport
  have firstCompletion := frame.completed payload event (Or.inr (by
    rw [typed]
    rfl))
  have secondCompletion := paired.completed payload event (Or.inr (by
    rw [typed]
    rfl))
  have fresh : (event ∉ left.current.native.config.cut.completed ∧
      event ∈ firstNative.config.cut.completed) ↔
      (event ∉ right.current.native.config.cut.completed ∧
        event ∈ secondNative.config.cut.completed) :=
    and_congr (not_congr firstCompletion) secondCompletion
  refine ⟨firstNative, secondNative, firstSupport, secondSupport, rfl, rfl, paired, ?_⟩
  simp only [RecoveryState.environmentResult]
  by_cases newlyCompleted : event ∉ left.current.native.config.cut.completed ∧
      event ∈ firstNative.config.cut.completed
  · have counterpart := fresh.mp newlyCompleted
    simp only [ite_eq_left newlyCompleted, ite_eq_left counterpart, excluded]
  · have counterpart : ¬ (event ∉ right.current.native.config.cut.completed ∧
        event ∈ secondNative.config.cut.completed) := fun actual =>
      newlyCompleted (fresh.mpr actual)
    simp only [ite_eq_right newlyCompleted, ite_eq_right counterpart, excluded]

end Vegas.EventGraphRuntime.ReservedEpoch
