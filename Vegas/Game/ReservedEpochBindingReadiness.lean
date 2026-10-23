/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.EventGraph.Sequential

/-! # Foreign binding completions do not advance an owner's readiness cone -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem binding_predecessors (event prior : (graph).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload) :
    prior ∈ (graph).order.predecessors event ↔
      prior.val < event.val ∧
        (((graph).outputLayout prior).IsPublic ∨
          ((graph).outputLayout prior).SameBindingOwner (.binding owner payload)) := by
  rw [withMode_concurrentReveals_predecessors]
  have dependent : ¬ (toEventGraph program).IndependentReveals prior event := by
    intro independent
    have publication := independent.2.1
    change ((graph).outputLayout event).IsPublication at publication
    rw [binding] at publication
    exact publication
  simp only [dependent, not_false_eq_true, and_true]
  change prior ∈ (barrierOrder (outputLayout program)).predecessors event ↔ _
  rw [mem_barrierOrder]
  change _ ↔ prior.val < event.val ∧
    ((outputLayout program prior).IsPublic ∨
      (outputLayout program prior).SameBindingOwner (.binding owner payload))
  change outputLayout program event = .binding owner payload at binding
  rw [binding]
  simp only [EventField.IsPublic, false_or]

theorem binding_ready_congr (left right : (graph).order.Cut)
    (event : (graph).EventId) (owner : Player) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (completed : ∀ prior : (graph).EventId,
      (((graph).outputLayout prior).IsPublic ∨
          ((graph).outputLayout prior).SameBindingOwner (.binding owner payload)) →
        (prior ∈ left.completed ↔ prior ∈ right.completed)) :
    left.Ready event ↔ right.Ready event := by
  have own : ((graph).outputLayout event).SameBindingOwner (.binding owner payload) := by
    rw [binding]
    exact rfl
  have itself := completed event (Or.inr own)
  constructor
  · intro ready
    refine ⟨fun member => ready.1 (itself.mpr member), ?_⟩
    intro prior predecessor
    have cone := ((binding_predecessors program event prior owner payload binding).mp
      predecessor).2
    exact (completed prior cone).mp (ready.2 predecessor)
  · intro ready
    refine ⟨fun member => ready.1 (itself.mp member), ?_⟩
    intro prior predecessor
    have cone := ((binding_predecessors program event prior owner payload binding).mp
      predecessor).2
    exact (completed prior cone).mpr (ready.2 predecessor)

end Vegas.EventGraphRuntime.ReservedEpoch
