/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.EventGraph.Sequential
import Vegas.Pending.EventApplication

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

theorem other_owner_not_binding_predecessor (event other : (graph).EventId)
    (owner foreign : Player) (payload foreignPayload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (otherBinding : (graph).outputLayout other = .binding foreign foreignPayload)
    (different : foreign ≠ owner) : other ∉ (graph).order.predecessors event := by
  rw [binding_predecessors program event other owner payload binding, otherBinding]
  simp only [EventField.IsPublic, EventField.SameBindingOwner, false_or]
  exact fun member => different member.2

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

theorem binding_ready_after_foreign_completion (cut : (graph).order.Cut)
    (event other : (graph).EventId) (owner foreign : Player) (payload foreignPayload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (otherBinding : (graph).outputLayout other = .binding foreign foreignPayload)
    (different : foreign ≠ owner) (ready : cut.Ready other) :
    (cut.complete other ready).Ready event ↔ cut.Ready event := by
  have absent := other_owner_not_binding_predecessor program event other owner foreign
    payload foreignPayload binding otherBinding different
  have events : event ≠ other := by
    intro same
    subst other
    have owners : owner = foreign := (EventField.binding.inj
      (binding.symm.trans otherBinding)).1
    exact different owners.symm
  constructor
  · intro after
    refine ⟨fun member => after.1 (Finset.mem_insert_of_mem member), ?_⟩
    intro prior predecessor
    have completed := after.2 predecessor
    rw [EventOrder.Cut.mem_complete] at completed
    rcases completed with same | previous
    · subst prior
      exact (absent predecessor).elim
    · exact previous
  · intro before
    exact before.after_complete ready events

theorem complete_other_binding_stamp (state : State graph)
    (event other : (graph).EventId) (owner foreign : Player) (payload foreignPayload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (otherBinding : (graph).outputLayout other = .binding foreign foreignPayload)
    (different : foreign ≠ owner) (ready : state.config.cut.Ready other)
    (action : (graph).Action other) (value : ((graph).outputLayout other).Value)
    (actor : (graph).actor? event = some owner) (entered : Nat)
    (requested : state.config.cut.Ready event) (stamp : state.activatedAt event = some entered) :
    (state.complete other ready action value).activatedAt event = some entered := by
  have retained := (binding_ready_after_foreign_completion program state.config.cut
    event other owner foreign payload foreignPayload binding otherBinding different ready).mpr
      requested
  change (state.config.complete other ready action value).cut.Ready event at retained
  change State.refreshActivated _ state.clock state.activatedAt event = some entered
  simp only [State.refreshActivated, retained, ↓reduceDIte, actor, stamp, Option.orElse_some]

theorem accepted_binding_foreign_readiness (runtime : EventGraphRuntime graph)
    (state next : State graph) (id : Interaction.MessageId Player)
    (event other : (graph).EventId) (owner foreign : Player) (payload foreignPayload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (otherBinding : (graph).outputLayout other = .binding foreign foreignPayload)
    (different : foreign ≠ owner) (candidate : Handle graph)
    (accepted : handle runtime state ⟨id, .commitment other candidate⟩ = some next) :
    next.config.cut.Ready event ↔ state.config.cut.Ready event := by
  obtain ⟨address, addressed, ready, action, member⟩ :=
    handle_config_mem_step runtime state next ⟨id, .commitment other candidate⟩ accepted
  have same : other = address := Option.some.inj addressed
  subst address
  rw [Config.step_cut state.config other ready action next.config member]
  exact binding_ready_after_foreign_completion program state.config.cut event other owner foreign
    payload foreignPayload binding otherBinding different ready

end Vegas.EventGraphRuntime.ReservedEpoch
