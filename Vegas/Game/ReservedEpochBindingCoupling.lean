/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingReadiness
import Vegas.Pending.EventInvariant

/-! # Paired native binding steps at one reserved processing clock -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem accepted_binding_foreign_cone (runtime : EventGraphRuntime graph)
    (left right : State graph) (id : MessageId Player) (event : (graph).EventId)
    (candidate : Handle graph) (owner foreign : Player) (payload foreignPayload : L.Ty)
    (binding : (graph).outputLayout event = .binding foreign foreignPayload)
    (different : foreign ≠ owner)
    (accepted : handle runtime left ⟨id, .commitment event candidate⟩ = some right)
    (query : (graph).EventId)
    (cone : ((graph).outputLayout query).IsPublic ∨
      ((graph).outputLayout query).SameBindingOwner (.binding owner payload)) :
    query ∈ left.config.cut.completed ↔ query ∈ right.config.cut.completed := by
  have distinct : query ≠ event := by
    intro same
    subst query
    rw [binding] at cone
    rcases cone with impossible | sameOwner
    · exact impossible
    · exact different sameOwner
  obtain ⟨address, named, ready, action, member⟩ :=
    handle_config_mem_step runtime left right ⟨id, .commitment event candidate⟩ accepted
  have same : event = address := Option.some.inj named
  subst address
  rw [Config.step_cut left.config event ready action right.config member,
    EventOrder.Cut.mem_complete]
  exact (or_iff_right distinct).symm

theorem accepted_binding_foreign_stamp (runtime : EventGraphRuntime graph)
    (left right : State graph) (inputs : (graph).Inputs) (valid : left.Invariant inputs)
    (id : MessageId Player) (event query : (graph).EventId) (candidate : Handle graph)
    (owner foreign : Player) (payload foreignPayload : L.Ty)
    (binding : (graph).outputLayout query = .binding owner payload)
    (otherBinding : (graph).outputLayout event = .binding foreign foreignPayload)
    (different : foreign ≠ owner)
    (accepted : handle runtime left ⟨id, .commitment event candidate⟩ = some right) :
    right.activatedAt query = left.activatedAt query := by
  have requested := accepted_binding_foreign_readiness program runtime left right id query event
    owner foreign payload foreignPayload binding otherBinding different candidate accepted
  have physical := handle_clock_activated runtime left right
    ⟨id, .commitment event candidate⟩ accepted
  rw [physical.2]
  cases stamp : left.activatedAt query with
  | some entered =>
      have before := (valid.activated_iff query).mp (by simp only [stamp, Option.isSome_some])
      have after := requested.mpr before.1
      exact State.refreshActivated_eq_of_ready right.config left.clock left.activatedAt query
        entered after before.2 stamp
  | none =>
      cases actor : (graph).actor? query with
      | none => simp only [State.refreshActivated, actor, dite_eq_ite, ite_self]
      | some who =>
          have unfinished : ¬ right.config.cut.Ready query := by
            intro ready
            have present := (valid.activated_iff query).mpr
              ⟨requested.mp ready, by simp only [actor, Option.isSome_some]⟩
            simp only [stamp, Option.isSome_none, Bool.false_eq_true] at present
          simp only [State.refreshActivated, unfinished, ↓reduceDIte]

/-- Processing the same owned packet at the same epoch clock gives every owned
successor the same readiness and timer, despite different foreign completions. -/
theorem accepted_binding_successor_timer (runtime : EventGraphRuntime graph)
    (left right nextLeft nextRight : State graph)
    (idLeft idRight : MessageId Player) (event query : (graph).EventId)
    (candidateLeft candidateRight : Handle graph) (owner : Player) (payload : L.Ty)
    (binding : (graph).outputLayout query = .binding owner payload)
    (completed : ∀ prior : (graph).EventId,
      (((graph).outputLayout prior).IsPublic ∨
        ((graph).outputLayout prior).SameBindingOwner (.binding owner payload)) →
      (prior ∈ left.config.cut.completed ↔ prior ∈ right.config.cut.completed))
    (clock : left.clock = right.clock)
    (stamp : left.activatedAt query = right.activatedAt query)
    (acceptedLeft : handle runtime left ⟨idLeft, .commitment event candidateLeft⟩ = some nextLeft)
    (acceptedRight : handle runtime right ⟨idRight, .commitment event candidateRight⟩ =
      some nextRight) :
    (nextLeft.config.cut.Ready query ↔ nextRight.config.cut.Ready query) ∧
      nextLeft.activatedAt query = nextRight.activatedAt query ∧
      nextLeft.clock = nextRight.clock := by
  obtain ⟨addressLeft, namedLeft, readyLeft, actionLeft, memberLeft⟩ :=
    handle_config_mem_step runtime left nextLeft ⟨idLeft, .commitment event candidateLeft⟩
      acceptedLeft
  have sameLeft : event = addressLeft := Option.some.inj namedLeft
  subst addressLeft
  obtain ⟨addressRight, namedRight, readyRight, actionRight, memberRight⟩ :=
    handle_config_mem_step runtime right nextRight ⟨idRight, .commitment event candidateRight⟩
      acceptedRight
  have sameRight : event = addressRight := Option.some.inj namedRight
  subst addressRight
  have cutLeft := Config.step_cut left.config event readyLeft actionLeft nextLeft.config memberLeft
  have cutRight := Config.step_cut right.config event readyRight actionRight nextRight.config
    memberRight
  have ready : nextLeft.config.cut.Ready query ↔ nextRight.config.cut.Ready query := by
    apply binding_ready_congr program _ _ query owner payload binding
    intro prior cone
    rw [cutLeft, cutRight, EventOrder.Cut.mem_complete, EventOrder.Cut.mem_complete]
    exact or_congr Iff.rfl (completed prior cone)
  have physicalLeft := handle_clock_activated runtime left nextLeft
    ⟨idLeft, .commitment event candidateLeft⟩ acceptedLeft
  have physicalRight := handle_clock_activated runtime right nextRight
    ⟨idRight, .commitment event candidateRight⟩ acceptedRight
  refine ⟨ready, ?_, physicalLeft.1.trans (clock.trans physicalRight.1.symm)⟩
  rw [physicalLeft.2, physicalRight.2]
  simp only [State.refreshActivated, dite_eq_ite]
  by_cases requested : nextLeft.config.cut.Ready query
  · have other := ready.mp requested
    simp only [ite_eq_left requested, ite_eq_left other]
    rw [clock, stamp]
  · have other : ¬ nextRight.config.cut.Ready query := fun member => requested (ready.mpr member)
    simp only [ite_eq_right requested, ite_eq_right other]

end Vegas.EventGraphRuntime.ReservedEpoch
