/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingReadiness
import Vegas.Pending.PhaseReadiness
import Vegas.Pending.ReactiveEventStability

/-! # An unfinished surviving binding chain keeps its actual attempt live -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem unfinished_owner_binding_ready (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (cut : (graph).order.Cut)
    (within : cut.Within phase.low phase.high) (owner : Player)
    (unfinished : ∃ event ∈ phase.events, (graph).actor? event = some owner ∧
      event ∉ cut.completed) :
    ∃ event ∈ phase.events, (graph).actor? event = some owner ∧ cut.Ready event := by
  classical
  let missing := phase.events.filter fun event =>
    (graph).actor? event = some owner ∧ event ∉ cut.completed
  have nonempty : missing.Nonempty := by
    obtain ⟨event, inside, actor, notCompleted⟩ := unfinished
    exact ⟨event, Finset.mem_filter.mpr ⟨inside, actor, notCompleted⟩⟩
  let event := missing.min' nonempty
  have selected : event ∈ missing := Finset.min'_mem _ _
  obtain ⟨inside, actor, notCompleted⟩ := Finset.mem_filter.mp selected
  have bounds := (phase.mem_events event).mp inside
  have typed := phase.fields event bounds.1 bounds.2
  rw [commitment] at typed
  obtain ⟨who, payload, binding⟩ := typed
  have ownerEq : who = owner := Option.some.inj
    (((graph).actor?_of_outputLayout_binding binding).symm.trans actor)
  subst who
  refine ⟨event, inside, actor, notCompleted, ?_⟩
  intro prior predecessor
  obtain ⟨earlier, cone⟩ := (binding_predecessors program event prior owner payload binding).mp
    predecessor
  by_cases lower : prior.val < phase.low
  · exact within.1 prior lower
  have priorInside : prior ∈ phase.events := (phase.mem_events prior).mpr
    ⟨by omega, by omega⟩
  rcases cone with visible | own
  · have priorType := phase.fields prior (by omega) (by omega)
    rw [commitment] at priorType
    obtain ⟨who, sort, priorType⟩ := priorType
    rw [priorType] at visible
    exact visible.elim
  · by_contra absent
    have priorType : ∃ sort, (graph).outputLayout prior = .binding owner sort := by
      cases kind : (graph).outputLayout prior with
      | binding who sort =>
          have same : who = owner := by simpa only [kind, EventField.SameBindingOwner] using own
          subst who
          exact ⟨sort, rfl⟩
      | publicData | publication | privateInput =>
          simp only [kind, EventField.SameBindingOwner] at own
    obtain ⟨sort, priorType⟩ := priorType
    have priorActor := (graph).actor?_of_outputLayout_binding priorType
    have member : prior ∈ missing := Finset.mem_filter.mpr ⟨priorInside, priorActor, absent⟩
    have minimal : event.val ≤ prior.val := Finset.min'_le _ _ member
    omega

theorem unfinished_owner_request (state : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (installed : phase ∈ state.phases.head?) (commitment : phase.kind = .commitment)
    (within : state.current.native.config.cut.Within phase.low phase.high)
    (owner : Player) (active : owner ∉ state.current.excluded)
    (unfinished : ∃ event ∈ phase.events, (graph).actor? event = some owner ∧
      event ∉ state.current.native.config.cut.completed) :
    ∃ event, state.SeedRequest owner ⟨state.attempt, event⟩ := by
  obtain ⟨event, inside, actor, ready⟩ := unfinished_owner_binding_ready program phase commitment
    state.current.native.config.cut within owner unfinished
  exact ⟨event, rfl, ⟨phase, installed, inside⟩, ready, actor, active⟩

end Vegas.EventGraphRuntime.ReservedEpoch
