/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingReadiness
import Vegas.Pending.PhaseReadiness
import Vegas.Pending.ReactiveEventStability

/-! # Automatic foreign failure keeps the surviving binding readiness cones -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem drain_binding_readiness (phase : RuntimePhase graph) (commitment : phase.kind = .commitment)
    (state : RecoveryState graph) (owner : Player) (survivor : owner ∉ state.excluded)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload) :
    (phase.drain state).native.config.cut.Ready event ↔ state.native.config.cut.Ready event := by
  apply binding_ready_congr program _ _ event owner payload binding
  intro prior cone
  rcases cone with isPublic | own
  · have outside : prior ∉ phase.events := by
      intro member
      have interval := (phase.mem_events prior).mp member
      have typed := phase.fields prior interval.1 interval.2
      rw [commitment] at typed
      obtain ⟨who, sort, typed⟩ := typed
      rw [typed] at isPublic
      exact isPublic
    have outputs := phase.drainFuel_output_outside state.native.config.remaining state prior outside
    change (phase.drain state).native.config.outputs prior =
      state.native.config.outputs prior at outputs
    rw [← (phase.drain state).native.config.output_available prior,
      ← state.native.config.output_available prior, outputs]
  · have typed : ∃ sort, (graph).outputLayout prior = .binding owner sort := by
      cases kind : (graph).outputLayout prior with
      | binding who sort =>
          have same : who = owner := by simpa only [kind, EventField.SameBindingOwner] using own
          subst who
          exact ⟨sort, rfl⟩
      | publicData | publication | privateInput =>
          simp only [kind, EventField.SameBindingOwner] at own
    obtain ⟨sort, typed⟩ := typed
    have acting := (graph).actor?_of_outputLayout_binding typed
    exact phase.drainFuel_completed_survivor _ state prior owner acting survivor

end Vegas.EventGraphRuntime.ReservedEpoch
