/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingReadiness
import Vegas.Pending.PhaseReadiness
import Vegas.Pending.PhaseSavedExclusionReadback

/-! # Exact binding records of an excluded owner's completed original drain -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

/-- The existing automatic drain completes an excluded owner's entire binding
chain. Public prerequisites already precede the installed phase; in-block
prerequisites belong to the same owner and are handled in source rank order. -/
theorem drain_excluded_owner_completed (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (state : RecoveryState graph)
    (within : state.native.config.cut.Within phase.low phase.high)
    (owner : Player) (excluded : owner ∈ state.excluded) :
    ∀ event ∈ phase.events, (graph).actor? event = some owner →
      event ∈ (phase.drain state).native.config.cut.completed := by
  have drainedWithin := phase.drain_within state within
  have byRank : ∀ rank, ∀ event : (graph).EventId, event.val = rank →
      event ∈ phase.events → (graph).actor? event = some owner →
      event ∈ (phase.drain state).native.config.cut.completed := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
        intro event rankEq inside actor
        by_contra unfinished
        obtain ⟨lower, upper⟩ := (phase.mem_events event).mp inside
        obtain ⟨who, payload, binding⟩ := by
          simpa only [commitment] using phase.fields event lower upper
        have whoEq : who = owner := Option.some.inj
          (((graph).actor?_of_outputLayout_binding binding).symm.trans actor)
        subst who
        have ready : (phase.drain state).native.config.cut.Ready event := by
          refine ⟨unfinished, ?_⟩
          intro prior dependency
          obtain ⟨earlier, cone⟩ :=
            (binding_predecessors program event prior owner payload binding).mp dependency
          by_cases before : prior.val < phase.low
          · exact drainedWithin.1 prior before
          have priorInside : prior ∈ phase.events :=
            (phase.mem_events prior).mpr ⟨by omega, earlier.trans upper⟩
          rcases cone with isPublic | own
          · obtain ⟨foreign, sort, kind⟩ := by
              simpa only [commitment] using phase.fields prior
                ((phase.mem_events prior).mp priorInside).1
                ((phase.mem_events prior).mp priorInside).2
            rw [kind] at isPublic
            exact isPublic.elim
          · have priorActor : (graph).actor? prior = some owner := by
              cases kind : (graph).outputLayout prior with
              | binding foreign sort =>
                  have same : foreign = owner := by
                    simpa only [kind, EventField.SameBindingOwner] using own
                  subst foreign
                  exact (graph).actor?_of_outputLayout_binding kind
              | publicData | publication | privateInput =>
                  simp only [kind, EventField.SameBindingOwner] at own
            exact ih prior.val (by omega) prior rfl priorInside priorActor
        apply phase.drain_quiescent state event
        refine ⟨inside, ready, ?_⟩
        rw [actor, phase.drain_excluded]
        exact excluded
  intro event inside actor
  exact byRank event.val event rfl inside actor

/-- The original drained snapshot retains the literal accepted handle and
candidate catalogue. Its per-binding public miss bit is precisely absence of
an accepting handle, including when an accepted handle has unusable meaning. -/
theorem drain_excluded_owner_binding_records (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (state : RecoveryState graph)
    (within : state.native.config.cut.Within phase.low phase.high)
    (owner : Player) (excluded : owner ∈ state.excluded) :
    (phase.drain state).native.accepted = state.native.accepted ∧
      (phase.drain state).native.candidates = state.native.candidates ∧
      ∀ event ∈ phase.events, (graph).actor? event = some owner →
        event ∈ (phase.drain state).native.config.cut.completed ∧
          ((phase.drain state).native.PublicFailure event ↔
            state.native.accepted (.inr event) = none) := by
  have tables := phase.drain_tables state
  refine ⟨tables.1, tables.2.1, ?_⟩
  intro event inside actor
  have completed := drain_excluded_owner_completed program phase commitment state within owner
    excluded event inside actor
  obtain ⟨lower, upper⟩ := (phase.mem_events event).mp inside
  obtain ⟨who, payload, binding⟩ := by
    simpa only [commitment] using phase.fields event lower upper
  have whoEq : who = owner := Option.some.inj
    (((graph).actor?_of_outputLayout_binding binding).symm.trans actor)
  subst who
  refine ⟨completed, ?_⟩
  rw [(phase.drain state).native.publicFailure_iff_accepted_none event owner payload
    binding completed, tables.1]

end Vegas.EventGraphRuntime.ReservedEpoch
