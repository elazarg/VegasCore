/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingFrame
import Vegas.Game.ReservedEpochCommitmentDrain

/-! # Actual commitment drains preserve surviving native owner frames -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem automatic_commitment_frame (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (before after : RecoveryState graph)
    (inputs : (graph).Inputs) (valid : before.native.Invariant inputs)
    (owner : Player) (survivor : owner ∉ before.excluded)
    (step : phase.AutomaticStep before after) :
    BindingFrame program owner before.native after.native := by
  obtain ⟨event, eligible, rfl⟩ := step
  obtain ⟨foreign, actor, excluded⟩ := eligible.2.owned
  have different : foreign ≠ owner := fun same => survivor (same ▸ excluded)
  obtain ⟨low, high⟩ := (phase.mem_events event).mp eligible.1
  obtain ⟨who, payload, binding⟩ := by
    simpa only [commitment] using phase.fields event low high
  have whoEq : who = foreign := Option.some.inj
    (((graph).actor?_of_outputLayout_binding binding).symm.trans actor)
  subst who
  obtain ⟨action, supported⟩ := before.completeAutomatic_step event eligible.2
  have history := Config.step_history before.native.config event eligible.2.1 action _ supported
  rw [Config.step, PMF.support_map] at supported
  obtain ⟨output, outputSupported, config⟩ := supported
  have tables := before.native.completeFailure_tables event eligible.2.1
  have outside : ∀ query : (graph).EventId,
      (((graph).outputLayout query).IsPublic ∨
        ∃ sort, (graph).outputLayout query = .binding owner sort) → query ≠ event := by
    intro query cone same
    subst query
    rw [binding] at cone
    rcases cone with impossible | ⟨sort, owned⟩
    · exact impossible
    · exact different (EventField.binding.inj owned).1
  have completed : ∀ query : (graph).EventId,
      (((graph).outputLayout query).IsPublic ∨
        ∃ sort, (graph).outputLayout query = .binding owner sort) →
      (query ∈ (before.completeAutomatic event eligible.2).native.config.cut.completed ↔
        query ∈ before.native.config.cut.completed) := by
    intro query cone
    have cut := Config.step_cut before.native.config event eligible.2.1 action _
      (by rw [Config.step, PMF.support_map]; exact ⟨output, outputSupported, config⟩)
    rw [cut, EventOrder.Cut.mem_complete]
    exact or_iff_right (outside query cone)
  have ready : ∀ query sort, (graph).outputLayout query = .binding owner sort →
      ((before.completeAutomatic event eligible.2).native.config.cut.Ready query ↔
        before.native.config.cut.Ready query) := by
    intro query sort owned
    apply binding_ready_congr program _ _ query owner sort owned
    intro prior cone
    rcases cone with visible | sameOwner
    · exact completed prior (Or.inl visible)
    · have typed : ∃ kind, (graph).outputLayout prior = .binding owner kind := by
        cases layout : (graph).outputLayout prior with
        | binding who valueSort =>
            have same : who = owner := by
              simpa only [layout, EventField.SameBindingOwner] using sameOwner
            subst who
            exact ⟨valueSort, rfl⟩
        | publicData | publication | privateInput =>
            simp only [layout, EventField.SameBindingOwner] at sameOwner
      exact completed prior (Or.inr typed)
  constructor
  · rw [← config]
    rfl
  · intro query visible
    rw [← config]
    exact (Config.complete_output_of_ne _ _ _ _ _ _ (outside query (Or.inl visible))).symm
  · intro query sort owned
    rw [← config]
    exact (Config.complete_output_of_ne _ _ _ _ _ _
      (outside query (Or.inr ⟨sort, owned⟩))).symm
  · have other : (graph).actor? event ≠ some owner :=
      fun same => different (Option.some.inj (actor.symm.trans same))
    simp only [history, ownCompletions, List.filter_append, List.filter_cons, List.filter_nil,
      other, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · intro query sort owned
    exact congrFun tables.1 (.inr query) |>.symm
  · intro slot
    exact congrArg (fun catalog => catalog.lookup (owner, slot)) tables.2.1 |>.symm
  · intro candidate owned
    unfold State.HandleUnused
    change (∀ field, before.native.accepted field ≠ some candidate) ↔
      ∀ field, (before.native.completeFailure event eligible.2.1).accepted field ≠ some candidate
    rw [tables.1]
  · intro query sort owned
    change before.native.activatedAt query =
      (before.native.completeFailure event eligible.2.1).activatedAt query
    rw [before.native.completeFailure_activated event eligible.2.1 actor]
    symm
    cases stamp : before.native.activatedAt query with
    | some entered =>
        have beforeReady := (valid.activated_iff query).mp
          (by simp only [stamp, Option.isSome_some])
        exact State.refreshActivated_eq_of_ready _ before.native.clock
          before.native.activatedAt query entered
          ((ready query sort owned).mpr beforeReady.1) beforeReady.2 stamp
    | none =>
        have absent : ¬ (before.completeAutomatic event eligible.2).native.config.cut.Ready
            query := by
          intro requested
          have entered := (valid.activated_iff query).mpr
            ⟨(ready query sort owned).mp requested,
              by rw [(graph).actor?_of_outputLayout_binding owned]; rfl⟩
          simp only [stamp, Option.isSome_none, Bool.false_eq_true] at entered
        change ¬ (before.native.completeFailure event eligible.2.1).config.cut.Ready query at absent
        simp only [State.refreshActivated, absent, ↓reduceDIte]
  · exact tables.2.2.symm

theorem commitment_drain_frame (phase : RuntimePhase graph)
    (commitment : phase.kind = .commitment) (state : RecoveryState graph)
    (inputs : (graph).Inputs) (valid : state.native.Invariant inputs)
    (owner : Player) (survivor : owner ∉ state.excluded) :
    BindingFrame program owner state.native (phase.drain state).native := by
  have preserve : ∀ after, Relation.ReflTransGen phase.AutomaticStep state after →
      after.native.Invariant inputs ∧ after.excluded = state.excluded ∧
        BindingFrame program owner state.native after.native := by
    intro after path
    induction path with
    | refl => exact ⟨valid, rfl, BindingFrame.refl owner state.native⟩
    | @tail middle after path step ih =>
        obtain ⟨nativeValid, sameExcluded, frame⟩ := ih
        have next := automatic_commitment_frame program phase commitment middle after inputs
          nativeValid owner (by simpa only [sameExcluded] using survivor) step
        obtain ⟨event, eligible, rfl⟩ := step
        obtain ⟨who, acting, _⟩ := eligible.2.owned
        exact ⟨State.completeFailure_invariant nativeValid event eligible.2.1 acting,
          sameExcluded, frame.trans next⟩
  exact (preserve _ (phase.drain_trace state)).2.2

end Vegas.EventGraphRuntime.ReservedEpoch
