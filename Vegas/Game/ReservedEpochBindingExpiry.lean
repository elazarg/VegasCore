/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingFrame

/-! # Paired owned binding completion and actual deadline expiry -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem BindingFrame.complete_owned {owner : Player} {left right : State graph}
    (frame : BindingFrame program owner left right) (event : (graph).EventId)
    (payload : L.Ty) (binding : (graph).outputLayout event = .binding owner payload)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (action : (graph).Action event) (value : ((graph).outputLayout event).Value) :
    BindingFrame program owner (left.complete event leftReady action value)
      (right.complete event rightReady action value) := by
  have ready (query : (graph).EventId) (sort : L.Ty)
      (typed : (graph).outputLayout query = .binding owner sort) :
      (left.config.complete event leftReady action value).cut.Ready query ↔
        (right.config.complete event rightReady action value).cut.Ready query := by
    apply binding_ready_congr program _ _ query owner sort typed
    intro prior cone
    change prior ∈ (left.config.cut.complete event leftReady).completed ↔
      prior ∈ (right.config.cut.complete event rightReady).completed
    rw [EventOrder.Cut.mem_complete, EventOrder.Cut.mem_complete]
    exact or_congr Iff.rfl (frame.completed sort prior cone)
  constructor
  · exact frame.inputs
  · intro query visible
    have different : query ≠ event := by
      rintro rfl
      rw [binding] at visible
      exact visible
    change (left.config.complete event leftReady action value).outputs query =
      (right.config.complete event rightReady action value).outputs query
    rw [Config.complete_output_of_ne _ _ _ _ _ _ different,
      Config.complete_output_of_ne _ _ _ _ _ _ different]
    exact frame.publicOutputs query visible
  · intro query sort typed
    change (left.config.complete event leftReady action value).outputs query =
      (right.config.complete event rightReady action value).outputs query
    by_cases same : query = event
    · subst query
      simp only [Config.complete_output_same]
    · rw [Config.complete_output_of_ne _ _ _ _ _ _ same,
        Config.complete_output_of_ne _ _ _ _ _ _ same]
      exact frame.ownerOutputs query sort typed
  · have own := frame.ownHistory
    change left.config.history.filter _ = right.config.history.filter _ at own
    simp only [State.complete, Config.complete, ownCompletions, List.filter_append, own]
  · exact frame.accepted
  · exact frame.candidates
  · exact frame.unused
  · intro query sort typed
    change State.refreshActivated (left.config.complete event leftReady action value)
        left.clock left.activatedAt query =
      State.refreshActivated (right.config.complete event rightReady action value)
        right.clock right.activatedAt query
    simp only [State.refreshActivated, dite_eq_ite]
    by_cases requested : (left.config.complete event leftReady action value).cut.Ready query
    · have counterpart := (ready query sort typed).mp requested
      simp only [ite_eq_left requested, ite_eq_left counterpart, frame.clock,
        frame.activated query sort typed]
    · have counterpart : ¬ (right.config.complete event rightReady action value).cut.Ready query :=
        fun actual => requested ((ready query sort typed).mpr actual)
      simp only [ite_eq_right requested, ite_eq_right counterpart]
  · exact frame.clock

theorem BindingFrame.advance_clock {owner : Player} {left right : State graph}
    (frame : BindingFrame program owner left right) :
    BindingFrame program owner { left with clock := left.clock + 1 }
      { right with clock := right.clock + 1 } where
  inputs := frame.inputs
  publicOutputs := frame.publicOutputs
  ownerOutputs := frame.ownerOutputs
  ownHistory := frame.ownHistory
  accepted := frame.accepted
  candidates := frame.candidates
  unused := frame.unused
  activated := frame.activated
  clock := congrArg (fun clock => clock + 1) frame.clock

theorem BindingFrame.expire_owned {owner : Player} {left right : State graph}
    (frame : BindingFrame program owner left right) (runtime : EventGraphRuntime graph)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (nextLeft nextRight : State graph)
    (first : nextLeft ∈ (environmentStep runtime left (.expire event)).support)
    (second : nextRight ∈ (environmentStep runtime right (.expire event)).support) :
    BindingFrame program owner nextLeft nextRight := by
  have code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind owner payload := by
    generalize cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) = body
    cases body
    rfl
  have node := nodeView_eq_bind binding code
  by_cases leftReady : left.config.cut.Ready event
  · have rightReady := (frame.ready event payload binding).mp leftReady
    cases entered : left.activatedAt event with
    | none =>
        have rightEntered := (frame.activated event payload binding).symm.trans entered
        rw [environmentStep_expire_of_not_activated runtime left event leftReady entered,
          PMF.mem_support_pure_iff _ _] at first
        rw [environmentStep_expire_of_not_activated runtime right event rightReady rightEntered,
          PMF.mem_support_pure_iff _ _] at second
        subst nextLeft
        subst nextRight
        exact frame
    | some clock =>
        have rightEntered := (frame.activated event payload binding).symm.trans entered
        by_cases due : runtime.deadline event ≤ left.clock - clock
        · have rightDue : runtime.deadline event ≤ right.clock - clock := by
            rw [← frame.clock]
            exact due
          rw [environmentStep_expire_bind_eq runtime left event leftReady clock entered due
            owner payload binding code node, PMF.mem_support_pure_iff _ _] at first
          rw [environmentStep_expire_bind_eq runtime right event rightReady clock rightEntered
            rightDue owner payload binding code node, PMF.mem_support_pure_iff _ _] at second
          subst nextLeft
          subst nextRight
          exact BindingFrame.complete_owned program frame event payload binding
            leftReady rightReady _ _
        · have rightNotDue : ¬ runtime.deadline event ≤ right.clock - clock := by
            rw [← frame.clock]
            exact due
          rw [environmentStep_expire_of_not_due runtime left event leftReady clock entered due,
            PMF.mem_support_pure_iff _ _] at first
          rw [environmentStep_expire_of_not_due runtime right event rightReady clock rightEntered
            rightNotDue, PMF.mem_support_pure_iff _ _] at second
          subst nextLeft
          subst nextRight
          exact frame
  · have rightNotReady : ¬ right.config.cut.Ready event :=
      fun ready => leftReady ((frame.ready event payload binding).mpr ready)
    rw [environmentStep_expire_of_not_ready runtime left event leftReady,
      PMF.mem_support_pure_iff _ _] at first
    rw [environmentStep_expire_of_not_ready runtime right event rightNotReady,
      PMF.mem_support_pure_iff _ _] at second
    subst nextLeft
    subst nextRight
    exact frame

end Vegas.EventGraphRuntime.ReservedEpoch
