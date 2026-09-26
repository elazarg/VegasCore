/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant
import Vegas.EventGraph.Sequential

/-! # Local deadlines between sequential events

Completing the current event makes its immediate successor ready and starts
that successor's clock at the actual completion time. Completing before the
block's ticks therefore ages the successor by exactly those ticks; completing
after them leaves its age zero. Increasing relative deadlines accommodate both
branches without assuming that the complete service calendar is timely.
-/

noncomputable section

namespace Vegas.EventOrder.Cut

/-- Completing the least unfinished event enables its immediate successor. -/
theorem ready_successor_after_complete {count : Nat}
    (cut : (EventOrder.sequential count).Cut) (event next : Fin count)
    (ready : cut.Ready event) (successor : next.val = event.val + 1) :
    (cut.complete event ready).Ready next := by
  constructor
  · intro completed
    rcases (mem_complete cut event ready next).mp completed with same | previous
    · have sameRank := congrArg Fin.val same
      omega
    · have before := (cut.mem_completed_iff_lt_of_ready ready).mp previous
      omega
  · intro prior member
    have before := (EventOrder.sequential.mem_predecessors prior next).mp member
    apply (mem_complete cut event ready prior).mpr
    by_cases same : prior.val = event.val
    · exact Or.inl (Fin.ext same)
    · exact Or.inr ((cut.mem_completed_iff_lt_of_ready ready).mpr (by omega))

end Vegas.EventOrder.Cut

namespace Vegas.EventGraphRuntime.State

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Clock ticks alone preserve the application invariant. -/
theorem Invariant.add_clock {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) (ticks : Nat) :
    ({ state with clock := state.clock + ticks } : State graph).Invariant inputs := by
  refine ⟨invariant.reachable, invariant.activated_iff, ?_⟩
  intro event entered activated
  have prior := invariant.activated_le event entered activated
  change entered ≤ state.clock + ticks
  omega

omit [DecidableEq Player] in
/-- Waiting a full relative deadline makes every already active event due,
regardless of how early its predecessor completed. -/
theorem Invariant.due_after_deadline {inputs : graph.Inputs} {state : State graph}
    (invariant : state.Invariant inputs) (runtime : EventGraphRuntime graph)
    (event : graph.EventId) (entered : Nat)
    (activated : state.activatedAt event = some entered) :
    runtime.deadline event ≤ state.clock + runtime.deadline event - entered := by
  have prior := invariant.activated_le event entered activated
  omega

/-- An initially ready strategic event has age zero. -/
theorem initial_withinDeadline (inputs : graph.Inputs) (runtime : EventGraphRuntime graph)
    (event : graph.EventId) (ready : (initial inputs).config.cut.Ready event)
    (strategic : (graph.actor? event).isSome = true) (positive : 0 < runtime.deadline event) :
    (initial inputs).WithinDeadline runtime event := by
  have invariant := initial_invariant inputs
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready strategic
  have bound := invariant.activated_le event entered activated
  change entered ≤ 0 at bound
  have zero : entered = 0 := by omega
  simp only [WithinDeadline, activated, zero]
  exact positive

omit [DecidableEq Player] in
/-- A different sequential event cannot already have an activation time while
the current event is ready. This prevents inheriting an older deadline. -/
theorem Invariant.successor_not_activated {inputs : graph.sequentialize.Inputs}
    {state : State graph.sequentialize} (invariant : state.Invariant inputs)
    (event next : graph.sequentialize.EventId) (ready : state.config.cut.Ready event)
    (successor : next.val = event.val + 1) : state.activatedAt next = none := by
  cases activated : state.activatedAt next with
  | none => rfl
  | some entered =>
      have nextReady := (invariant.activated_iff next).mp
        (by simp only [activated, Option.isSome_some]) |>.1
      have same := graph.sequentialize_ready_unique state.config.cut ready nextReady
      have sameRank := congrArg Fin.val same
      omega

omit [DecidableEq Player] in
/-- Completing a sequential event starts its successor's clock now, for every
action and result. In particular the result can be a withheld publication. -/
theorem complete_successor_activatedAt {inputs : graph.sequentialize.Inputs}
    (state : State graph.sequentialize) (invariant : state.Invariant inputs)
    (event next : graph.sequentialize.EventId) (ready : state.config.cut.Ready event)
    (successor : next.val = event.val + 1)
    (strategic : (graph.sequentialize.actor? next).isSome = true)
    (action : graph.sequentialize.Action event)
    (value : (graph.sequentialize.outputLayout event).Value) :
    (state.complete event ready action value).config.cut.Ready next ∧
      (state.complete event ready action value).activatedAt next = some state.clock := by
  have enabled := state.config.cut.ready_successor_after_complete event next ready successor
  change (state.config.complete event ready action value).cut.Ready next at enabled
  have absent := invariant.successor_not_activated event next ready successor
  refine ⟨enabled, ?_⟩
  change refreshActivated (state.config.complete event ready action value)
    state.clock state.activatedAt next = some state.clock
  rw [refreshActivated, dite_eq_left enabled]
  cases actor : graph.sequentialize.actor? next with
  | none => simp only [actor, Option.isSome_none, Bool.false_eq_true] at strategic
  | some owner => simp only [absent, Option.orElse_none]

omit [DecidableEq Player] in
/-- If completion occurs before the clock segment, the successor has exactly
the segment's age and is timely whenever its deadline exceeds that length. -/
theorem complete_successor_within_after_ticks {inputs : graph.sequentialize.Inputs}
    (runtime : EventGraphRuntime graph.sequentialize)
    (state : State graph.sequentialize) (invariant : state.Invariant inputs)
    (event next : graph.sequentialize.EventId) (ready : state.config.cut.Ready event)
    (successor : next.val = event.val + 1)
    (strategic : (graph.sequentialize.actor? next).isSome = true)
    (action : graph.sequentialize.Action event)
    (value : (graph.sequentialize.outputLayout event).Value)
    (ticks : Nat) (short : ticks < runtime.deadline next) :
    ({ state.complete event ready action value with clock := state.clock + ticks } :
      State graph.sequentialize).WithinDeadline runtime next := by
  have activated := (complete_successor_activatedAt state invariant event next ready successor
    strategic action value).2
  change (match (state.complete event ready action value).activatedAt next with
    | none => False
    | some entered => state.clock + ticks - entered < runtime.deadline next)
  rw [activated]
  simpa only [Nat.add_sub_cancel_left] using short

omit [DecidableEq Player] in
/-- If completion occurs after the clock segment, the successor starts with
age zero. The predecessor's withholding therefore cannot consume its deadline. -/
theorem ticks_complete_successor_within {inputs : graph.sequentialize.Inputs}
    (runtime : EventGraphRuntime graph.sequentialize)
    (state : State graph.sequentialize) (invariant : state.Invariant inputs)
    (event next : graph.sequentialize.EventId) (ready : state.config.cut.Ready event)
    (successor : next.val = event.val + 1)
    (strategic : (graph.sequentialize.actor? next).isSome = true)
    (action : graph.sequentialize.Action event)
    (value : (graph.sequentialize.outputLayout event).Value)
    (ticks : Nat) (positive : 0 < runtime.deadline next) :
    (({ state with clock := state.clock + ticks } : State graph.sequentialize).complete
      event ready action value).WithinDeadline runtime next := by
  have activated := (complete_successor_activatedAt
    ({ state with clock := state.clock + ticks } : State graph.sequentialize)
    (invariant.add_clock ticks) event next ready successor strategic action value).2
  unfold WithinDeadline
  rw [activated]
  change state.clock + ticks - (state.clock + ticks) < runtime.deadline next
  simpa only [Nat.sub_self] using positive

end Vegas.EventGraphRuntime.State
