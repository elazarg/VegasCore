/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseAcceptedFrame
import Vegas.Pending.PhaseHistoryCheckpoint

/-! # Exact checkpoints before an unfinished singleton event

The existing stored-value and history-prefix invariants identify the whole
semantic configuration. The actual accepted-table footprint identifies every
association, including previously accepted unusable bindings.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem config_eq_of_same_cut_checkpoint (saved live : graph.Config)
    (sameCut : saved.cut = live.cut)
    (stored : ∀ field value, saved.store field = some value → live.store field = some value)
    (history : saved.history.IsPrefix live.history) : saved = live := by
  have inputs : saved.inputs = live.inputs := by
    funext input
    have value := stored (.inl input) (saved.inputs input) rfl
    change some (live.inputs input) = some (saved.inputs input) at value
    exact (Option.some.inj value).symm
  have outputs : saved.outputs = live.outputs := by
    funext event
    cases savedValue : saved.outputs event with
    | none =>
        cases liveValue : live.outputs event with
        | none => rfl
        | some value =>
            have completed : event ∈ live.cut.completed :=
              (live.output_available event).mp (by rw [liveValue]; rfl)
            have present := (saved.output_available event).mpr
              (by rw [sameCut]; exact completed)
            rw [savedValue] at present
            cases present
    | some value => exact (stored (.inr event) value savedValue).symm
  have histories : saved.history = live.history := by
    obtain ⟨tail, joined⟩ := history
    have empty : tail = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro completion member
      have after : completion.event ∈ live.history.map Completion.event :=
        List.mem_map.mpr ⟨completion, by rw [← joined]; exact List.mem_append_right _ member, rfl⟩
      have before : completion.event ∈ saved.history.map Completion.event :=
        (saved.history_exact _).mpr (by
          rw [sameCut]
          exact (live.history_exact _).mp after)
      have distinct := live.history_nodup
      rw [← joined, List.map_append] at distinct
      exact (List.nodup_append.mp distinct).2.2 completion.event before completion.event
        (List.mem_map.mpr ⟨completion, member, rfl⟩) rfl
    simpa only [empty, List.append_nil] using joined
  cases saved
  cases live
  cases inputs
  cases sameCut
  cases outputs
  cases histories
  rfl

namespace PhaseRuntimeState

omit [DecidableEq Player] in
/-- An unfinished singleton has no semantic or association change relative to
its actual saved checkpoint. Physical preparations and clock changes remain free. -/
theorem checkpoint_eq_of_singleton_unfinished (state : PhaseRuntimeState graph)
    (frontier : state.Frontier) (stored : state.StoredCheckpoint)
    (history : state.HistoryCheckpoint) (accepted : state.AcceptedCheckpointFrame)
    (phase : RuntimePhase graph) (head : state.phases.head? = some phase)
    (event : graph.EventId) (only : phase.events = {event})
    (unfinished : event ∉ state.current.native.config.cut.completed) :
    state.entry.native.config = state.current.native.config ∧
      state.entry.native.accepted = state.current.native.accepted := by
  have positioned : state.entry.native.config.cut.IsPrefix phase.low ∧
      state.current.native.config.cut.Within phase.low phase.high := by
    cases phases : state.phases with
    | nil => simp only [phases, List.head?_nil, reduceCtorEq] at head
    | cons installed remaining =>
        have same : installed = phase := by simpa only [phases, List.head?_cons,
          Option.some.injEq] using head
        subst installed
        simpa only [Positioned, phases] using frontier.positioned
  have sameCut : state.entry.native.config.cut = state.current.native.config.cut := by
    apply EventOrder.Cut.ext
    ext other
    constructor
    · intro completed
      exact positioned.2.1 other ((positioned.1.2 other).mp completed)
    · intro completed
      apply (positioned.1.2 other).mpr
      by_contra notBefore
      have inside : other ∈ phase.events :=
        (phase.mem_events _).mpr ⟨Nat.le_of_not_gt notBefore, positioned.2.2 other completed⟩
      have same := Finset.mem_singleton.mp ((Finset.ext_iff.mp only _).mp inside)
      subst other
      exact unfinished completed
  exact ⟨config_eq_of_same_cut_checkpoint _ _ sameCut stored history,
    (accepted.eq_of_singleton phase head event only unfinished).symm⟩

end PhaseRuntimeState

/-- Every initialized raw history supplies exact checkpoint alignment before
an unfinished singleton, independently of source honesty or a count menu. -/
theorem phaseCheckpointAlignment_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph)
    (head : control.execution.application.phases.head? = some phase)
    (event : graph.EventId) (only : phase.events = {event})
    (unfinished : event ∉ control.execution.application.current.native.config.cut.completed) :
    control.execution.application.entry.native.config =
        control.execution.application.current.native.config ∧
      control.execution.application.entry.native.accepted =
        control.execution.application.current.native.accepted := by
  have frontier := (phaseApplication_frontier runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_frontier plan draw) trace
  exact control.execution.application.checkpoint_eq_of_singleton_unfinished frontier
    (phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler trace)
    (phaseHistoryCheckpoint_history runtime leaks plan inputs horizon scheduler trace)
    (phaseAcceptedCheckpointFrame_history runtime leaks plan inputs horizon scheduler trace)
    phase head event only unfinished

end Vegas.EventGraphRuntime
