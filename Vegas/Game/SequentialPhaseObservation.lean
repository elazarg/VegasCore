/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialRuntimePhases
import Vegas.Pending.PhaseClearMetadata
import Vegas.Pending.PhaseLive
import Vegas.Pending.PhasePlanSuffix
import Mathlib.Order.Interval.Finset.Fin

/-! # Singleton phase identity read from the native public observation

At a live singleton frontier the completion-order length is the current source
rank. Before exclusion the archive is empty and the generation is zero, so the
entire phase public application view is reconstructed from the native public
view and exclusion mask. The history theorem covers arbitrary raw deviations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.SequentialPhaseObservation

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem history_length_of_prefix {graph : Vegas.EventGraph Player L}
    (config : graph.Config) {length : Nat} (orderedPrefix : config.cut.IsPrefix length) :
    config.history.length = length := by
  have same : (config.history.map Completion.event).toFinset = config.cut.completed := by
    ext event
    simpa only [List.mem_toFinset] using config.history_exact event
  have counted : config.cut.completed.card = config.history.length := by
    rw [← same, List.toFinset_card_of_nodup config.history_nodup, List.length_map]
  have bounded := orderedPrefix.1
  by_cases inside : length < graph.order.eventCount
  · let boundary : graph.EventId := ⟨length, inside⟩
    have initial : config.cut.completed = Finset.Iio boundary := by
      ext event
      simpa only [Finset.mem_Iio, Fin.lt_def] using orderedPrefix.2 event
    rw [initial, Fin.card_Iio] at counted
    exact counted.symm
  · have final : length = graph.order.eventCount := by omega
    have terminal : config.cut.completed = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro event
      exact (orderedPrefix.2 event).mpr (by omega)
    rw [terminal, Finset.card_univ, Fintype.card_fin] at counted
    exact counted.symm.trans final.symm

omit [DecidableEq Player] in
private theorem singleton_live_prefix {graph : Vegas.EventGraph Player L}
    (phase : RuntimePhase graph) (state : RecoveryState graph)
    (within : state.native.config.cut.Within phase.low phase.high)
    (singleton : phase.high = phase.low + 1) (live : ¬ phase.Finished state) :
    state.native.config.cut.IsPrefix phase.low := by
  classical
  have missing : ∃ event ∈ phase.events, event ∉ state.native.config.cut.completed := by
    by_contra absent
    apply live
    intro event member
    by_contra incomplete
    exact absent ⟨event, member, incomplete⟩
  obtain ⟨missing, member, incomplete⟩ := missing
  have bounds := (phase.mem_events missing).mp member
  refine ⟨phase.nonempty.le.trans phase.bounded, fun event => ⟨?_, within.1 event⟩⟩
  intro completed
  have upper := within.2 event completed
  by_contra below
  have same : event = missing := Fin.ext (by omega)
  exact incomplete (same ▸ completed)

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "G" => EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.sequential

/-- The static descriptor at the first rank absent from the public completion order. -/
def descriptor (native : PublicView G) : Option (RuntimePhaseKind × Nat × Nat) :=
  if available : native.observation.completionOrder.length < eventCount program then
    let phase := sequentialRuntimePhaseAt program
      ⟨native.observation.completionOrder.length, available⟩
    some (phase.kind, phase.low, phase.high)
  else none

/-- The public phase data reconstructed solely from the recovery public input. -/
def publicView (native : PublicView G) (excluded : Finset Player) : PhasePublicView G where
  native
  excluded
  phase := descriptor program native
  attempt := ⟨native.observation.completionOrder.length, 0⟩
  retired := []

/-- A live singleton frontier fixes both the descriptor and source address. -/
theorem descriptor_of_frontier (state : PhaseRuntimeState G)
    (frontier : state.Frontier) (live : state.Live)
    (suffix : state.phases <:+ (sequentialRuntimePhasePlan program).phases) :
    state.publicView.phase = descriptor program state.current.native.publicView ∧
      state.attempt.phase =
        state.current.native.publicView.observation.completionOrder.length := by
  cases installed : state.phases with
  | nil =>
      have orderedPrefix := frontier.positioned
      rw [installed] at orderedPrefix
      have length := history_length_of_prefix state.current.native.config orderedPrefix
      change state.current.native.config.history.length = eventCount program at length
      simp only [PhaseRuntimeState.publicView, PhaseRuntimeState.attempt, installed,
        List.head?_nil, Option.map_none, Option.getD_none]
      constructor
      · simp only [descriptor, State.publicView, EventGraph.publicObserve, List.length_map,
          length, Nat.lt_irrefl, ↓reduceDIte]
      · simp only [State.publicView, EventGraph.publicObserve, List.length_map]
        change eventCount program = state.current.native.config.history.length
        exact length.symm
  | cons phase rest =>
      have head : phase ∈ state.phases.head? := by
        simp only [installed, List.head?_cons, Option.mem_some_iff]
      have member := suffix.subset (List.mem_of_mem_head? head)
      obtain ⟨index, same⟩ := (mem_sequentialRuntimePhasePlan program phase).mp member
      have positioned := frontier.positioned
      rw [installed] at positioned
      have singleton := sequentialRuntimePhasePlan_singleton program phase member
      have orderedPrefix := singleton_live_prefix phase state.current positioned.2 singleton
        (live phase head)
      have length := history_length_of_prefix state.current.native.config orderedPrefix
      have rank : state.current.native.config.history.length = index.val := by
        simpa only [same, sequentialRuntimePhaseAt] using length
      simp only [PhaseRuntimeState.publicView, PhaseRuntimeState.attempt, installed,
        List.head?_cons, Option.map_some, Option.getD_some]
      constructor
      · simp only [descriptor, State.publicView, EventGraph.publicObserve, List.length_map,
          rank, index.isLt, ↓reduceDIte, Fin.eta, same]
      · simpa only [State.publicView, EventGraph.publicObserve, List.length_map, same,
          sequentialRuntimePhaseAt] using rank.symm

/-- The reconstructed public input equals the actual phase view at a clear live frontier. -/
theorem publicView_of_frontier (state : PhaseRuntimeState G)
    (frontier : state.Frontier) (live : state.Live)
    (suffix : state.phases <:+ (sequentialRuntimePhasePlan program).phases)
    (generation : state.generation = 0) (retired : state.retired = []) :
    state.publicView =
      publicView program state.current.native.publicView state.current.excluded := by
  obtain ⟨phase, address⟩ := descriptor_of_frontier program state frontier live suffix
  have attempt : state.attempt =
      ⟨state.current.native.publicView.observation.completionOrder.length, 0⟩ := by
    cases named : state.attempt with
    | mk source retry =>
        have sourceEq : source =
            state.current.native.publicView.observation.completionOrder.length := by
          simpa only [named] using address
        have retryEq : retry = 0 := by
          have current : state.attempt.generation = state.generation := rfl
          simpa only [named, generation] using current
        exact congrArg₂ CommitAttemptId.mk sourceEq retryEq
  change (⟨state.current.native.publicView, state.current.excluded,
      state.phases.head?.map (fun phase => (phase.kind, phase.low, phase.high)), state.attempt,
      state.retired.map (fun record => (record.attempt, record.state.publicView))⟩ :
        PhasePublicView G) = _
  rw [← show state.publicView.phase =
      state.phases.head?.map (fun phase => (phase.kind, phase.low, phase.high)) from rfl,
    phase, attempt, retired]
  rfl

/-- Every actual clear raw history has the exact public view reconstructed from its
native observation; no honesty, service or selected-anchor premise is used. -/
theorem publicView_history (runtime : EventGraphRuntime G)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket G))
    (inputs : PMF (G).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    control.execution.application.publicView =
      publicView program control.execution.application.current.native.publicView ∅ := by
  have frontierLive := (phaseApplication_live runtime leaks).history _ horizon scheduler
    (fun state member => by
      obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
      exact ⟨PhaseRuntimeState.initial_frontier _ draw, PhaseRuntimeState.initial_live _ draw⟩)
    trace
  have suffix := phasePlanSuffix_history runtime leaks (sequentialRuntimePhasePlan program)
    inputs horizon scheduler trace
  obtain ⟨generation, retired⟩ := phaseClearMetadata_history runtime leaks
    (sequentialRuntimePhasePlan program) inputs horizon scheduler trace clear
  simpa only [clear] using publicView_of_frontier program control.execution.application
    frontierLive.1 frontierLive.2 suffix generation retired

end Vegas.EventGraphRuntime.SequentialPhaseObservation
