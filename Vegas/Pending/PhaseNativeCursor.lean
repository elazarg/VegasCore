/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeProjection
import Vegas.Pending.PhaseLive

/-! # Recovering the clear phase cursor from native public completion data -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

open Classical in
/-- The first static interval with an unfinished event is the installed clear phase. -/
def phaseAt (plan : RuntimePhasePlan graph) (view : PublicView graph) :
    Option (RuntimePhase graph) :=
  plan.phases.find? fun phase => decide (∃ event ∈ phase.events,
    event ∉ view.observation.completionOrder)

open Classical in
/-- Reconstruct only public phase metadata, without reading any private source state. -/
def restorePublic (plan : RuntimePhasePlan graph) (view : PublicView graph) :
    PhasePublicView graph :=
  ⟨view, ∅, (phaseAt plan view).map fun phase => (phase.kind, phase.low, phase.high),
    ⟨((phaseAt plan view).map RuntimePhase.low).getD graph.order.eventCount, 0⟩, []⟩

omit [DecidableEq Player] in
private theorem prefix_high_le (earlierPhases : List (RuntimePhase graph))
    (phase : RuntimePhase graph)
    (tail : List (RuntimePhase graph))
    (ordered : (earlierPhases ++ phase :: tail).IsChain fun before after => before.high = after.low)
    (earlier : RuntimePhase graph) (member : earlier ∈ earlierPhases) :
    earlier.high ≤ phase.low := by
  induction earlierPhases generalizing earlier with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst earlier
        exact RuntimePhasePlan.high_le_of_mem_tail first (rest ++ phase :: tail) ordered phase
          (by simp only [List.mem_append, List.mem_cons, true_or, or_true])
      · exact ih ordered.tail earlier later

omit [DecidableEq Player] in
theorem phaseAt_publicView (plan : RuntimePhasePlan graph) (state : PhaseRuntimeState graph)
    (suffix : state.phases <:+ plan.phases) (frontier : state.Frontier) (live : state.Live) :
    phaseAt plan state.current.native.publicView = state.phases.head? := by
  classical
  cases phases : state.phases with
  | nil =>
      have terminal : state.current.native.config.cut.Terminal := frontier.terminal phases
      apply List.find?_eq_none.mpr
      intro phase _member unfinished
      obtain ⟨event, _inside, missing⟩ := of_decide_eq_true unfinished
      apply missing
      apply (state.current.native.config.history_exact event).mpr
      rw [terminal]
      exact Finset.mem_univ event
  | cons phase tail =>
      have within := frontier.positioned
      change PhaseRuntimeState.Positioned state.phases state.entry state.current at within
      rw [phases] at within
      obtain ⟨earlierPhases, whole⟩ := suffix
      rw [phases] at whole
      have ordered : (earlierPhases ++ phase :: tail).IsChain
          (fun before after => before.high = after.low) := by
        rw [whole]
        exact plan.adjacent
      have currentUnfinished : ∃ event ∈ phase.events,
          event ∉ state.current.native.publicView.observation.completionOrder := by
        have notFinished := live phase (by simp only [phases, List.head?_cons, Option.mem_some_iff])
        change ¬ phase.events ⊆ state.current.native.config.cut.completed at notFinished
        have missingEvent : ∃ event, event ∈ phase.events ∧
            event ∉ state.current.native.config.cut.completed := by
          by_contra absent
          apply notFinished
          intro event inside
          by_contra missing
          exact absent ⟨event, inside, missing⟩
        obtain ⟨event, inside, missing⟩ := missingEvent
        exact ⟨event, inside, fun listed => missing
          ((state.current.native.config.history_exact event).mp listed)⟩
      apply List.find?_eq_some_iff_append.mpr
      refine ⟨decide_eq_true currentUnfinished, earlierPhases, tail, whole.symm, ?_⟩
      intro earlier member
      have absent : ¬ ∃ event ∈ earlier.events,
          event ∉ state.current.native.publicView.observation.completionOrder := by
        rintro ⟨event, inside, missing⟩
        have before := prefix_high_le earlierPhases phase tail ordered earlier member
        have below := ((earlier.mem_events event).mp inside).2.trans_le before
        exact missing ((state.current.native.config.history_exact event).mpr
          (within.2.1 event below))
      simp only [absent, decide_false, Bool.not_false]

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

omit [DecidableEq Player] in
theorem restorePublic_of_clear (state : PhaseRuntimeState graph)
    (suffix : state.phases <:+ plan.phases) (frontier : state.Frontier) (live : state.Live)
    (generation : state.generation = 0) (retired : state.retired = [])
    (clear : state.current.excluded = ∅) :
    restorePublic plan state.current.native.publicView = state.publicView := by
  classical
  simp only [restorePublic, phaseAt_publicView plan state suffix frontier live,
    PhaseRuntimeState.publicView, PhaseRuntimeState.attempt, generation, retired,
    List.map_nil, clear]

/-- Lift native scheduler observations by the uniquely recovered static metadata. -/
def liftEnvironmentView (view : (N).EnvironmentView) : (P).EnvironmentView :=
  ⟨view.network.mapPayload plan.stampPacket, restorePublic plan view.application, view.receipts⟩

/-- All retained public packet tags and the current cursor are recovered exactly. -/
theorem liftEnvironmentView_of_clear [Fintype Player] (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) :
    liftEnvironmentView runtime leaks plan
        (environmentView runtime leaks plan (current.execution.observeEnvironment P)) =
      current.execution.observeEnvironment P := by
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler raw
  have frontier := (phaseApplication_live runtime leaks).history _ horizon scheduler
    (fun state supported => by
      obtain ⟨input, _support, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_frontier plan input,
        PhaseRuntimeState.initial_live plan input⟩)
      raw
  have archive := phase_clear_history runtime leaks plan inputs horizon scheduler current raw clear
  have metadata := restorePublic_of_clear plan current.execution.application suffix
    frontier.1 frontier.2 archive.1 archive.2 clear
  have network := congrArg MessageNetwork.publicView
    (network_retag_of_clear runtime leaks plan bounds inputs horizon scheduler trace clear)
  change (⟨_, _, _⟩ : (P).EnvironmentView) = ⟨_, _, _⟩
  erw [metadata]
  exact congrArg (fun visible => (⟨visible, current.execution.application.publicView,
    current.execution.receipts⟩ : (P).EnvironmentView)) network

end Vegas.EventGraphRuntime.PhaseNativeProjection
