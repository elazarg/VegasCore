/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseExclusionRecord
import Vegas.Pending.PhaseLive
import Vegas.Pending.PhaseReadiness
import Vegas.Pending.PhasePlanSuffix

/-! # The actual current descriptor of a ready binding event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Ordered descriptor boundaries locate a ready binding in the current
commitment phase of every actual initialized history. -/
theorem phase_ready_binding_phase
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding who payload)
    (ready : control.execution.application.current.native.config.cut.Ready event) :
    ∃ phase remaining, control.execution.application.phases = phase :: remaining ∧
      phase.kind = .commitment ∧ event ∈ phase.events := by
  have exclusion := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler trace
  have live := (phaseApplication_live runtime leaks).history
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler (fun state member => by
      obtain ⟨initial, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact ⟨PhaseRuntimeState.initial_frontier plan initial,
        PhaseRuntimeState.initial_live plan initial⟩) trace
  have geometry := phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
    trace
  cases installed : control.execution.application.phases with
  | nil =>
      have terminal := exclusion.frontier.terminal installed
      exact (ready.1 (terminal.symm ▸ Finset.mem_univ event)).elim
  | cons phase remaining =>
      have head : phase ∈ control.execution.application.phases.head? := by
        rw [installed]
        exact Option.mem_some_iff.mpr rfl
      have position := exclusion.frontier.positioned
      rw [installed] at position
      rw [installed] at geometry
      have boundaries := PhaseRuntimeState.phase_boundaries phase remaining geometry.1
        geometry.2.1 geometry.2.2
      have inside := phase.ready_mem control.execution.application.current ordered position.2
        (live.2 phase head) boundaries.1 boundaries.2 event ready
      have typed := phase.fields event ((phase.mem_events event).mp inside).1
        ((phase.mem_events event).mp inside).2
      have kind : phase.kind = .commitment := by
        cases kind : phase.kind with
        | commitment => rfl
        | reveal =>
            rw [kind] at typed
            obtain ⟨value, layout⟩ := typed
            rw [binding] at layout
            cases layout
        | sample =>
            rw [kind] at typed
            obtain ⟨value, layout⟩ := typed
            rw [binding] at layout
            cases layout
      exact ⟨phase, remaining, rfl, kind, inside⟩

end Vegas.EventGraphRuntime
