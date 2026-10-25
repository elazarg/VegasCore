/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCheckpointAlignment
import Vegas.Pending.PhaseExclusionRecord

/-! # Unfinished singleton checkpoints have no new exclusion

The existing public-failure evidence would place any newly excluded owner at a
completed event beyond the saved prefix. Exact pre-completion alignment rules
that out under arbitrary actual raw histories.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

omit [DecidableEq Player] in
theorem ExclusionRecord.excluded_eq_of_same_config {state : PhaseRuntimeState graph}
    (record : state.ExclusionRecord) (phase : RuntimePhase graph)
    (head : state.phases.head? = some phase)
    (sameConfig : state.entry.native.config = state.current.native.config) :
    state.entry.excluded = state.current.excluded := by
  have saved : state.entry.native.config.cut.IsPrefix phase.low := by
    cases phases : state.phases with
    | nil => simp only [phases, List.head?_nil, reduceCtorEq] at head
    | cons installed remaining =>
        have same : installed = phase := by simpa only [phases, List.head?_cons,
          Option.some.injEq] using head
        subst installed
        have positioned := record.frontier.positioned
        rw [phases] at positioned
        exact positioned.1
  have evidence := record.installed phase (by rw [head]; rfl)
  ext owner
  constructor
  · exact fun member => (evidence.excluded owner).mpr (Or.inl member)
  · intro member
    rcases (evidence.excluded owner).mp member with previous | ⟨event, lower, acting, failed⟩
    · exact previous
    · have completed := failed.completed
      rw [← sameConfig] at completed
      have below := (saved.2 event).mp completed
      omega

end PhaseRuntimeState

/-- Actual raw histories identify exclusion as well as config and accepted
associations at every unfinished singleton phase. -/
theorem phaseCheckpointExcluded_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph)
    (head : control.execution.application.phases.head? = some phase)
    (event : graph.EventId) (only : phase.events = {event})
    (unfinished : event ∉ control.execution.application.current.native.config.cut.completed) :
    control.execution.application.entry.excluded =
      control.execution.application.current.excluded := by
  have record := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler trace
  exact record.excluded_eq_of_same_config phase head
    (phaseCheckpointAlignment_history runtime leaks plan inputs horizon scheduler trace
      phase head event only unfinished).1

end Vegas.EventGraphRuntime
