/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseFrontier

/-! # Actual native reachability throughout phased recovery histories -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every initialized phased history retains genuine native reachability for
one fixed initial draw, including all semantic rollbacks and automatic drains. -/
theorem phaseNativeInvariant_history {graph : Vegas.EventGraph Player L}
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    ∃ draw, control.execution.application.Invariant draw := by
  have invariant : (phaseApplication runtime leaks).Invariant
      (fun state => ∃ draw, state.Invariant draw) := by
    refine ⟨?_, ?_, ?_⟩
    · intro state who submission valid
      obtain ⟨draw, valid⟩ := valid
      exact ⟨draw, (phaseApplication_invariant runtime leaks draw).submit
        state who submission valid⟩
    · intro state message next valid handled
      obtain ⟨draw, valid⟩ := valid
      exact ⟨draw, (phaseApplication_invariant runtime leaks draw).handle
        state message next valid handled⟩
    · intro state command next valid reached
      obtain ⟨draw, valid⟩ := valid
      exact ⟨draw, (phaseApplication_invariant runtime leaks draw).environment
        state command next valid reached⟩
  apply invariant.history _ horizon scheduler ?_ trace
  intro state member
  obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  exact ⟨draw, (PhaseRuntimeState.initial_invariant plan draw).1⟩

end Vegas.EventGraphRuntime
