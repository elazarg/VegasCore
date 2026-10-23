/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseStoredCheckpoint
import Vegas.Pending.PhaseBindingCountTransport

/-! # Physical preparations at an older saved semantic frontier -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

omit [DecidableEq Player] in
/-- A genuinely ready live binding has no saved completion: every saved cell
is still present in the live store, whereas readiness excludes its own output. -/
theorem saved_uncompleted_of_ready (state : PhaseRuntimeState graph)
    (stored : state.StoredCheckpoint) (event : graph.EventId)
    (ready : state.current.native.config.cut.Ready event) :
    event ∉ state.entry.native.config.cut.completed := by
  intro completed
  have present := (state.entry.native.config.output_available event).mpr completed
  cases value : state.entry.native.config.outputs event with
  | none => simp only [value, Option.isSome_none, Bool.false_eq_true] at present
  | some result =>
      have after : state.current.native.config.outputs event = some result :=
        stored (.inr event) result value
      apply ready.1
      apply (state.current.native.config.output_available event).mp
      rw [after]
      rfl

variable {runtime leaks}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

end Vegas.EventGraphRuntime.PhaseBindingRepair
