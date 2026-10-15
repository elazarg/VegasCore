/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingDelayedRepair
import Interaction.ReactiveRoundTrace

/-! # The original scheduler supplies actual repaired delayed-inclusion histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Every actual scheduler atom is unchanged by the directed frame. This is an
equality of the original scheduler laws, not a substituted scheduler policy. -/
theorem scheduler_law (frame : Frame runtime leaks memory owner original repaired)
    (scheduler : (phaseApplication runtime leaks).Scheduler) :
    scheduler original.environmentRecall
        (original.observeEnvironment (phaseApplication runtime leaks)) =
      scheduler repaired.environmentRecall
        (repaired.observeEnvironment (phaseApplication runtime leaks)) := by
  rw [frame.service, frame.environment_input]

/-- A selected delayed inclusion extends the already constructed repaired
prefix under the same original scheduler. Target transition support is derived
from the actual deterministic include operation. -/
theorem include_trace (frame : Frame runtime leaks memory owner original repaired)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (prior : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, repaired⟩)) (id : MessageId Player)
    (selected : (ReactiveApplication.Command.include id) ∈
      (scheduler original.environmentRecall
        (original.observeEnvironment (phaseApplication runtime leaks))).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none,
        { repaired.includePending (phaseApplication runtime leaks) id with
          environmentRecall := repaired.environmentRecall ++
            [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }⟩)) := by
  have chosen : (ReactiveApplication.Command.include id) ∈
      (scheduler repaired.environmentRecall
        (repaired.observeEnvironment (phaseApplication runtime leaks))).support := by
    rw [← frame.scheduler_law scheduler]
    exact selected
  apply menu.trace_environment initial horizon scheduler remaining repaired _ (.include id)
    prior chosen
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.mem_support_pure_iff]

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
