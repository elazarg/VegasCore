/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingInertResponse

/-! # Actual physical clock commands through directed binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Clock advancement before actual automatic phase installation. The saved
semantic clock remains the original checkpoint clock. -/
def rawClock (physical : (phaseApplication runtime leaks).Execution) :
    (phaseApplication runtime leaks).Execution :=
  { physical with
    application := { physical.application with current :=
      { physical.application.current with native :=
        { physical.application.current.native with
          clock := physical.application.current.native.clock + 1 } } }
    environmentRecall := physical.environmentRecall ++
      [⟨physical.observeEnvironment (phaseApplication runtime leaks), .application .advanceClock⟩] }

/-- The real environment kernel performs the raw clock edge and then its
existing normalizer, including the original physical scheduler observation. -/
theorem clock_environment (physical : (phaseApplication runtime leaks).Execution) :
    physical.environmentStep (phaseApplication runtime leaks) (.application .advanceClock) =
      PMF.pure (PhaseRuntimeState.normalizeExecution runtime leaks (rawClock runtime leaks
        physical)) := by
  simp only [ReactiveApplication.Execution.environmentStep, phaseApplication,
    PhaseRuntimeState.environment, PhaseRuntimeState.commandAllowed, ite_true, environmentStep,
    PMF.pure_map]
  rfl

namespace Frame

variable {runtime leaks}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

end Frame

end Vegas.EventGraphRuntime.PhaseBindingRepair
