/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingOpeningResponse

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

/-- The native clock frame lifts simultaneously to the live execution and its
unchanged saved semantic checkpoint. -/
theorem clock (frame : Frame runtime leaks memory owner original repaired) :
    Frame runtime leaks memory owner
      (PhaseRuntimeState.normalizeExecution runtime leaks (rawClock runtime leaks original))
      (PhaseRuntimeState.normalizeExecution runtime leaks (rawClock runtime leaks repaired)) := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let left := rawClock runtime leaks original
  let right := rawClock runtime leaks repaired
  have native := frame.live.advanceClock
  dsimp only at native
  rw [PhaseBindingRepair.observeEnvironment runtime leaks original,
    PhaseBindingRepair.observeEnvironment runtime leaks repaired] at native
  have live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      (execution runtime leaks left) (execution runtime leaks right) := by
    simpa only [left, right, rawClock, execution, List.map_append, List.map_cons, List.map_nil,
      environmentEntry, command] using native
  have savedLeft : (checkpoint runtime leaks left).application =
      (checkpoint runtime leaks original).application := rfl
  have savedRight : (checkpoint runtime leaks right).application =
      (checkpoint runtime leaks repaired).application := rfl
  have saved : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      (checkpoint runtime leaks left) (checkpoint runtime leaks right) := by
    apply checkpointFrame live (checkpoint runtime leaks left).application
      (checkpoint runtime leaks right).application
    · rw [savedRight, savedLeft]
      exact congrArg ReactiveApplication.PlayerView.application frame.saved.observed
    · rw [savedLeft, savedRight]
      exact frame.saved.views
    · rw [savedLeft, savedRight]
      exact frame.saved.slots
    · rw [savedLeft, savedRight]
      exact frame.saved.successful
  have service : left.environmentRecall = right.environmentRecall := by
    change original.environmentRecall ++
        [⟨original.observeEnvironment app, .application .advanceClock⟩] =
      repaired.environmentRecall ++ [⟨repaired.observeEnvironment app, .application .advanceClock⟩]
    rw [frame.service, frame.environment_input]
  have raw : Frame runtime leaks memory owner left right :=
    ⟨live, saved, frame.phases, frame.generation, frame.clearOriginal, frame.clearRepaired,
      frame.archiveOriginal, frame.archiveRepaired, frame.network, service, frame.foreignRecall⟩
  exact raw.normalize

/-- Clock replay extends the actual repaired history with the atom chosen by
the unchanged original scheduler. -/
theorem clock_trace (frame : Frame runtime leaks memory owner original repaired)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (prior : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, repaired⟩))
    (selected : ((.application .advanceClock) : (phaseApplication runtime leaks).Command) ∈
      (scheduler original.environmentRecall
        (original.observeEnvironment (phaseApplication runtime leaks))).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none,
        PhaseRuntimeState.normalizeExecution runtime leaks
          (rawClock runtime leaks repaired)⟩)) := by
  have chosen : ((.application .advanceClock) : (phaseApplication runtime leaks).Command) ∈
      (scheduler repaired.environmentRecall
        (repaired.observeEnvironment (phaseApplication runtime leaks))).support := by
    rw [← frame.scheduler_law scheduler]
    exact selected
  apply menu.trace_environment initial horizon scheduler remaining repaired _
    (.application .advanceClock) prior chosen
  rw [clock_environment, PMF.mem_support_pure_iff]

end Frame

end Vegas.EventGraphRuntime.PhaseBindingRepair
