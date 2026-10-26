/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairContinuation

/-! # Supported passive environment steps of directed binding repair

Every actual pending-message sample has a paired supported sample because the
entire pending network is equal. Waiting and advancing the public clock also
have paired actual successors with the same directed repair frame.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

namespace DirectedBindingFrame

variable {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (application setup runtime leaks).Execution}

/-- The same actual pending-identifier sample extends both executions. No
independence or restriction on the pending-message observation law is needed. -/
theorem activate_step (frame : DirectedBindingFrame (runtime := runtime) memory owner original
  repaired)
    (actor : Player) (nextOriginal : (application setup runtime leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep (application setup runtime leaks)
      (.activate actor)).support) :
    ∃ nextRepaired : (application setup runtime leaks).Execution,
      nextRepaired ∈ (repaired.environmentStep (application setup runtime leaks)
        (.activate actor)).support ∧
      DirectedBindingFrame (runtime := runtime) memory owner nextOriginal nextRepaired := by
  rw [ReactiveApplication.Execution.activation_samples, PMF.support_map] at left
  obtain ⟨selected, supported, rfl⟩ := left
  refine ⟨repaired.sampledActivation (application setup runtime leaks) actor selected, ?_,
    frame.activate actor selected⟩
  rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
  refine ⟨selected, ?_, rfl⟩
  rw [← frame.network]
  exact supported

/-- Waiting records the same actual scheduler input and preserves all private
recalls. Its paired successor is determined by the runtime. -/
theorem wait_step (frame : DirectedBindingFrame (runtime := runtime) memory owner original repaired)
    (nextOriginal : (application setup runtime leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep (application setup runtime leaks)
      .wait).support) :
    ∃ nextRepaired : (application setup runtime leaks).Execution,
      nextRepaired ∈ (repaired.environmentStep (application setup runtime leaks) .wait).support ∧
      DirectedBindingFrame (runtime := runtime) memory owner nextOriginal nextRepaired := by
  have leftEq : nextOriginal = { original with environmentRecall := original.environmentRecall ++
      [⟨original.observeEnvironment (application setup runtime leaks), .wait⟩] } := by
    simpa only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff _ _] using left
  subst nextOriginal
  refine ⟨{ repaired with environmentRecall := repaired.environmentRecall ++
    [⟨repaired.observeEnvironment (application setup runtime leaks), .wait⟩] }, ?_, ?_⟩
  · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff _ _]
  · refine ⟨{ frame.toFrame with service := ?_ }, frame.recalled⟩
    change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
    rw [frame.service, frame.toFrame.environment]

/-- Advancing the actual public clock has a paired deterministic successor. -/
theorem advanceClock_step (frame : DirectedBindingFrame (runtime := runtime) memory owner original
  repaired)
    (nextOriginal : (application setup runtime leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep (application setup runtime leaks)
      (.application .advanceClock)).support) :
    ∃ nextRepaired : (application setup runtime leaks).Execution,
      nextRepaired ∈ (repaired.environmentStep (application setup runtime leaks)
        (.application .advanceClock)).support ∧
      DirectedBindingFrame (runtime := runtime) memory owner nextOriginal nextRepaired := by
  let next (execution : (application setup runtime leaks).Execution) :
      (application setup runtime leaks).Execution :=
    { execution with
      application := { execution.application with clock := execution.application.clock + 1 }
      environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment (application setup runtime leaks), .application
          .advanceClock⟩] }
  have law (execution : (application setup runtime leaks).Execution) :
      execution.environmentStep (application setup runtime leaks) (.application .advanceClock) =
        PMF.pure (next execution) := by
    have appLaw : (application setup runtime leaks).environment execution.application
      .advanceClock =
        PMF.pure { execution.application with clock := execution.application.clock + 1 } := rfl
    simp only [ReactiveApplication.Execution.environmentStep, appLaw, PMF.pure_map]
    rfl
  rw [law, PMF.mem_support_pure_iff] at left
  subst nextOriginal
  refine ⟨next repaired, ?_, frame.advanceClock⟩
  rw [law, PMF.mem_support_pure_iff]

end DirectedBindingFrame

end Vegas
