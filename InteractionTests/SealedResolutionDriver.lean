/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionDriver

/-! # Exact stopping-state regressions for the pending-message round driver -/

noncomputable section

namespace InteractionTests.SealedResolutionDriver

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

private def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩]⟩, none, 2⟩

private def players : Bool → runtime.messageApplication.PlayerPolicy :=
  fun _ _ _ => FinDist.pure .wait

private def wire : runtime.messageApplication.WirePolicy :=
  fun _ _ => FinDist.pure .wait

private def initial : runtime.messageApplication.PolicyExecution :=
  PolicyExecution.initial _ (State.initial _ runtime.initial)

/-- The driver stops at the second clock call, not at its five-round budget.
Its environment history stops there too. -/
theorem stopping_retains_actual_history :
    (runtime.roundDriver.runRounds [] 0 players wire 5 initial).map (fun execution =>
      (execution.native.application.visible.clock, execution.environmentHistory.length)) =
      FinDist.pure (2, 2) := by
  have hzero : runtime.complete initial.native.application.visible = false := rfl
  have hone : runtime.complete (runtime.tick initial.native.application).visible = false := rfl
  have htwo : runtime.complete
      (runtime.tick (runtime.tick initial.native.application)).visible = true := rfl
  simp only [MessageApplication.RoundDriver.runRounds, MessageApplication.RoundDriver.round,
    List.map_nil, List.replicate_zero, List.nil_append,
    runPolicies, FinDist.pure_bind, environmentPolicyStep, advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step,
    SealedResolution.messageApplication, FinDist.map_pure,
    hzero, hone, htwo, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Running the whole invocation list would retain five clock calls. The
checkpoint projection, rather than the last trace snapshot, is essential. -/
theorem full_trace_keeps_later_clock_calls :
    (runtime.messageApplication.runPolicies players (runtime.roundEnvironment 0 wire)
      (SealedResolution.roundSchedule [] 0 5) initial).map (fun execution =>
        (execution.native.application.visible.clock, execution.environmentHistory.length)) =
      FinDist.pure (5, 5) := by
  simp only [SealedResolution.roundSchedule, SealedResolution.roundInvocations,
    List.map_nil, List.replicate_zero, List.nil_append, List.singleton_append,
    runPolicies, invoke, SealedResolution.roundEnvironment,
    Nat.zero_add, Nat.mod_one, ↓reduceIte, FinDist.pure_bind,
    environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
    MessageApplication.step, SealedResolution.messageApplication, FinDist.map_pure]
  rfl

end InteractionTests.SealedResolutionDriver
