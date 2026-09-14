/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionDeadline

/-! # Concrete sealed-resolution deadline provenance regressions -/

noncomputable section

namespace InteractionTests.SealedResolutionDeadline

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

private def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.commit true, [0]⟩]⟩, none, 2⟩

private def timedOut := runtime.tick (runtime.tick runtime.initial)

/-- A timeout reached by the concrete clocked runtime retains the timestamp
that started its deadline, and that deadline has genuinely elapsed. -/
theorem actual_timeout_has_elapsed_origin :
    timedOut.visible.timeouts = [0] ∧
      ∃ timestamp,
        timedOut.visible.firstReady? 0 = some timestamp ∧
        timestamp + runtime.window ≤ timedOut.visible.clock ∧
        timestamp = 0 ∧
        ∃ rule, runtime.program.rules[0]? = some rule ∧
          rule.requires.all timedOut.visible.completed = true := by
  have hsound0 := SealedResolution.PublicState.DeadlineSound.initial runtime
  have hsound1 := hsound0.tick
  have hsound2 := hsound1.tick
  have htimeout : 0 ∈ timedOut.visible.timeouts := by decide
  obtain ⟨rule, timestamp, hrule, hready, hdeadline, hrequires⟩ :=
    hsound2 0 htimeout
  have hconcrete : timedOut.visible.firstReady? 0 = some 0 := by decide
  have htimestamp : timestamp = 0 :=
    Option.some.inj (hready.symm.trans hconcrete)
  exact ⟨by decide, timestamp, hready, hdeadline, htimestamp,
    rule, hrule, hrequires⟩

private def registered : SealedResolution.ApplicationState Bool (Option Bool) :=
  { runtime.initial with
    service := (runtime.initial.service.sealValue false 0 (some true)).state }

private def preparedState : runtime.messageApplication.State :=
  let initial := State.initial runtime.messageApplication registered
  { initial with
    pool := (initial.pool.submit false (.commitment 0 (false, 0))).2 }

private def before : runtime.messageApplication.PolicyExecution :=
  PolicyExecution.initial runtime.messageApplication preparedState

private def players : Bool → runtime.messageApplication.PlayerPolicy :=
  fun _ _ _ => FinDist.pure .wait

private def environment : runtime.messageApplication.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.include (false, 0))

private def included : runtime.messageApplication.PolicyExecution :=
  { before with
    native := runtime.messageApplication.includePending before.native (false, 0)
    environmentHistory := before.environmentHistory ++
      [⟨State.environmentView runtime.messageApplication before.native,
        .include (false, 0)⟩]
    nativeTrace := before.nativeTrace ++ [.include (false, 0)] }

private theorem invoke_includes :
    runtime.messageApplication.invoke players environment before .environment =
      FinDist.pure included := by
  simp [MessageApplication.invoke, environment, environmentPolicyStep, advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, included]

/-- Inclusion of the first commitment is an actual policy invocation.  Its
refresh newly stamps the dependent rule at exactly the resulting clock. -/
theorem actual_invoke_stamps_newly_ready_rule :
    ∃ after,
      after ∈ (runtime.messageApplication.invoke players environment before
        .environment).support ∧
      after.native.application.visible.firstReady? 1 =
        some after.native.application.visible.clock ∧
      ∃ rule, runtime.program.rules[1]? = some rule ∧
        rule.requires.all after.native.application.visible.completed = true := by
  have hsupported : included ∈
      (runtime.messageApplication.invoke players environment before .environment).support := by
    rw [invoke_includes]
    exact FinDist.mem_support_pure.mpr rfl
  have hsound : before.native.application.visible.ReadySound runtime := by
    change runtime.initial.visible.ReadySound runtime
    exact SealedResolution.PublicState.ReadySound.initial runtime
  have hnone : before.native.application.visible.firstReady? 1 = none := by decide
  have hready : included.native.application.visible.firstReady? 1 = some 0 := by decide
  have horigin := runtime.invoke_firstReady?_of_none players environment before included
    .environment 1 0 hsound hsupported hnone hready
  refine ⟨included, hsupported, ?_, horigin.2⟩
  rwa [horigin.1] at hready

end InteractionTests.SealedResolutionDeadline
