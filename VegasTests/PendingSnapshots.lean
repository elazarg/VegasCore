/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.PendingPolicies

/-! # Expected policy snapshots for pending-message regressions

Fixtures describe expected states, with their transition laws proved against
the canonical shared steps and invocations. They are not an alternative runner.
-/

namespace VegasTests.PendingSnapshots

open Interaction Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingPolicies

noncomputable section

/-- Expected snapshots, checked below against the canonical invocations. -/
def playerSnapshot (who : Player) (execution : Application.PolicyExecution)
    (command : Application.PlayerCommand) (native : Application.State) :
    Application.PolicyExecution :=
  { execution with
    native
    principalHistory := fun other =>
      if other = who then execution.principalHistory who ++
        [⟨MessageApplication.State.observe Application execution.native who, command⟩]
      else execution.principalHistory other
    nativeTrace := execution.nativeTrace ++ (command.toAction Application who).toList }

def environmentSnapshot (execution : Application.PolicyExecution)
    (command : Application.EnvironmentPolicyCommand) (native : Application.State) :
    Application.PolicyExecution :=
  { execution with
    native
    environmentHistory := execution.environmentHistory ++
      [⟨MessageApplication.State.environmentView Application execution.native, command⟩]
    nativeTrace := execution.nativeTrace ++ command.toAction.toList }

theorem playerStep_snapshot (who : Player) (execution : Application.PolicyExecution)
    (command : Application.PlayerCommand) (native : Application.State)
    (hnative : (match command.toAction Application who with
      | none => FinDist.pure execution.native
      | some action => Application.step execution.native action) = FinDist.pure native) :
    Application.playerStep who execution command =
      FinDist.pure (playerSnapshot who execution command native) := by
  cases ha : command.toAction Application who with
  | none =>
      simp only [ha] at hnative
      have heq : execution.native = native := by
        apply FinDist.mem_support_pure.mp
        rw [← hnative]
        exact FinDist.mem_support_pure.mpr rfl
      subst native
      simp [MessageApplication.playerStep, MessageApplication.advance, playerSnapshot, ha]
  | some action =>
      simp only [ha] at hnative
      simp [MessageApplication.playerStep, MessageApplication.advance, playerSnapshot, ha, hnative]

theorem environmentStep_snapshot (execution : Application.PolicyExecution)
    (command : Application.EnvironmentPolicyCommand) (native : Application.State)
    (hnative : (match command.toAction with
      | none => FinDist.pure execution.native
      | some action => Application.step execution.native action) = FinDist.pure native) :
    Application.environmentPolicyStep execution command =
      FinDist.pure (environmentSnapshot execution command native) := by
  cases ha : command.toAction with
  | none =>
      simp only [ha] at hnative
      have heq : execution.native = native := by
        apply FinDist.mem_support_pure.mp
        rw [← hnative]
        exact FinDist.mem_support_pure.mpr rfl
      subst native
      simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        environmentSnapshot, ha]
  | some action =>
      simp only [ha] at hnative
      simp [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        environmentSnapshot, ha, hnative]

theorem invokePlayer_snapshot (players : Player → Application.PlayerPolicy)
    (environment : Application.EnvironmentPolicy) (execution : Application.PolicyExecution)
    (who : Player) (command : Application.PlayerCommand) (native : Application.State)
    (hpolicy : players who (execution.principalHistory who)
      (MessageApplication.State.observe Application execution.native who) = FinDist.pure command)
    (hnative : (match command.toAction Application who with
      | none => FinDist.pure execution.native
      | some action => Application.step execution.native action) = FinDist.pure native) :
    Application.invoke players environment execution (.player who) =
      FinDist.pure (playerSnapshot who execution command native) := by
  simp only [MessageApplication.invoke, hpolicy, FinDist.pure_bind]
  exact playerStep_snapshot who execution command native hnative

theorem invokeEnvironment_snapshot (players : Player → Application.PlayerPolicy)
    (environment : Application.EnvironmentPolicy) (execution : Application.PolicyExecution)
    (command : Application.EnvironmentPolicyCommand) (native : Application.State)
    (hpolicy : environment execution.environmentHistory
      (MessageApplication.State.environmentView Application execution.native) =
        FinDist.pure command)
    (hnative : (match command.toAction with
      | none => FinDist.pure execution.native
      | some action => Application.step execution.native action) = FinDist.pure native) :
    Application.invoke players environment execution .environment =
      FinDist.pure (environmentSnapshot execution command native) := by
  simp only [MessageApplication.invoke, hpolicy, FinDist.pure_bind]
  exact environmentStep_snapshot execution command native hnative

end

end VegasTests.PendingSnapshots
