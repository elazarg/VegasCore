/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockIsolation
import Vegas.Compile.WindowedBlockResolution
import VegasTests.WindowedApplication

/-! # Block service on a compiler-generated two-owner application

The first owner stays silent. The other owner relays its expiry. The unused
suffix of this block leaves the successor's response window at its original
activation time. The fixture uses the generated windowed application and the
actual policy runner.
-/

noncomputable section

namespace VegasTests.WindowedBlockService

open Vegas Interaction Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.WindowedApplication

abbrev Player := VegasTests.WindowedApplication.Player

def roster : List Player := [1, 0]

def players (who : Player) : runtime.application.PlayerPolicy :=
  if who = 0 then fun _ _ => FinDist.pure .wait
  else runtime.blockPlayer who (fun _ _ => FinDist.pure .wait)

def execution : runtime.application.PolicyExecution :=
  PolicyExecution.initial runtime.application initial

private def playerWait (who : Player) (before : runtime.application.PolicyExecution) :
    runtime.application.PolicyExecution :=
  { before with principalHistory := fun other =>
      if other = who then before.principalHistory who ++
        [⟨State.observe runtime.application before.native who, .wait⟩]
      else before.principalHistory other }

private def polled := playerWait 0 (playerWait 0 (playerWait 1 (playerWait 1 execution)))

private theorem polling_law :
    runtime.application.runPolicies players (runtime.blockEnvironment roster)
      [.player 1, .player 1, .player 0, .player 0] execution = FinDist.pure polled := by
  simp +unfoldPartialApp only [MessageApplication.runPolicies, MessageApplication.invoke,
    MessageApplication.playerStep, MessageApplication.advance, PlayerCommand.toAction]
  repeat' erw [FinDist.pure_bind]
  rfl

private def ticked : runtime.application.PolicyExecution :=
  { polled with
    native := { polled.native with application :=
      { polled.native.application with base := polled.native.application.base.advance 11 } }
    environmentHistory :=
      [⟨State.environmentView runtime.application polled.native, .wait⟩,
       ⟨State.environmentView runtime.application polled.native, .application (.advance 11)⟩]
    nativeTrace := [.environment (.advance 11)] }

private def waited : runtime.application.PolicyExecution :=
  { polled with environmentHistory :=
    [⟨State.environmentView runtime.application polled.native, .wait⟩] }

private theorem tick_law :
    runtime.application.runPolicies players (runtime.blockEnvironment roster)
      [.environment, .environment] polled = FinDist.pure ticked := by
  have hwait : runtime.blockEnvironment roster polled.environmentHistory
      (State.environmentView runtime.application polled.native) = FinDist.pure .wait := rfl
  have hclock : runtime.blockEnvironment roster waited.environmentHistory
      (State.environmentView runtime.application waited.native) =
        FinDist.pure (.application (.advance 11)) := rfl
  have hwaited : runtime.application.environmentPolicyStep polled .wait =
      FinDist.pure waited := runtime.application.environmentStep_wait polled
  simp only [MessageApplication.runPolicies, MessageApplication.invoke,
    hwait, FinDist.pure_bind, hwaited, hclock, FinDist.bind_pure]
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step,
    WindowedApplication.application_advance, FinDist.map_pure, FinDist.pure_bind]
  rfl

/-- The genuine expiry activates the second binding. The remainder of the
first block leaves that binding unexpired and does not advance its clock. -/
theorem silent_owner_preserves_successor_window :
    (runtime.application.runPolicies players (runtime.blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).map
        (fun out => (out.native.application.active,
          out.native.application.base.memory.clock)) =
      FinDist.pure (some ⟨1, 11⟩, 11) := by
  change (runtime.application.runPolicies players (runtime.blockEnvironment roster)
    ([.player 1, .player 1, .player 0, .player 0] ++
      ([.environment, .environment] ++ [.player 1, .environment, .player 0, .environment]))
    execution).map _ = _
  rw [MessageApplication.runPolicies_append, polling_law, FinDist.pure_bind,
    MessageApplication.runPolicies_append, tick_law, FinDist.pure_bind]
  have hsubmit : players 1 (ticked.principalHistory 1)
      (State.observe runtime.application ticked.native 1) =
        FinDist.pure (.submit (.expireBinding 0)) := by
    rfl
  have hinclude : runtime.blockEnvironment roster ticked.environmentHistory
      (State.environmentView runtime.application
        { ticked.native with pool :=
          (ticked.native.pool.submit 1 (.expireBinding 0)).2 }) =
        FinDist.pure (.include (1, 0)) := rfl
  simp +unfoldPartialApp only [
    MessageApplication.runPolicies, MessageApplication.invoke,
    hsubmit, hinclude, FinDist.pure_bind, FinDist.bind_pure,
    MessageApplication.playerStep, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, PlayerCommand.toAction, EnvironmentPolicyCommand.toAction,
    MessageApplication.step]
  repeat' first | erw [FinDist.pure_bind] | erw [FinDist.bind_pure] | erw [FinDist.map_pure]
  rfl

end VegasTests.WindowedBlockService

/-- info: 'VegasTests.WindowedBlockService.silent_owner_preserves_successor_window' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBlockService.silent_owner_preserves_successor_window
