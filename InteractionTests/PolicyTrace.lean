/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyTrace
import InteractionTests.MessageApplication

/-! # Policy trace regressions for stochastic applications -/

namespace InteractionTests.PolicyTrace

open Interaction Interaction.MessageApplication GameTheory.Math.Probability
open InteractionTests.MessageApplication

noncomputable section

def waitingPlayers : Principal → lottery.PlayerPolicy :=
  fun _ _ _ => FinDist.pure .wait

def drawEnvironment : lottery.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.application .draw)

def passiveEnvironment : lottery.EnvironmentPolicy :=
  fun _ _ => FinDist.pure .wait

def initialExecution : lottery.PolicyExecution :=
  MessageApplication.PolicyExecution.initial lottery s4

/-- Trace instrumentation retains the lottery's fair native draw law. -/
theorem final_native_draw_is_fair (players : Principal → lottery.PlayerPolicy) :
    ((lottery.tracePolicies players drawEnvironment [.environment] initialExecution).map
      (fun trace =>
        InteractionTests.MessageApplication.Application.outcome
          trace.last.native.application)) = fair.map some := by
  change (lottery.tracePolicies players drawEnvironment [.environment] initialExecution).map
      ((fun execution : lottery.PolicyExecution => execution.native.application.outcome) ∘
        PolicyTrace.last) = fair.map some
  rw [← FinDist.map_comp, lottery.tracePolicies_last]
  unfold drawEnvironment
  exact policy_draw_law players

def afterWait : lottery.PolicyExecution :=
  { initialExecution with
    principalHistory := fun other =>
      if other = 1 then
        initialExecution.principalHistory 1 ++
          [⟨MessageApplication.State.observe lottery initialExecution.native 1, .wait⟩]
      else initialExecution.principalHistory other }

theorem player_wait_transition :
    lottery.playerStep 1 initialExecution .wait = FinDist.pure afterWait := by
  simpa [afterWait] using lottery.playerStep_wait 1 initialExecution

/-- A wait produces a trace containing both the pre-invocation and final
snapshots, records one player-history entry, and adds no native action. -/
theorem wait_records_snapshots :
    lottery.tracePolicies waitingPlayers passiveEnvironment [.player 1] initialExecution =
      FinDist.pure (.step initialExecution (.finish afterWait)) ∧
    afterWait.native = initialExecution.native ∧
    (afterWait.principalHistory 1).length = 1 ∧
    afterWait.nativeTrace = [] := by
  constructor
  · simp [MessageApplication.tracePolicies, MessageApplication.invoke, waitingPlayers,
      player_wait_transition]
  · exact ⟨rfl, rfl, rfl⟩

end

end InteractionTests.PolicyTrace
