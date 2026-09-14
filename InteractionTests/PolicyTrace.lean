/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationTraceLikelihood
import Interaction.MessageApplicationContinuation
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

/-- Randomizing over commands retains their individual masses even when a
chosen command makes no native state change. -/
theorem wait_probability (law : FinDist lottery.PlayerCommand)
    (environment : lottery.EnvironmentPolicy) :
    (lottery.invoke (fun _ _ _ => law) environment initialExecution (.player 1)).prob afterWait =
      law.prob .wait :=
  lottery.invoke_player_prob_of_step _ environment 1 initialExecution afterWait .wait
    (by rw [player_wait_transition, FinDist.mem_support_pure])

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

/-- The selected wait snapshot has probability one even though the original
runner then performs a genuine random draw. The unseen suffix is integrated,
not counted as an additional factor in the stopped probability. -/
theorem stopped_before_random_draw :
    let release := fun execution : lottery.PolicyExecution =>
      !((execution.principalHistory 1).isEmpty)
    let trace : lottery.PolicyTrace := .step initialExecution (.finish afterWait)
    ((lottery.tracePolicies waitingPlayers drawEnvironment [.player 1, .environment]
      initialExecution).map (PolicyTrace.prefixThrough release)).prob trace = 1 := by
  classical
  intro release trace
  rw [lottery.tracePolicies_prefixThrough_prob_eq_prod]
  have hinvoke : lottery.invoke waitingPlayers drawEnvironment initialExecution (.player 1) =
      FinDist.pure afterWait := by
    simp only [invoke, waitingPlayers, FinDist.pure_bind, player_wait_transition]
  have hstart : release initialExecution = false := rfl
  have hend : release afterWait = true := by decide
  simp only [trace, stoppedPointFactors, hstart, hend, Bool.false_eq_true, ↓reduceIte,
    PolicyTrace.first, FinDist.prob_pure_self, List.prod_cons, List.prod_nil,
    hinvoke, mul_one]

/-- The multiplicative-potential theorem accepts the identically zero
potential; no positivity or cancellation premise is required. -/
theorem stopped_trace_zero_potential
    (release : lottery.PolicyExecution → Bool) (trace : lottery.PolicyTrace)
    (htrace : trace ∈ ((lottery.tracePolicies waitingPlayers drawEnvironment
      [.player 1, .environment] initialExecution).map
        (PolicyTrace.prefixThrough release)).support) :
    0 * ((lottery.tracePolicies waitingPlayers drawEnvironment
      [.player 1, .environment] initialExecution).map
        (PolicyTrace.prefixThrough release)).prob trace = 0 := by
  exact lottery.tracePolicies_prefixThrough_prob_mul
    waitingPlayers waitingPlayers drawEnvironment drawEnvironment release
    (fun _ => 0) initialExecution [.player 1, .environment] trace htrace
    (by intros; simp)

/-- A cutoff immediately before a random application step retains its original
fair outcome law when resumed from the recorded state and histories. -/
theorem resumed_random_draw_is_fair :
    let release := fun execution : lottery.PolicyExecution =>
      !((execution.principalHistory 1).isEmpty)
    (((lottery.tracePolicies waitingPlayers drawEnvironment [.player 1, .environment]
      initialExecution).map (PolicyTrace.prefixThrough release)).bind fun stopped =>
        lottery.runPolicies waitingPlayers drawEnvironment
          ([.player 1, .environment].drop stopped.length) stopped.last).map
            (fun execution => execution.native.application.outcome) = fair.map some := by
  intro release
  rw [← lottery.runPolicies_bind_prefixThrough]
  simp only [runPolicies, invoke, waitingPlayers, drawEnvironment, FinDist.pure_bind,
    player_wait_transition, FinDist.bind_pure]
  have hlast := lottery.environmentStep_native afterWait (.application .draw)
  change (lottery.environmentPolicyStep afterWait (.application .draw)).map
    ((fun state : lottery.State => state.application.outcome) ∘
      MessageInterface.PolicyExecution.native) = _
  rw [← FinDist.map_comp, hlast]
  change (lottery.step s4 (.environment .draw)).map
    (fun state => state.application.outcome) = _
  rw [accepted_draw_law, FinDist.map_comp]
  rfl

end

end InteractionTests.PolicyTrace
