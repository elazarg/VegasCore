/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.WindowedExpiry
import Interaction.MessageApplicationImmediateService
import VegasTests.WindowedApplication

/-! # Permissionless relay on a generated windowed application -/

noncomputable section

namespace VegasTests.WindowedRelay

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability
open VegasTests.ApplicationEarlyBinding
open VegasTests.WindowedApplication

def waitingPolicy : runtime.application.PlayerPolicy := fun _ _ => FinDist.pure .wait

def relayPlayers : Fin 2 → runtime.application.PlayerPolicy := fun who =>
  if who = 1 then runtime.relayWhenWaiting waitingPolicy else waitingPolicy

/-- The first environment turn advances the public clock. Later turns include
the relay principal's latest pending envelope. -/
def relayEnvironment : runtime.application.EnvironmentPolicy := fun history view =>
  match history with
  | [] => FinDist.pure (.application (.advance 100))
  | _ => runtime.application.includeLatestFrom 1 history view

def initialExecution : runtime.application.PolicyExecution :=
  PolicyExecution.initial runtime.application initial

def relaySchedule : List (@Invocation (Fin 2)) :=
  [.environment, .player 1, .environment]

/-- A non-owner observes the overdue active instruction, authors its canonical
expiry envelope, and the ordinary environment inclusion service accepts it.
The author identity and unmodified histories are retained by the shared policy
runner. -/
theorem overdue_other_principal_relay :
    (runtime.application.runPolicies relayPlayers relayEnvironment relaySchedule
      initialExecution).map (fun result =>
        (result.native.application.base.memory.accepted 0,
          result.native.application.base.memory.done 0,
          result.native.application.active,
          result.native.pool.ledger,
          result.native.receipts,
          (result.principalHistory 1).map (·.command),
          result.environmentHistory.length)) =
      FinDist.pure
        (some (.publicDefault ⟨.bool, false⟩), true, some ⟨1, 100⟩,
          [⟨(1, 0), .expireBinding 0⟩], [((1, 0), true)],
          [.submit (.expireBinding 0)], 2) := by
  have hdue : runtime.dueExpiry?
      (runtime.application.observePlayer
        { initial.application with base := initial.application.base.advance 100 } 1) =
      some (.expireBinding 0) := rfl
  have hserial : (initial.pool.submit 1 (.expireBinding 0)).2.nextSerial 1 = 1 := rfl
  have hlookup : (initial.pool.submit 1 (.expireBinding 0)).2.lookup (1, 0) =
      some ⟨(1, 0), .expireBinding 0⟩ := rfl
  simp only [relaySchedule, MessageApplication.runPolicies, MessageApplication.invoke,
    relayPlayers, relayEnvironment, initialExecution, PolicyExecution.initial,
    waitingPolicy, WindowedApplication.relayWhenWaiting,
    WindowedApplication.relayCommand, hdue,
    MessageApplication.playerStep, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, PlayerCommand.toAction, EnvironmentPolicyCommand.toAction,
    MessageApplication.step, MessageApplication.includeLatestFrom,
    MessageApplication.latestSubmissionCommand, State.observe, State.environmentView,
    WindowedApplication.application_advance, FinDist.pure_bind, FinDist.map_pure,
    List.nil_append, hserial, hlookup, Option.isSome_some, ↓reduceIte]
  rfl

/-- Before the strict boundary the same relay wrapper is exactly the supplied
policy on the principal's real empty history and initial public view. -/
theorem early_relay_delegates :
    runtime.relayWhenWaiting waitingPolicy []
      (MessageApplication.State.observe runtime.application initial 1) =
      waitingPolicy [] (MessageApplication.State.observe runtime.application initial 1) := by
  apply runtime.relayWhenWaiting_eq_base_before_window
    waitingPolicy [] _ initialNative.memory ⟨0, 0⟩ rfl
  decide

def overdueApplication : WindowedApplication.State (Fin 2) simpleExpr :=
  { runtime.initial initialNative with base := initialNative.advance 100 }

def overdueExecution : runtime.application.PolicyExecution :=
  PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application overdueApplication)

def ordinaryBindingPolicy : runtime.application.PlayerPolicy := fun _ _ =>
  FinDist.pure (.submit (.binding 0 ((0 : Fin 2), 0)))

/-- The public view is genuinely overdue, but the relay wrapper preserves a
non-wait command sampled by the underlying policy. -/
theorem overdue_nonwait_is_preserved :
    runtime.dueExpiry?
      (MessageApplication.State.observe runtime.application overdueExecution.native 0).application =
        some (.expireBinding 0) ∧
    runtime.relayWhenWaiting ordinaryBindingPolicy
      (overdueExecution.principalHistory 0)
      (MessageApplication.State.observe runtime.application overdueExecution.native 0) =
        ordinaryBindingPolicy (overdueExecution.principalHistory 0)
          (MessageApplication.State.observe runtime.application overdueExecution.native 0) := by
  constructor
  · rfl
  · apply runtime.relayWhenWaiting_eq_of_wait_not_supported
    simp [ordinaryBindingPolicy]

end VegasTests.WindowedRelay

/-- info: 'VegasTests.WindowedRelay.overdue_other_principal_relay' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedRelay.overdue_other_principal_relay

/-- info: 'VegasTests.WindowedRelay.early_relay_delegates' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedRelay.early_relay_delegates

/-- info: 'VegasTests.WindowedRelay.overdue_nonwait_is_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedRelay.overdue_nonwait_is_preserved
