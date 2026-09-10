/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedApplication
import Interaction.MessageApplicationPolicies

/-! # Executable regressions for the shared sealed-message application -/

namespace InteractionTests.SealedApplication

open Interaction Interaction.SealedProgram Interaction.MessageApplication
open GameTheory.Math.Probability

noncomputable section

def program : SealedProgram Bool := ⟨[]⟩

abbrev Application := program.messageApplication (Value := Bool)

def initialApplication : Application.Application := ⟨IdealCommitments.empty, []⟩

def initial : Application.State :=
  MessageApplication.State.initial Application initialApplication

def initialExecution : Application.PolicyExecution :=
  MessageApplication.PolicyExecution.initial Application initial

def registerCommand : Application.PlayerCommand := .privateCommand ⟨(3, true)⟩

def afterRegister : Application.PolicyExecution :=
  { initialExecution with
    native := { initialExecution.native with
      application := Application.privateStep initialExecution.native.application false
        ⟨(3, true)⟩ }
    principalHistory := fun other =>
      if other = false then
        initialExecution.principalHistory false ++
          [⟨MessageApplication.State.observe Application initialExecution.native false,
            registerCommand⟩]
      else initialExecution.principalHistory other
    nativeTrace := initialExecution.nativeTrace ++ [.privateCommand false ⟨(3, true)⟩] }

/-- Private registration is attributed to the invoked principal and retained
in both the shared policy history and native action trace. -/
theorem register_transition :
    Application.playerStep false initialExecution registerCommand =
      FinDist.pure afterRegister := by
  simp [MessageApplication.playerStep, MessageApplication.advance, registerCommand,
    afterRegister, initialExecution, Application, program, SealedProgram.messageApplication,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step]

theorem register_principal_attribution :
    afterRegister.native.application.service.lookup (false, 3) = some true ∧
      (afterRegister.principalHistory false).length = 1 ∧
      afterRegister.nativeTrace = [.privateCommand false ⟨(3, true)⟩] := by
  exact ⟨rfl, rfl, rfl⟩

def submitCommand : Application.PlayerCommand := .submit .malformed

def afterSubmit : Application.PolicyExecution :=
  { initialExecution with
    native := { initialExecution.native with
      pool := (initialExecution.native.pool.submit false .malformed).2 }
    principalHistory := fun other =>
      if other = false then
        initialExecution.principalHistory false ++
          [⟨MessageApplication.State.observe Application initialExecution.native false,
            submitCommand⟩]
      else initialExecution.principalHistory other
    nativeTrace := initialExecution.nativeTrace ++ [.submit false .malformed] }

theorem submit_transition :
    Application.playerStep false initialExecution submitCommand =
      FinDist.pure afterSubmit := by
  simp [MessageApplication.playerStep, MessageApplication.advance, submitCommand,
    afterSubmit, initialExecution, Application, program, SealedProgram.messageApplication,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step]

theorem submit_principal_attribution :
    afterSubmit.native.pool.pending.head?.map Message.sender = some false ∧
      afterSubmit.nativeTrace = [.submit false .malformed] := by
  exact ⟨rfl, rfl⟩

def unknownReplayCommand : Application.PlayerCommand := .replay (false, 0)

def afterUnknownReplay : Application.PolicyExecution :=
  { afterSubmit with
    native := { afterSubmit.native with
      pool := (afterSubmit.native.pool.replay true (false, 0)).state }
    principalHistory := fun who =>
      if who = true then
        afterSubmit.principalHistory true ++
          [⟨MessageApplication.State.observe Application afterSubmit.native true,
            unknownReplayCommand⟩]
      else afterSubmit.principalHistory who
    nativeTrace := afterSubmit.nativeTrace ++ [.replay true (false, 0)] }

/-- A principal cannot replay an envelope before observing it. The attempted
action is still recorded as policy history and in the native trace. -/
theorem unknown_replay_transition :
    Application.playerStep true afterSubmit unknownReplayCommand =
      FinDist.pure afterUnknownReplay := by
  simp [MessageApplication.playerStep, MessageApplication.advance, unknownReplayCommand,
    afterUnknownReplay, Application, program, SealedProgram.messageApplication,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step]

theorem unknown_replay_stutters_pool :
    afterUnknownReplay.native.pool = afterSubmit.native.pool ∧
      (afterUnknownReplay.principalHistory true).length = 1 ∧
      afterUnknownReplay.nativeTrace.getLast? = some (.replay true (false, 0)) := by
  exact ⟨rfl, rfl, rfl⟩

def deliveryCommand : Application.EnvironmentPolicyCommand :=
  .deliver true (false, 0)

def afterDelivery : Application.PolicyExecution :=
  { afterSubmit with
    native := { afterSubmit.native with
      pool := (afterSubmit.native.pool.deliver true (false, 0)).state }
    environmentHistory := afterSubmit.environmentHistory ++
      [⟨MessageApplication.State.environmentView Application afterSubmit.native,
        deliveryCommand⟩]
    nativeTrace := afterSubmit.nativeTrace ++ [.deliver true (false, 0)] }

theorem delivery_transition :
    Application.environmentPolicyStep afterSubmit deliveryCommand =
      FinDist.pure afterDelivery := by
  simp [MessageApplication.environmentPolicyStep, MessageApplication.advance, deliveryCommand,
    afterDelivery, Application, program, SealedProgram.messageApplication,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step]

theorem delivery_preserves_player_histories :
    afterDelivery.principalHistory = afterSubmit.principalHistory ∧
      (MessageApplication.State.observe Application afterSubmit.native true).messages.inbox = [] ∧
      ((MessageApplication.State.observe Application
        afterDelivery.native true).messages.inbox.head?.map Message.sender) = some false := by
  exact ⟨rfl, rfl, rfl⟩

def replayCommand : Application.PlayerCommand := .replay (false, 0)

def afterReplay : Application.PolicyExecution :=
  { afterDelivery with
    native := { afterDelivery.native with
      pool := (afterDelivery.native.pool.replay true (false, 0)).state }
    principalHistory := fun who =>
      if who = true then
        afterDelivery.principalHistory true ++
          [⟨MessageApplication.State.observe Application afterDelivery.native true,
            replayCommand⟩]
      else afterDelivery.principalHistory who
    nativeTrace := afterDelivery.nativeTrace ++ [.replay true (false, 0)] }

/-- Once observed, replay succeeds while retaining the original message
author, even though another principal invoked the replay. -/
theorem observed_replay_transition :
    Application.playerStep true afterDelivery replayCommand =
      FinDist.pure afterReplay := by
  simp [MessageApplication.playerStep, MessageApplication.advance, replayCommand,
    afterReplay, Application, program, SealedProgram.messageApplication,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step]

theorem observed_replay_preserves_author :
    afterReplay.native.pool.pending.length = 2 ∧
      (afterReplay.native.pool.sent true).length = 1 ∧
      afterReplay.native.pool.pending.getLast?.map Message.sender = some false ∧
      afterReplay.nativeTrace.getLast? = some (.replay true (false, 0)) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def afterWait : Application.PolicyExecution :=
  { initialExecution with
    principalHistory := fun other =>
      if other = false then
        initialExecution.principalHistory false ++
          [⟨MessageApplication.State.observe Application initialExecution.native false, .wait⟩]
      else initialExecution.principalHistory other }

theorem wait_transition :
    Application.playerStep false initialExecution .wait = FinDist.pure afterWait := by
  simp [MessageApplication.playerStep, MessageApplication.advance, afterWait,
    initialExecution, Application, program, SealedProgram.messageApplication,
    MessageApplication.PlayerCommand.toAction]

/-- Waiting stutters natively while recording the sampled view and command. -/
theorem wait_stutters_native_and_records_history :
    afterWait.native = initial ∧ afterWait.nativeTrace = [] ∧
      (afterWait.principalHistory false).length = 1 ∧
      (afterWait.principalHistory true).length = 0 ∧
      (afterWait.principalHistory false).head?.map MessageInterface.PlayerEntry.command =
        some MessageInterface.PlayerCommand.wait := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end InteractionTests.SealedApplication
