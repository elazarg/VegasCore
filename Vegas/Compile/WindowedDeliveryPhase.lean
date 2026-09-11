/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryService
import Interaction.MessageApplicationEnvironmentCommands

/-! # The fixed delivery prefix -/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem environmentPolicyStep_deliver_native
    (runtime : WindowedApplication P L) (execution next : runtime.application.PolicyExecution)
    (recipient : P) (id : MessageId P)
    (hnext : next ∈ (runtime.application.environmentPolicyStep execution
      (.deliver recipient id)).support) :
    next.native = { execution.native with
      pool := (execution.native.pool.deliver recipient id).state } := by
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure] at hnext
  subst next
  rfl

private theorem deliveryPrefixFrom
    (runtime : WindowedApplication P L) (players : P → runtime.application.PlayerPolicy)
    (roster all before rest : List P) (blockIndex : Nat)
    (instruction : ApplicationInstruction P L) (id : MessageId P)
    (hall : all = before ++ rest)
    (execution : runtime.application.PolicyExecution)
    (hlength : execution.environmentHistory.length =
      blockIndex * (all.length + roster.length + 2) + before.length)
    (hindex : runtime.image.instructions[blockIndex]? = some instruction)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hinclude : runtime.liftEnvironmentCommand
      (runtime.image.serviceCommand instruction
        (runtime.eraseEnvironmentView
          (State.environmentView runtime.application execution.native))) = .include id) :
    runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster all)
        (rest.map fun _ => (Invocation.environment : @Invocation P)) execution =
      runtime.application.runEnvironmentCommands
        (rest.map fun recipient =>
          (MessageInterface.EnvironmentPolicyCommand.deliver recipient id)) execution := by
  induction rest generalizing before execution with
  | nil => rfl
  | cons recipient rest ih =>
      have hwidth : 0 < all.length + roster.length + 2 := by omega
      have hbefore : before.length < all.length := by
        rw [hall, List.length_append, List.length_cons]
        omega
      have hdivision : execution.environmentHistory.length /
          (all.length + roster.length + 2) = blockIndex := by
        rw [hlength, Nat.mul_comm blockIndex, Nat.mul_add_div hwidth,
          Nat.div_eq_of_lt (by omega), Nat.add_zero]
      have hslot : execution.environmentHistory.length %
          (all.length + roster.length + 2) = before.length := by
        rw [hlength, Nat.mul_comm blockIndex, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have hrecipient : all[before.length]? = some recipient := by
        rw [hall]
        simp
      have hpolicy := runtime.deliveryBlockEnvironment_delivery_include roster all
        execution.environmentHistory (State.environmentView runtime.application execution.native)
        instruction before.length recipient id (by rwa [hdivision]) hactive hslot hbefore
        hrecipient hinclude
      simp only [List.map_cons, MessageApplication.runPolicies, MessageApplication.invoke,
        hpolicy, FinDist.pure_bind, MessageApplication.runEnvironmentCommands]
      apply FinDist.bind_congr
      intro next hnext
      have hnative := runtime.environmentPolicyStep_deliver_native execution next recipient id hnext
      apply ih (before ++ [recipient])
        (by simpa only [List.append_assoc, List.singleton_append] using hall) next
      · rw [runtime.application.environmentStep_history_length execution
          (.deliver recipient id) next hnext, hlength, List.length_append]
        simp [Nat.add_assoc]
      · simpa only [hnative] using hactive
      · have hpending : (execution.native.pool.deliver recipient id).state.pending =
            execution.native.pool.pending := by
          unfold MessagePool.deliver
          split <;> rfl
        have hserial : (execution.native.pool.deliver recipient id).state.nextSerial =
            execution.native.pool.nextSerial := by
          unfold MessagePool.deliver
          split <;> rfl
        cases instruction <;>
          simpa only [hnative, WindowedApplication.eraseEnvironmentView,
            State.environmentView, ApplicationImage.serviceCommand,
            MessageApplication.latestSubmissionCommand, MessagePool.lookup,
            hpending, hserial] using hinclude

/-- The actual delivery prefix executes the fixed selected identifier once for
each recipient, including repeated recipients. -/
theorem runPolicies_deliveryPrefix
    (runtime : WindowedApplication P L) (players : P → runtime.application.PlayerPolicy)
    (roster recipients : List P) (blockIndex : Nat)
    (instruction : ApplicationInstruction P L) (id : MessageId P)
    (execution : runtime.application.PolicyExecution)
    (hlength : execution.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2))
    (hindex : runtime.image.instructions[blockIndex]? = some instruction)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hinclude : runtime.liftEnvironmentCommand
      (runtime.image.serviceCommand instruction
        (runtime.eraseEnvironmentView
          (State.environmentView runtime.application execution.native))) = .include id) :
    runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients)
        (recipients.map fun _ => (Invocation.environment : @Invocation P)) execution =
      runtime.application.runEnvironmentCommands
        (recipients.map fun recipient =>
          (MessageInterface.EnvironmentPolicyCommand.deliver recipient id)) execution := by
  exact runtime.deliveryPrefixFrom players roster recipients [] recipients blockIndex instruction
    id (by simp) execution (by simpa using hlength) hindex hactive hinclude

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_deliveryPrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_deliveryPrefix
