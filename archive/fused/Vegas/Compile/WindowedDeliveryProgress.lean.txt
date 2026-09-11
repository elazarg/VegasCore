/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryIsolation
import Vegas.Compile.WindowedBlockProgress

/-! # Active source checkpoints under delivery-enabled service -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- No coordinate of a player-controlled delivery block executes source
chance. Delivery and raw reaction slots remain part of the actual schedule. -/
theorem deliveryBlockEnvironment_command_not_sample
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (owner : P)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (howner : instruction.submitter = some owner)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hcommand : command ∈ (runtime.deliveryBlockEnvironment roster recipients
      execution.environmentHistory
      (State.environmentView runtime.application execution.native)).support) :
    ∀ address, command ≠ .application (.sample address) := by
  let slot := execution.environmentHistory.length % (recipients.length + roster.length + 2)
  by_cases hdelivery : slot < recipients.length
  · have hrecipient : recipients[slot]? = some recipients[slot] := by simp [hdelivery]
    obtain rfl | ⟨id, rfl⟩ := runtime.deliveryBlockEnvironment_recipient_only roster recipients
      execution.environmentHistory (State.environmentView runtime.application execution.native)
      instruction slot recipients[slot] command hindex rfl hdelivery hrecipient hcommand
    · simp
    · simp
  · simp only [deliveryBlockEnvironment, hindex, FinDist.mem_support_pure] at hcommand
    subst command
    intro address
    split
    · split
      · exact runtime.serviceCommand_not_sample instruction owner howner _ address
      · split
        · split
          · simp
          · split <;> simp
        · split
          · simp
          · exact runtime.latestSubmissionCommand_not_sample _ _ address
    · simp

/-- A supported invocation that leaves the original instruction active
preserves its source refinement and activation origin; its clock is monotone. -/
theorem invoke_delivery_refines_of_active
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy)
    (execution next : runtime.application.PolicyExecution)
    (invocation : @Invocation P) (instruction : ApplicationInstruction P L)
    (owner : P) {G : Graph P L} (cfg : Config G)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (howner : instruction.submitter = some owner)
    (hrefines : execution.native.application.base.Refines cfg)
    (hbefore : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hafter : runtime.image.activeAddress? next.native.application.base.memory =
      some instruction.address)
    (hnext : next ∈ (runtime.application.invoke players
      (runtime.deliveryBlockEnvironment roster recipients) execution invocation).support) :
    next.native.application.base.Refines cfg ∧
      next.native.application.active = execution.native.application.active ∧
      execution.native.application.base.memory.clock ≤
        next.native.application.base.memory.clock := by
  cases invocation with
  | player who =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, _, hstep⟩ := hnext
      obtain ⟨hrefines, hactivation, hclock⟩ :=
        runtime.playerStep_refines who execution next command cfg hrefines hstep
      exact ⟨hrefines, hactivation, Nat.le_of_eq hclock.symm⟩
  | environment =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, hcommand, hstep⟩ := hnext
      exact runtime.environmentPolicyStep_refines_of_active execution next command
        instruction.address cfg hrefines hbefore hafter
        (runtime.deliveryBlockEnvironment_command_not_sample roster recipients execution
          instruction owner hindex howner command hcommand) hstep

end Vegas.WindowedApplication
