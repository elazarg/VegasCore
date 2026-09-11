/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockProvenance
import Vegas.Compile.WindowedDeliveryService

/-! # Source-command provenance for delivery-gated players -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Erasing a command supported by the delivery-gated wrapper yields either a
command of the underlying source policy at the actual erased input or a genuine
wait/expiry command. Delivery reaction slots are waits for reference players. -/
theorem deliveryBlockPlayer_supported (runtime : WindowedApplication P L) (who : P)
    (base : runtime.image.orderedApplication.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (command : runtime.application.PlayerCommand)
    (hcommand : command ∈
      (runtime.deliveryBlockPlayer who (runtime.liftPlayerPolicy base) history view).support) :
    runtime.erasePlayerCommand command ∈
        (base (history.map runtime.erasePlayerEntry) (runtime.eraseView view)).support ∨
      runtime.image.IdleOrExpiryCommand (runtime.erasePlayerCommand command) := by
  unfold deliveryBlockPlayer at hcommand
  cases hindex : runtime.image.instructions[history.length / 4]? with
  | none =>
      simp only [hindex, FinDist.mem_support_pure] at hcommand
      subst command
      exact Or.inr runtime.image.idleOrExpiryCommand_wait
  | some instruction =>
      by_cases hactive :
          runtime.image.activeAddress? view.application.1 = some instruction.address
      · by_cases hzero : history.length % 4 = 0
        · simp only [hindex, hactive, if_pos, hzero] at hcommand
          split at hcommand
          · unfold liftPlayerPolicy at hcommand
            rw [FinDist.support_map] at hcommand
            obtain ⟨baseCommand, hbase, rfl⟩ := hcommand
            exact Or.inl (by simpa using hbase)
          · simp only [FinDist.mem_support_pure] at hcommand
            subst command
            exact Or.inr runtime.image.idleOrExpiryCommand_wait
        · by_cases hone : history.length % 4 = 1
          · simp only [hindex, hactive, if_pos, hone] at hcommand
            split at hcommand
            · unfold liftPlayerPolicy at hcommand
              rw [FinDist.support_map] at hcommand
              obtain ⟨baseCommand, hbase, rfl⟩ := hcommand
              exact Or.inl (by simpa using hbase)
            · simp only [FinDist.mem_support_pure] at hcommand
              subst command
              exact Or.inr runtime.image.idleOrExpiryCommand_wait
          · by_cases htwo : history.length % 4 = 2
            · simp only [hindex, hactive, if_pos, htwo,
                FinDist.mem_support_pure] at hcommand
              subst command
              exact Or.inr runtime.image.idleOrExpiryCommand_wait
            · have hthree : history.length % 4 = 3 := by omega
              simp only [hindex, hactive, if_pos, hthree,
                FinDist.mem_support_pure] at hcommand
              subst command
              cases hdue : runtime.dueExpiry? view.application with
              | none => exact Or.inr runtime.image.idleOrExpiryCommand_wait
              | some payload =>
                  exact Or.inr (runtime.image.idleOrExpiryCommand_submit payload
                    (runtime.dueExpiry?_deadlineDependent view.application payload hdue))
      · simp only [hindex, hactive, if_false,
          FinDist.mem_support_pure] at hcommand
        subst command
        exact Or.inr runtime.image.idleOrExpiryCommand_wait

end Vegas.WindowedApplication
