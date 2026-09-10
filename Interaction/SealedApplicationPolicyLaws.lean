/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyLaws
import Interaction.SealedApplication

/-! # Shared policy execution projected to the sealed reference model

The policy runner retains receipts in observations. Erasure is used only to
decode its supported native action trace, without asserting a policy or
observation equivalence with the receipt-free reference state.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- A supported shared policy execution erases to the raw sealed execution of
its recorded native action trace. -/
theorem runPolicies_eraseReceipts_eq_run_trace (program : SealedProgram Principal)
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (state : (program.messageApplication (Value := Value)).State)
    (execution : (program.messageApplication (Value := Value)).PolicyExecution)
    (hmem : execution ∈
      ((program.messageApplication (Value := Value)).runPolicies players environment schedule
        (MessageApplication.PolicyExecution.initial _ state)).support) :
    program.eraseReceipts execution.native =
      program.run (program.eraseReceipts state)
        (execution.nativeTrace.map program.nativeAction) := by
  have hnative := MessageApplication.runPolicies_initial_native_support
    (app := program.messageApplication (Value := Value)) players environment schedule state
      execution hmem
  have herased : program.eraseReceipts execution.native ∈
      (((program.messageApplication (Value := Value)).run execution.nativeTrace state).map
        program.eraseReceipts).support := by
    rw [FinDist.support_map]
    exact ⟨execution.native, hnative, rfl⟩
  rw [program.run_eraseReceipts] at herased
  exact FinDist.mem_support_pure.mp herased

end Interaction.SealedProgram
