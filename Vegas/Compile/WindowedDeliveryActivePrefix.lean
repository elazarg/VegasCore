/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryProgress
import Vegas.Compile.WindowedDeliveryIsolation

/-! # Active prefixes of the delivery service -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr} {G : Graph P L}

/-- If a delivery-service suffix ends with its original owned instruction
active, every preceding invocation remained in the active branch. The suffix
therefore preserves source refinement and activation origin, and only advances
the public clock monotonically. -/
theorem runPolicies_delivery_refines_of_final_active
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation P))
    (execution final : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (owner : P) (cfg : Config G)
    (howner : instruction.submitter = some owner)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index /
        (recipients.length + roster.length + 2)]? = some instruction)
    (hrefines : execution.native.application.base.Refines cfg)
    (hactive : runtime.image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hfinalActive : runtime.image.activeAddress?
      final.native.application.base.memory = some instruction.address)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients) schedule execution).support) :
    final.native.application.base.Refines cfg ∧
      final.native.application.active = execution.native.application.active ∧
      execution.native.application.base.memory.clock ≤
        final.native.application.base.memory.clock := by
  induction schedule generalizing execution final with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hfinal
      subst final
      exact ⟨hrefines, rfl, Nat.le_refl _⟩
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind,
        Set.mem_iUnion] at hfinal
      obtain ⟨middle, hmiddle, hrest⟩ := hfinal
      have hlength := runtime.application.runPolicies_environmentHistory_length players
        (runtime.deliveryBlockEnvironment roster recipients) [invocation] execution middle (by
          simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hmiddle)
      have hmiddleActive : runtime.image.activeAddress?
          middle.native.application.base.memory = some instruction.address := by
        by_contra hinactive
        have hstutter := runtime.runPolicies_deliveryBlock_inactive roster recipients players rest
          middle final instruction (by
            intro index hlo hhi
            apply hindex index
            · omega
            · simp only [List.countP_cons, List.countP_nil] at hlength ⊢
              omega) hinactive hrest
        have hmemory : final.native.application.base.memory =
            middle.native.application.base.memory := congrArg Prod.fst hstutter
        rw [hmemory] at hfinalActive
        exact hinactive hfinalActive
      have hstep : middle.native.application.base.Refines cfg ∧
          middle.native.application.active = execution.native.application.active ∧
          execution.native.application.base.memory.clock ≤
            middle.native.application.base.memory.clock := by
        cases invocation with
        | player who =>
            simp only [MessageApplication.invoke, FinDist.support_bind,
              Set.mem_iUnion] at hmiddle
            obtain ⟨command, _, hcommand⟩ := hmiddle
            obtain ⟨hr, ha, hc⟩ :=
              runtime.playerStep_refines who execution middle command cfg hrefines hcommand
            exact ⟨hr, ha, Nat.le_of_eq hc.symm⟩
        | environment =>
            apply runtime.invoke_delivery_refines_of_active roster recipients players execution
              middle .environment instruction owner cfg
            · apply hindex execution.environmentHistory.length
              · exact Nat.le_refl _
              · simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte]
                omega
            · exact howner
            · exact hrefines
            · exact hactive
            · exact hmiddleActive
            · exact hmiddle
      obtain ⟨hrestRefines, hrestActivation, hrestClock⟩ :=
        ih middle final (by
          intro index hlo hhi
          apply hindex index
          · omega
          · simp only [List.countP_cons, List.countP_nil] at hlength ⊢
            omega) hstep.1 hmiddleActive hfinalActive hrest
      exact ⟨hrestRefines, hrestActivation.trans hstep.2.1,
        Nat.le_trans hstep.2.2 hrestClock⟩

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_delivery_refines_of_final_active'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_delivery_refines_of_final_active
