/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationIdleService
import Vegas.Compile.WindowedDeliveryService
import Vegas.Compile.ApplicationImageStateRefinement

/-! # Isolation of resolved delivery-service blocks -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An inactive addressed instruction makes every coordinate of the delivery
environment idle. -/
theorem deliveryBlockEnvironment_inactive
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[history.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hinactive : runtime.image.activeAddress? view.application.1 ≠
      some instruction.address) :
    runtime.deliveryBlockEnvironment roster recipients history view = FinDist.pure .wait := by
  simp only [deliveryBlockEnvironment, hindex, hinactive, ↓reduceIte]

/-- Once the addressed instruction is inactive, the delivery environment is
idle throughout an aligned suffix. Arbitrary raw player commands remain in the
runner and may still modify pools, histories, and private preparation. -/
theorem runPolicies_deliveryBlock_inactive_invariant
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index /
        (recipients.length + roster.length + 2)]? = some instruction)
    (Invariant : WindowedApplication.State P L → Prop)
    (hprivate : ∀ state actor command, Invariant state →
      Invariant (runtime.application.privateStep state actor command))
    (hinactive : ∀ state, Invariant state →
      runtime.image.activeAddress? state.base.memory ≠ some instruction.address)
    (hinvariant : Invariant execution.native.application)
    (hnext : next ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients) schedule execution).support) :
    Invariant next.native.application := by
  apply runtime.application.runPolicies_idleEnvironment_invariant players
    (runtime.deliveryBlockEnvironment roster recipients) schedule execution next
    Invariant hprivate ?_ hinvariant hnext
  intro current hcurrent hlo hhi
  have hcurrentIndex := hindex current.environmentHistory.length hlo hhi
  have hcurrentInactive := hinactive current.native.application hcurrent
  apply runtime.deliveryBlockEnvironment_inactive roster recipients _ _ instruction
    hcurrentIndex
  simpa [State.environmentView, WindowedApplication.application] using hcurrentInactive

/-- An aligned inactive delivery suffix preserves public application memory
and activation, despite unrestricted raw player traffic. -/
theorem runPolicies_deliveryBlock_inactive
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index /
        (recipients.length + roster.length + 2)]? = some instruction)
    (hinactive : runtime.image.activeAddress? execution.native.application.base.memory ≠
      some instruction.address)
    (hnext : next ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients) schedule execution).support) :
    (next.native.application.base.memory, next.native.application.active) =
      (execution.native.application.base.memory, execution.native.application.active) := by
  apply runtime.runPolicies_deliveryBlock_inactive_invariant roster recipients players schedule
    execution next instruction hindex
    (fun state => (state.base.memory, state.active) =
      (execution.native.application.base.memory, execution.native.application.active))
  · intro state actor command hstate
    cases command with
    | register slot value => exact hstate
  · intro state hstate
    have hmemory : state.base.memory = execution.native.application.base.memory :=
      congrArg Prod.fst hstate
    rwa [hmemory]
  · rfl
  · exact hnext

/-- An aligned inactive delivery suffix preserves source refinement; private
registration may evolve, while accepted source values remain fixed. -/
theorem runPolicies_deliveryBlock_inactive_refines
    (runtime : WindowedApplication P L) {G : Graph P L} (cfg : Config G)
    (roster recipients : List P) (players : P → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index /
        (recipients.length + roster.length + 2)]? = some instruction)
    (hinactive : runtime.image.activeAddress? execution.native.application.base.memory ≠
      some instruction.address)
    (hrefines : execution.native.application.base.Refines cfg)
    (hnext : next ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients) schedule execution).support) :
    next.native.application.base.Refines cfg := by
  have hresult := runtime.runPolicies_deliveryBlock_inactive_invariant roster recipients players
    schedule execution next instruction hindex
    (fun state => state.base.Refines cfg ∧
      runtime.image.activeAddress? state.base.memory ≠ some instruction.address)
    (by
      intro state actor command hstate
      cases command with
      | register slot value => exact ⟨hstate.1.register actor slot value, hstate.2⟩)
    (fun _ hstate => hstate.2) ⟨hrefines, hinactive⟩ hnext
  exact hresult.1

end Vegas.WindowedApplication
