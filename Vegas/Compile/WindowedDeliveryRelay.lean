/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryService
import Vegas.Compile.WindowedBlockIsolation
import Vegas.Compile.WindowedActivationFreshness
import Interaction.MessageApplicationImmediateService

/-! # Resolution in a delivery-service relay slot -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The delivery service's clock coordinate preserves an active refined
checkpoint while setting the exact post-window clock. -/
theorem delivery_clock_step_checkpoint (runtime : WindowedApplication P L)
    (roster recipients : List P) (players : P → runtime.application.PlayerPolicy)
    {G : Graph P L} (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (cfg : Config G)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length %
      (recipients.length + roster.length + 2) = recipients.length + 1)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hrefines : execution.native.application.base.Refines cfg) :
    ∃ next, runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients) [.environment] execution =
          FinDist.pure next ∧
      next.native.application.base.memory.clock =
        max execution.native.application.base.memory.clock
          (activation.since + runtime.windowOf instruction.address + 1) ∧
      next.native.application.base.Refines cfg ∧
      next.native.application.active = execution.native.application.active ∧
      runtime.image.activeAddress? next.native.application.base.memory =
        some instruction.address := by
  have hpolicy := runtime.deliveryBlockEnvironment_advance roster recipients
    execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application execution.native)
    instruction activation hindex hactive hslot hactivation hkey
  simp only [MessageApplication.runPolicies, MessageApplication.invoke]
  rw [hpolicy]
  simp only [FinDist.pure_bind, MessageApplication.environmentPolicyStep,
    EnvironmentPolicyCommand.toAction, MessageApplication.advance,
    MessageApplication.step]
  dsimp only [WindowedApplication.application]
  simp only [WindowedApplication.environmentStep, FinDist.map_pure, FinDist.pure_bind,
    FinDist.bind_pure]
  refine ⟨_, rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · simp [ApplicationImage.State.advance]
  refine ⟨hrefines.advance _, rfl, ?_⟩
  simpa [ApplicationImage.State.advance, ApplicationImage.activeAddress?] using hactive

/-- One aligned unchanged delivery-service relay submits a certified due
payload and includes it through the corresponding environment slot. -/
theorem delivery_relay_accepts (runtime : WindowedApplication P L)
    (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (base : runtime.application.PlayerPolicy)
    (hrelay : players who = runtime.deliveryBlockPlayer who base)
    (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (index : Nat)
    (hplayerIndex :
      runtime.image.instructions[(execution.principalHistory who).length / 4]? = some instruction)
    (hplayerSlot : (execution.principalHistory who).length % 4 = 3)
    (henvironmentIndex : runtime.image.instructions[execution.environmentHistory.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (henvironmentSlot : execution.environmentHistory.length %
      (recipients.length + roster.length + 2) = recipients.length + index + 2)
    (hwho : roster[index]? = some who)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (payload : ApplicationImage.Payload P L) (next : WindowedApplication.State P L)
    (hdue : runtime.dueExpiry?
      (execution.native.application.base.memory, execution.native.application.active) =
        some payload)
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hhandle : runtime.handle execution.native.application
      ⟨(who, execution.native.pool.nextSerial who), payload⟩ = some next) :
    (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients)
      [.player who, .environment] execution).map
        (fun out => (out.native.application, out.native.pool.ledger, out.native.receipts)) =
      FinDist.pure (next,
        execution.native.pool.ledger ++
          [⟨(who, execution.native.pool.nextSerial who), payload⟩],
        execution.native.receipts ++
          [((who, execution.native.pool.nextSerial who), true)]) := by
  have hsubmit : players who (execution.principalHistory who)
      (MessageApplication.State.observe runtime.application execution.native who) =
        FinDist.pure (.submit payload) := by
    rw [hrelay]
    exact runtime.deliveryBlockPlayer_relay who base _ _ instruction payload
      hplayerIndex hactive hplayerSlot hdue
  have hservice := runtime.deliveryBlockEnvironment_relay roster recipients
    execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application
      { execution.native with pool := (execution.native.pool.submit who payload).2 })
    instruction index who henvironmentIndex hactive (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using henvironmentSlot) hwho
  have hlaw : runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients)
      [.player who, .environment] execution =
      runtime.application.runPolicies players (runtime.application.includeLatestFrom who)
        [.player who, .environment] execution := by
    simp only [MessageApplication.runPolicies, MessageApplication.invoke, hsubmit,
      FinDist.pure_bind, MessageApplication.playerStep, MessageApplication.advance,
      PlayerCommand.toAction, MessageApplication.step, MessageApplication.includeLatestFrom]
    rw [hservice, FinDist.pure_bind]
  rw [hlaw]
  exact runtime.application.submit_include_accepts players who payload execution next
    hsubmit hfresh hhandle

/-- The application projection of an accepted delivery relay is the certified
handler result, and that result has resolved the formerly active instruction. -/
theorem delivery_relay_resolves_active (runtime : WindowedApplication P L)
    (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (base : runtime.application.PlayerPolicy)
    (hrelay : players who = runtime.deliveryBlockPlayer who base)
    (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (index : Nat)
    (hplayerIndex :
      runtime.image.instructions[(execution.principalHistory who).length / 4]? = some instruction)
    (hplayerSlot : (execution.principalHistory who).length % 4 = 3)
    (henvironmentIndex : runtime.image.instructions[execution.environmentHistory.length /
      (recipients.length + roster.length + 2)]? = some instruction)
    (henvironmentSlot : execution.environmentHistory.length %
      (recipients.length + roster.length + 2) = recipients.length + index + 2)
    (hwho : roster[index]? = some who)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (payload : ApplicationImage.Payload P L) (next : WindowedApplication.State P L)
    (hdue : runtime.dueExpiry?
      (execution.native.application.base.memory, execution.native.application.active) =
        some payload)
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hhandle : runtime.handle execution.native.application
      ⟨(who, execution.native.pool.nextSerial who), payload⟩ = some next) :
    (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients)
      [.player who, .environment] execution).map
        (fun out => (out.native.application, out.native.pool.ledger, out.native.receipts)) =
      FinDist.pure (next,
        execution.native.pool.ledger ++
          [⟨(who, execution.native.pool.nextSerial who), payload⟩],
        execution.native.receipts ++
          [((who, execution.native.pool.nextSerial who), true)]) ∧
      runtime.image.activeAddress? next.base.memory ≠ some instruction.address ∧
      next.FreshActivation := by
  have hlaw := runtime.delivery_relay_accepts roster recipients players who base hrelay execution
    instruction index hplayerIndex hplayerSlot henvironmentIndex henvironmentSlot hwho hactive
    payload next hdue hfresh hhandle
  refine ⟨hlaw, ?_, runtime.handle_freshActivation execution.native.application next _ hhandle⟩
  obtain ⟨address, hbefore, _, hinactive⟩ := runtime.handle_resolves_active
      execution.native.application next
      ⟨(who, execution.native.pool.nextSerial who), payload⟩ hhandle
  have haddress : address = instruction.address :=
    Option.some.inj (hbefore.symm.trans hactive)
  rwa [haddress] at hinactive

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.delivery_relay_resolves_active' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.delivery_relay_resolves_active
