/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockService
import Interaction.MessageApplicationImmediateService

/-! # Resolution in a reserved block relay slot

The relay is an actual player policy invocation followed by the block
environment's reserved inclusion. The policy uses its public activation and
local history; acceptance is delegated to the existing generated handler.
The statement retains the actual envelope, ledger entry, and receipt.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An aligned unchanged relay resolves an enabled expiry through the block
service. Other player policies and unrelated pending traffic are unrestricted.
The handler premise is local readiness, not completion of an execution. -/
theorem block_relay_accepts (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (base : runtime.application.PlayerPolicy)
    (hrelay : players who = runtime.blockPlayer who base)
    (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (index : Nat)
    (hplayerIndex :
      runtime.image.instructions[(execution.principalHistory who).length / 3]? = some instruction)
    (hplayerSlot : (execution.principalHistory who).length % 3 = 2)
    (henvironmentIndex :
      runtime.image.instructions[execution.environmentHistory.length / (roster.length + 2)]? =
        some instruction)
    (henvironmentSlot : execution.environmentHistory.length % (roster.length + 2) = index + 2)
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
    (runtime.application.runPolicies players (runtime.blockEnvironment roster)
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
    exact runtime.blockPlayer_relay who base _ _ instruction payload
      hplayerIndex hactive hplayerSlot hdue
  have hservice := runtime.blockEnvironment_relay roster execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application
      { execution.native with pool := (execution.native.pool.submit who payload).2 })
    instruction index who henvironmentIndex hactive henvironmentSlot hwho
  have hlaw : runtime.application.runPolicies players (runtime.blockEnvironment roster)
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

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.block_relay_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.block_relay_accepts
