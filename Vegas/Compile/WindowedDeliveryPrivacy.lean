/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryPhase
import Vegas.Compile.WindowedReactionPrivacy

/-! # Information agreement through the concrete delivery phase

This is a local bridge from the actual delivery-service environment policy to
the generic delivery/reaction agreement theorem.  All prefix selection and
visited-policy facts remain explicit; no source-wide correspondence is claimed.
-/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}

/-- Executing the concrete delivery slots for the same selected pending
identifier, followed by the roster reaction round, preserves focal agreement. -/
theorem deliveryPrefix_then_roster_reactions
    {left right leftFinal rightFinal : runtime.application.PolicyExecution}
    (agreement : PolicyAgreement runtime focal left right)
    (players : P → runtime.application.PlayerPolicy)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (hfocal : players focal = fun history view => FinDist.pure (command history view))
    (roster recipients : List P) (blockIndex : Nat)
    (instruction : ApplicationInstruction P L) (id : MessageId P)
    (hleftLength : left.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2))
    (hrightLength : right.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2))
    (hindex : runtime.image.instructions[blockIndex]? = some instruction)
    (hleftActive : runtime.image.activeAddress? left.native.application.base.memory =
      some instruction.address)
    (hrightActive : runtime.image.activeAddress? right.native.application.base.memory =
      some instruction.address)
    (hleftInclude : runtime.liftEnvironmentCommand
      (runtime.image.serviceCommand instruction
        (runtime.eraseEnvironmentView
          (State.environmentView runtime.application left.native))) = .include id)
    (hrightInclude : runtime.liftEnvironmentCommand
      (runtime.image.serviceCommand instruction
        (runtime.eraseEnvironmentView
          (State.environmentView runtime.application right.native))) = .include id)
    (starts limits : P → Nat)
    (hothers : ∀ actor history view, actor ≠ focal →
      starts actor ≤ history.length → history.length < limits actor →
      players actor history view = FinDist.pure .wait)
    (hleftRange : ∀ actor,
      starts actor ≤ (left.principalHistory actor).length ∧
        (left.principalHistory actor).length +
          (roster.map Invocation.player).countP (fun call => match call with
            | .player who => decide (who = actor)
            | .environment => false) = limits actor)
    (hrightRange : ∀ actor,
      starts actor ≤ (right.principalHistory actor).length ∧
        (right.principalHistory actor).length +
          (roster.map Invocation.player).countP (fun call => match call with
            | .player who => decide (who = actor)
            | .environment => false) = limits actor)
    (hleft : leftFinal ∈
      ((runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients)
        (recipients.map fun _ => (Invocation.environment : @Invocation P)) left).bind
          fun delivered => runtime.application.runPolicies players
            (runtime.deliveryBlockEnvironment roster recipients)
            (roster.map Invocation.player) delivered).support)
    (hright : rightFinal ∈
      ((runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients)
        (recipients.map fun _ => (Invocation.environment : @Invocation P)) right).bind
          fun delivered => runtime.application.runPolicies players
            (runtime.deliveryBlockEnvironment roster recipients)
            (roster.map Invocation.player) delivered).support) :
    PolicyAgreement runtime focal leftFinal rightFinal := by
  rw [runtime.runPolicies_deliveryPrefix players roster recipients blockIndex instruction id left
    hleftLength hindex hleftActive hleftInclude] at hleft
  rw [runtime.runPolicies_deliveryPrefix players roster recipients blockIndex instruction id right
    hrightLength hindex hrightActive hrightInclude] at hright
  exact agreement.deliveries_then_reactions id recipients command players
    (runtime.deliveryBlockEnvironment roster recipients) hfocal starts limits hothers
    (roster.map Invocation.player) (by simp) hleftRange hrightRange hleft hright

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.deliveryPrefix_then_roster_reactions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.WindowedApplication.PolicyAgreement.deliveryPrefix_then_roster_reactions
